#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <project_slug> [--strict]" >&2
  exit 64
fi
if [[ $# -eq 2 && "$2" != "--strict" ]]; then
  echo "usage: $0 <project_slug> [--strict]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

project_slug="$1"
strict_arg="${2:-}"
load_project_conf "${project_slug}"
project_asm="${ASM_FILE}"
project_scorecard="${PROGRESS_SCORECARD_FILE}"
analogue_slug="$(
  python3 "${SCRIPT_DIR}/scorecard_analogue.py" "${project_scorecard}"
)"
if [[ -z "${analogue_slug}" ]]; then
  echo "prior-project-reuse: skipped (pass 1 has not recorded an analogue yet)"
  exit 0
fi
if [[ "${analogue_slug}" == "none" ]]; then
  echo "prior-project-reuse: skipped (scorecard records Analogue: none)"
  exit 0
fi
if [[ "${analogue_slug}" == "${project_slug}" ]]; then
  echo "prior-project-reuse: error: project cannot name itself as its analogue" >&2
  exit 66
fi

# Resolve the analogue through its project.conf instead of assuming the
# standard asm filename. This wrapper ends immediately afterward, so replacing
# the current project variables in this shell cannot leak into another gate.
load_project_conf "${analogue_slug}"
analogue_asm="${ASM_FILE}"

args=(
  "${project_asm}"
  "${analogue_asm}"
  --analogue-slug "${analogue_slug}"
)
if [[ "${strict_arg}" == "--strict" ]]; then
  args+=(--strict)
fi

python3 "${SCRIPT_DIR}/prior_project_reuse_check.py" "${args[@]}"
