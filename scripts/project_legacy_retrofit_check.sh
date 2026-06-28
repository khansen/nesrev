#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <project_slug> [--require]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

PROJECT="$1"
MODE_ARG="${2:-}"
if [[ -n "${MODE_ARG}" && "${MODE_ARG}" != "--require" ]]; then
  echo "usage: $0 <project_slug> [--require]" >&2
  exit 64
fi

load_project_conf "${PROJECT}"

args=(
  --asm "${ASM_FILE}"
  --scorecard "${PROGRESS_SCORECARD_FILE}"
  --semantic-claims "${SEMANTIC_CLAIMS_FILE}"
  --scripts-dir "${SCRIPT_DIR}"
)
if [[ "${MODE_ARG}" == "--require" ]]; then
  args+=(--require)
fi

python3 "${SCRIPT_DIR}/legacy_retrofit_audit_check.py" "${args[@]}"
