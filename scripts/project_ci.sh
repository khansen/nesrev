#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

if [[ -n "${NESREV_ANALYSIS_BUNDLE+x}" || -n "${NESREV_ANALYSIS_BUILD_DIR+x}" || -n "${NESREV_XREF_FILE+x}" ]]; then
  echo "error: project-ci requires fresh analysis; do not supply an analysis bundle" >&2
  exit 65
fi

TMPDIR_PROJECT_CI="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PROJECT_CI}"' EXIT
export NESREV_XREF_FILE="${TMPDIR_PROJECT_CI}/xref_with_data.json"

source "${SCRIPT_DIR}/project_common.sh"
load_project_analysis_conf "$1"
prepare_project_analysis_bundle "$1" "${TMPDIR_PROJECT_CI}" ci-instructions-v1

NESREV_ANALYSIS_BUILD_DIR="${TMPDIR_PROJECT_CI}" bash "${SCRIPT_DIR}/project_verify.sh" "$1"
export NESREV_ANALYSIS_BUNDLE="${TMPDIR_PROJECT_CI}/bundle.json"
bash "${SCRIPT_DIR}/project_process_check.sh" "$1"
bash "${SCRIPT_DIR}/project_maturity_check.sh" "$1"
bash "${SCRIPT_DIR}/project_docs_check.sh" "$1"
python3 "${SCRIPT_DIR}/analysis_bundle.py" validate "${NESREV_ANALYSIS_BUNDLE}"
