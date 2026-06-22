#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

# Strict only when the project opts in (new scaffolds set this in project.conf);
# legacy projects default to advisory and never fail this check.
mode="advisory"
if [[ "${SEMANTIC_CLAIMS_REQUIRED}" == "1" ]]; then
  mode="strict"
fi

exec python3 "${SCRIPT_DIR}/project_semantic_claims_check.py" \
  "${ASM_FILE}" "${SEMANTIC_CLAIMS_FILE}" --mode "${mode}"
