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

bash "${SCRIPT_DIR}/check_docs.sh" \
  "${ASM_FILE}" \
  "${DOC_ROOT}" \
  "${SYSTEMS_DOC}" \
  "${WARN_BASELINE_FILE}" \
  "${NESREV_RECOVERY_STATUS}"
