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

args=(--root "${DOC_ROOT}")
if [[ -n "${CROSSWALK_FILE:-}" ]]; then
  args+=(--root "$(dirname "${CROSSWALK_FILE}")")
fi

python3 "${SCRIPT_DIR}/docs_provenance_lint.py" "${args[@]}"
