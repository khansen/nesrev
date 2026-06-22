#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

bash "${SCRIPT_DIR}/project_verify.sh" "$1"
bash "${SCRIPT_DIR}/project_process_check.sh" "$1"
bash "${SCRIPT_DIR}/project_maturity_check.sh" "$1"
bash "${SCRIPT_DIR}/project_docs_check.sh" "$1"
