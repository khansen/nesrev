#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 2 ]]; then
  echo "usage: $0 <asm_file> <branch_literal_sites_csv>" >&2
  exit 64
fi
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
bash "${SCRIPT_DIR}/branch_literal_analysis.sh" check "$@"
