#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <asm_file> <branch_literal_sites_csv>" >&2
  exit 64
fi

ASM_FILE="$1"
SITES_FILE="$2"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi
if [[ ! -f "${SITES_FILE}" ]]; then
  echo "error: branch-literal sites file not found: ${SITES_FILE}" >&2
  exit 66
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp)"
trap 'rm -f "${tmp}"' EXIT

bash "${SCRIPT_DIR}/branch_literal_sites.sh" "${ASM_FILE}" "${tmp}"

if cmp -s "${tmp}" "${SITES_FILE}"; then
  echo "OK: branch-literal site registry synchronized"
else
  echo "FAIL: branch-literal site registry is stale: ${SITES_FILE}" >&2
  echo "hint: run make project-inventory PROJECT=<slug>" >&2
  exit 67
fi
