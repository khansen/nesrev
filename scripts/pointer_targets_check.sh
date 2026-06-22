#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <asm_file> <pointer_targets_csv>" >&2
  exit 64
fi

ASM_FILE="$1"
PTR_FILE="$2"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi
if [[ ! -f "${PTR_FILE}" ]]; then
  echo "error: pointer targets file not found: ${PTR_FILE}" >&2
  exit 66
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp)"
trap 'rm -f "${tmp}"' EXIT

bash "${SCRIPT_DIR}/pointer_targets.sh" "${ASM_FILE}" "${tmp}"

if cmp -s "${tmp}" "${PTR_FILE}"; then
  echo "OK: pointer-target registry synchronized"
else
  echo "FAIL: pointer-target registry is stale: ${PTR_FILE}" >&2
  echo "hint: run make project-inventory PROJECT=<slug>" >&2
  exit 67
fi
