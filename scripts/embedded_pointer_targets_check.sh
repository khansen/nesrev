#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <asm_file> <embedded_pointer_targets_csv>" >&2
  exit 64
fi

ASM_FILE="$1"
TARGETS_FILE="$2"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi
if [[ ! -f "${TARGETS_FILE}" ]]; then
  echo "error: embedded pointer targets file not found: ${TARGETS_FILE}" >&2
  exit 66
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp)"
trap 'rm -f "${tmp}"' EXIT

python3 "${SCRIPT_DIR}/embedded_pointer_targets.py" "${ASM_FILE}" "${tmp}"

if cmp -s "${tmp}" "${TARGETS_FILE}"; then
  echo "OK: embedded pointer target registry synchronized"
else
  echo "FAIL: embedded pointer target registry is stale: ${TARGETS_FILE}" >&2
  echo "hint: run make project-inventory PROJECT=<slug>" >&2
  exit 67
fi
