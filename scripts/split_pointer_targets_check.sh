#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <xref_v2_json> <split_pointer_targets_csv>" >&2
  exit 64
fi

XREF_FILE="$1"
TARGETS_FILE="$2"

if [[ ! -f "${XREF_FILE}" ]]; then
  echo "error: xref file not found: ${XREF_FILE}" >&2
  exit 65
fi
if [[ ! -f "${TARGETS_FILE}" ]]; then
  echo "error: split pointer targets file not found: ${TARGETS_FILE}" >&2
  exit 66
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp)"
trap 'rm -f "${tmp}"' EXIT

python3 "${SCRIPT_DIR}/split_pointer_targets.py" "${XREF_FILE}" "${tmp}"

if cmp -s "${tmp}" "${TARGETS_FILE}"; then
  echo "OK: split pointer target registry synchronized"
else
  echo "FAIL: split pointer target registry is stale: ${TARGETS_FILE}" >&2
  echo "hint: run make project-inventory PROJECT=<slug>" >&2
  exit 67
fi
