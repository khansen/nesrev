#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <xref_v2_json> <pointer_targets_csv>" >&2
  exit 64
fi

XREF_FILE="$1"
PTR_FILE="$2"

if [[ ! -f "${XREF_FILE}" ]]; then
  echo "error: xref file not found: ${XREF_FILE}" >&2
  exit 65
fi
if [[ ! -f "${PTR_FILE}" ]]; then
  echo "error: pointer targets file not found: ${PTR_FILE}" >&2
  exit 66
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp)"
trap 'rm -f "${tmp}"' EXIT

bash "${SCRIPT_DIR}/pointer_targets.sh" "${XREF_FILE}" "${tmp}"

if cmp -s "${tmp}" "${PTR_FILE}"; then
  echo "OK: pointer-target registry synchronized"
else
  echo "FAIL: pointer-target registry is stale: ${PTR_FILE}" >&2
  echo "hint: run make project-inventory PROJECT=<slug>" >&2
  exit 67
fi
