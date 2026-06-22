#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <asm_file> [kpi_conf]" >&2
  exit 64
fi

ASM_FILE="$1"
KPI_CONF="${2:-}"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi

STRICT_INFERRED_ANNOTATIONS="$(
  { rg -n ";\s*inferred\b" "${ASM_FILE}" || true; } | wc -l | tr -d ' '
)"

echo "[inferred-kpi] strict_inferred_annotations=${STRICT_INFERRED_ANNOTATIONS}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: inferred KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_INFERRED_ANNOTATIONS="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_INFERRED_ANNOTATIONS[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

if [[ -z "${MAX_INFERRED_ANNOTATIONS}" ]]; then
  echo "error: KPI config must define MAX_INFERRED_ANNOTATIONS: ${KPI_CONF}" >&2
  exit 67
fi

if (( STRICT_INFERRED_ANNOTATIONS > MAX_INFERRED_ANNOTATIONS )); then
  echo "FAIL: strict_inferred_annotations (${STRICT_INFERRED_ANNOTATIONS}) exceeds KPI max (${MAX_INFERRED_ANNOTATIONS})" >&2
  exit 68
fi

echo "OK: inferred-annotation KPI gate passed"
