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

# Count executable operands that still use relative branch literals ($+N / $-N).
# These are often parity-sensitive and should not grow unintentionally.
STRICT_ACTIVE_BRANCH_LITERALS="$(
  awk '
    toupper($1) ~ /^[A-Z]{3}(\.[A-Z])?$/ {
      line=$0
      sub(/^[[:space:]]*[A-Z]{3}(\.[A-Z])?[[:space:]]+/, "", line)
      sub(/[[:space:];].*$/, "", line)
      if (line ~ /^\$[+-][0-9]+$/) c++
    }
    END { print c+0 }
  ' "${ASM_FILE}"
)"

echo "[branch-kpi] strict_active_branch_literals=${STRICT_ACTIVE_BRANCH_LITERALS}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: branch-literal KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_ACTIVE_BRANCH_LITERALS="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_ACTIVE_BRANCH_LITERALS[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

if [[ -z "${MAX_ACTIVE_BRANCH_LITERALS}" ]]; then
  echo "error: KPI config must define MAX_ACTIVE_BRANCH_LITERALS: ${KPI_CONF}" >&2
  exit 67
fi

if (( STRICT_ACTIVE_BRANCH_LITERALS > MAX_ACTIVE_BRANCH_LITERALS )); then
  echo "FAIL: strict_active_branch_literals (${STRICT_ACTIVE_BRANCH_LITERALS}) exceeds KPI max (${MAX_ACTIVE_BRANCH_LITERALS})" >&2
  exit 68
fi

echo "OK: branch-literal KPI gate passed"
