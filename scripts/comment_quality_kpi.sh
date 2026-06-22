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

# Placeholder/temporary-comment guard.
# Keep this scoped to known filler patterns and AGENTS-banned generic phrases.
PLACEHOLDER_RE='documented in brief|refine details in deeper pass|placeholder|packed byte data block \(structure documented by nearby consumer code\)|routines that reference this label in gameplay/render/audio paths|label-specific structure inferred from active readers'

STRICT_PLACEHOLDER_COMMENTS="$(
  { rg -ni "${PLACEHOLDER_RE}" "${ASM_FILE}" || true; } | wc -l | tr -d ' '
)"

echo "[comment-kpi] strict_placeholder_comments=${STRICT_PLACEHOLDER_COMMENTS}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: comment-quality KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_PLACEHOLDER_COMMENTS="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_PLACEHOLDER_COMMENTS[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

if [[ -z "${MAX_PLACEHOLDER_COMMENTS}" ]]; then
  echo "error: KPI config must define MAX_PLACEHOLDER_COMMENTS: ${KPI_CONF}" >&2
  exit 67
fi

if (( STRICT_PLACEHOLDER_COMMENTS > MAX_PLACEHOLDER_COMMENTS )); then
  echo "FAIL: strict_placeholder_comments (${STRICT_PLACEHOLDER_COMMENTS}) exceeds KPI max (${MAX_PLACEHOLDER_COMMENTS})" >&2
  exit 68
fi

echo "OK: comment-quality KPI gate passed"
