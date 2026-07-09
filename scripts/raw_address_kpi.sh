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

# Count executable operands (exclude .DB payloads and immediates)
# that still reference raw low addresses in operand position.
STRICT_ACTIVE_RAW_LOWADDR="$(
  awk '
    BEGIN {
      raw_lowaddr = "\\$([0-9A-F][0-9A-F]?|0[0-9A-F][0-9A-F][0-9A-F]?)"
      bare_lowaddr = raw_lowaddr "(,[XY])?"
      paren_lowaddr = "\\(" raw_lowaddr "(,[XY])?\\)(,Y)?"
      bracket_lowaddr = "\\[" raw_lowaddr "(,[XY])?\\](,[XY])?"
      raw_lowaddr_operand = "^(" bare_lowaddr "|" paren_lowaddr "|" bracket_lowaddr ")$"
    }
    toupper($1) ~ /^[A-Z]{3}(\.[A-Z])?$/ {
      line=$0
      sub(/^[[:space:]]*[A-Z]{3}(\.[A-Z])?[[:space:]]+/, "", line)
      sub(/[[:space:];].*$/, "", line)
      if (line ~ /^#/) next
      if (line ~ raw_lowaddr_operand) c++
    }
    END { print c+0 }
  ' "${ASM_FILE}"
)"

# Count executable operands with raw absolute ROM addresses in operand position
# (hardcoded absolute operands), excluding immediates.
STRICT_ACTIVE_RAW_ABSROM="$(
  awk '
    BEGIN {
      raw_absrom = "\\$[C-F][0-9A-F][0-9A-F][0-9A-F]"
      bare_absrom = raw_absrom "(,[XY])?"
      paren_absrom = "\\(" raw_absrom "(,[XY])?\\)(,Y)?"
      bracket_absrom = "\\[" raw_absrom "(,[XY])?\\](,[XY])?"
      raw_absrom_operand = "^(" bare_absrom "|" paren_absrom "|" bracket_absrom ")$"
    }
    toupper($1) ~ /^[A-Z]{3}(\.[A-Z])?$/ {
      mnemonic=toupper($1)
      line=$0
      sub(/^[[:space:]]*[A-Z]{3}(\.[A-Z])?[[:space:]]+/, "", line)
      sub(/[[:space:];].*$/, "", line)
      if (line ~ /^#/) next
      if (mnemonic ~ /^(STA|STX|STY)$/ && line ~ raw_absrom_operand) next
      if (line ~ raw_absrom_operand) c++
    }
    END { print c+0 }
  ' "${ASM_FILE}"
)"

echo "[raw-kpi] strict_active_raw_lowaddr=${STRICT_ACTIVE_RAW_LOWADDR}"
echo "[raw-kpi] strict_active_raw_absrom=${STRICT_ACTIVE_RAW_ABSROM}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: raw KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_ACTIVE_RAW_LOWADDR="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_ACTIVE_RAW_LOWADDR[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

MAX_ACTIVE_RAW_ABSROM="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_ACTIVE_RAW_ABSROM[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

if [[ -z "${MAX_ACTIVE_RAW_LOWADDR}" || -z "${MAX_ACTIVE_RAW_ABSROM}" ]]; then
  echo "error: KPI config must define MAX_ACTIVE_RAW_LOWADDR and MAX_ACTIVE_RAW_ABSROM: ${KPI_CONF}" >&2
  exit 67
fi

if (( STRICT_ACTIVE_RAW_LOWADDR > MAX_ACTIVE_RAW_LOWADDR )); then
  echo "FAIL: strict_active_raw_lowaddr (${STRICT_ACTIVE_RAW_LOWADDR}) exceeds KPI max (${MAX_ACTIVE_RAW_LOWADDR})" >&2
  exit 68
fi

if (( STRICT_ACTIVE_RAW_ABSROM > MAX_ACTIVE_RAW_ABSROM )); then
  echo "FAIL: strict_active_raw_absrom (${STRICT_ACTIVE_RAW_ABSROM}) exceeds KPI max (${MAX_ACTIVE_RAW_ABSROM})" >&2
  exit 69
fi

echo "OK: raw-address KPI gate passed"
