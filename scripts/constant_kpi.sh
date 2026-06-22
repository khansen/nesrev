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

# Count executable immediate numeric literals in active code.
# Excludes:
# - #0/#$00 (explicitly allowed default-clear literals)
# - symbolic immediates (#NAME, #<Label, #>Label, #(expr), etc.)
# - allowlisted `(label, mnemonic, immediate)` entries from
#   `inventory/constant_magic_allowlist.csv` next to the KPI config
ALLOWLIST_FILE="/dev/null"
if [[ -n "${KPI_CONF}" ]]; then
  CANDIDATE_ALLOWLIST_FILE="$(dirname "${KPI_CONF}")/constant_magic_allowlist.csv"
  if [[ -f "${CANDIDATE_ALLOWLIST_FILE}" ]]; then
    ALLOWLIST_FILE="${CANDIDATE_ALLOWLIST_FILE}"
  fi
fi

# When KPI_DETAIL_FILE is set, write one unresolved (line,label,mnemonic,
# immediate) tuple per row to that file instead of (or in addition to)
# counting. The aggregate count is still printed to stdout below.
if [[ -n "${KPI_DETAIL_FILE:-}" ]]; then
  : > "${KPI_DETAIL_FILE}"
fi

STRICT_ACTIVE_MAGIC_IMMEDIATES="$(
  awk -F',' -v details_file="${KPI_DETAIL_FILE:-}" -v asm_path="${ASM_FILE}" '
    function trim(s) {
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", s)
      return s
    }

    # Discriminate by FILENAME rather than FNR==NR, which mis-fires when the
    # allowlist input is empty (/dev/null) — the asm first record then has
    # FNR==NR==1 too and would be parsed as allowlist data.
    FILENAME != asm_path {
      if ($0 ~ /^[[:space:]]*#/ || $0 ~ /^[[:space:]]*$/) next
      if (tolower(trim($1)) == "label" && tolower(trim($2)) == "mnemonic" && tolower(trim($3)) == "immediate") next
      label = trim($1)
      mnemonic = toupper(trim($2))
      immediate = toupper(trim($3))
      if (label != "" && mnemonic != "" && immediate != "") {
        allow[label SUBSEP mnemonic SUBSEP immediate] = 1
      }
      next
    }

    {
      if ($0 ~ /^[[:space:]]*([A-Za-z_][A-Za-z0-9_]*|@@[A-Za-z0-9_]+):/) {
        label_line = $0
        sub(/^[[:space:]]*/, "", label_line)
        sub(/:.*/, "", label_line)
        current_label = label_line
        if (current_label !~ /^@@/) {
          current_global_label = current_label
        }
      }
    }

    {
      # The comma field separator leaves leading whitespace in $1 for
      # non-CSV asm lines, so split the mnemonic off the trimmed line
      # ourselves instead of relying on $1.
      first_token = $0
      sub(/^[[:space:]]+/, "", first_token)
      sub(/[[:space:]].*$/, "", first_token)
      if (toupper(first_token) !~ /^[A-Z]{3}(\.[A-Z])?$/) next
      line=$0
      sub(/^[[:space:]]*[A-Z]{3}(\.[A-Z])?[[:space:]]+/, "", line)
      sub(/[[:space:];].*$/, "", line)
      if (line !~ /^#/) next

      # Numeric immediate literals only (hex, decimal, binary).
      if (line ~ /^#[0-9]+$/ || line ~ /^#\$[0-9A-Fa-f]+$/ || line ~ /^#%[01]+$/) {
        # Allow literal zero clears.
        if (line ~ /^#0+$/) next
        if (line ~ /^#\$0+$/) next
        if (line ~ /^#%0+$/) next
        immediate = toupper(line)
        mnemonic = toupper(first_token)
        if (allow[current_label SUBSEP mnemonic SUBSEP immediate]) next
        if (allow[current_global_label SUBSEP mnemonic SUBSEP immediate]) next
        if (details_file != "") {
          label_for_detail = (current_label != "" ? current_label : current_global_label)
          print FNR ":" label_for_detail ":" mnemonic ":" immediate >> details_file
        }
        c++
      }
    }
    END { print c+0 }
  ' "${ALLOWLIST_FILE}" "${ASM_FILE}"
)"

echo "[const-kpi] strict_active_magic_immediates=${STRICT_ACTIVE_MAGIC_IMMEDIATES}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: constant KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_ACTIVE_MAGIC_IMMEDIATES="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_ACTIVE_MAGIC_IMMEDIATES[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

if [[ -z "${MAX_ACTIVE_MAGIC_IMMEDIATES}" ]]; then
  echo "error: KPI config must define MAX_ACTIVE_MAGIC_IMMEDIATES: ${KPI_CONF}" >&2
  exit 67
fi

if (( STRICT_ACTIVE_MAGIC_IMMEDIATES > MAX_ACTIVE_MAGIC_IMMEDIATES )); then
  echo "FAIL: strict_active_magic_immediates (${STRICT_ACTIVE_MAGIC_IMMEDIATES}) exceeds KPI max (${MAX_ACTIVE_MAGIC_IMMEDIATES})" >&2
  exit 68
fi

echo "OK: constantization KPI gate passed"
