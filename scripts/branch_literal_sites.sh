#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <asm_file> [out_csv]" >&2
  exit 64
fi

ASM_FILE="$1"
OUT_CSV="${2:-}"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi

emit_sites() {
  awk '
BEGIN {
  print "line,enclosing_label,mnemonic,operand,source"
  cur="(none)"
}
{
  raw=$0
  if (match(raw, /^[A-Za-z_][A-Za-z0-9_]*:/)) {
    lbl = substr(raw, RSTART, RLENGTH)
    sub(/:.*/, "", lbl)
    cur=lbl
  }

  if (toupper($1) ~ /^[A-Z]{3}(\.[A-Z])?$/) {
    line=raw
    sub(/^[[:space:]]*[A-Z]{3}(\.[A-Z])?[[:space:]]+/, "", line)
    sub(/[[:space:];].*$/, "", line)
    if (line ~ /^\$[+-][0-9]+$/) {
      src=raw
      gsub(/"/, "\"\"", src)
      printf "%d,%s,%s,%s,\"%s\"\n", NR, cur, $1, line, src
    }
  }
}
' "${ASM_FILE}"
}

if [[ -n "${OUT_CSV}" ]]; then
  emit_sites > "${OUT_CSV}"
else
  emit_sites
fi
