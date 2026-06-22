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

emit_targets() {
  awk '
function flush_pending(kind,    i) {
  for (i=1; i<=pending_n; i++) {
    label_kind[pending[i]] = kind
  }
  pending_n = 0
}
function token_kind(line,    l, tok) {
  l = line
  sub(/^[ \t]+/, "", l)
  if (l == "") return ""
  if (l ~ /^;/) return ""
  if (l ~ /^\./) return "data"
  split(l, f, /[ \t]+/)
  tok = f[1]
  if (toupper(tok) ~ /^[A-Z]{3}(\.[A-Z])?$/) return "code"
  if (tok ~ /^[A-Za-z_][A-Za-z0-9_]*:$/) return ""
  return "unknown"
}
function base_label(expr,    e, p) {
  e = expr
  gsub(/^[ \t]+|[ \t]+$/, "", e)
  gsub(/^\(+/, "", e)
  gsub(/\)+$/, "", e)
  if (e ~ /^[<>]/) e = substr(e, 2)
  p = index(e, "+")
  if (p > 0) e = substr(e, 1, p-1)
  p = index(e, "-")
  if (p > 0) e = substr(e, 1, p-1)
  return e
}
BEGIN {
  print "source,entry,target_label,target_type,confidence,notes"
  cur=""
  cur_entry=0
  pending_n=0
}
FNR==NR {
  line = $0
  if (match(line, /^[A-Za-z_][A-Za-z0-9_]*[ \t]+\.EQU[ \t]/)) {
    lbl = line
    sub(/[ \t]+\.EQU.*/, "", lbl)
    label_kind[lbl] = "data"
    next
  }
  if (match(line, /^[A-Za-z_][A-Za-z0-9_]*:/)) {
    lbl = substr(line, RSTART, RLENGTH)
    sub(/:.*/, "", lbl)
    pending[++pending_n] = lbl
    cur = lbl
    line = substr(line, RLENGTH + 1)
    if (line ~ /^[ \t]*$/) next
  }
  k = token_kind(line)
  if (k != "" && pending_n > 0) {
    flush_pending(k)
  }
  next
}
FNR==1 && NR!=1 {
  if (pending_n > 0) flush_pending("unknown")
}
{
  line = $0
  if (match(line, /^[A-Za-z_][A-Za-z0-9_]*:/)) {
    lbl = substr(line, RSTART, RLENGTH)
    sub(/:.*/, "", lbl)
    cur = lbl
    cur_entry = 0
    line = substr(line, RLENGTH + 1)
  }
  if (line ~ /^[ \t]*\.DW[ \t]+/) {
    dw = line
    sub(/^[ \t]*\.DW[ \t]+/, "", dw)
    sub(/;.*$/, "", dw)
    gsub(/[ \t]/, "", dw)
    n = split(dw, a, ",")
    for (i=1; i<=n; i++) {
      t=a[i]
      if (t ~ /^\$/) continue
      if (t ~ /^[0-9]+$/) continue
      if (t == "") continue
      b = base_label(t)
      kind = label_kind[b]
      type = "unknown_pointer"
      conf = "inferred"
      note = "auto-extracted from .DW entry (target kind unresolved)"
      if (kind == "code") {
        type = "code_pointer"
        conf = "high confidence"
        note = "auto-classified from target label leading instruction"
      } else if (kind == "data") {
        type = "data_pointer"
        conf = "high confidence"
        note = "auto-classified from target label leading data directive"
      }
      printf "%s,%d,%s,%s,%s,%s\n", cur, cur_entry+i-1, t, type, conf, note
    }
    cur_entry += n
  }
}
' "${ASM_FILE}" "${ASM_FILE}"
}

if [[ -n "${OUT_CSV}" ]]; then
  emit_targets > "${OUT_CSV}"
else
  emit_targets
fi
