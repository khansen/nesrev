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
function trim(s) {
  gsub(/^[ \t]+|[ \t]+$/, "", s)
  return s
}
function line_label(line,    l) {
  l = line
  sub(/^[ \t]+/, "", l)
  if (match(l, /^(@@)?[A-Za-z_][A-Za-z0-9_]*:/)) {
    return substr(l, RSTART, RLENGTH - 1)
  }
  return ""
}
function strip_label(line,    l) {
  l = line
  sub(/^[ \t]+/, "", l)
  if (match(l, /^(@@)?[A-Za-z_][A-Za-z0-9_]*:[ \t]*/)) {
    l = substr(l, RLENGTH + 1)
  }
  return l
}
function dw_payload(line,    l, head) {
  l = strip_label(line)
  sub(/;.*$/, "", l)
  head = l
  sub(/^[ \t]+/, "", head)
  if (toupper(head) !~ /^\.DW[ \t]+/) return ""
  sub(/^[ \t]*\.[Dd][Ww][ \t]+/, "", l)
  return trim(l)
}
function dw_entry_count(line,    payload, a) {
  payload = dw_payload(line)
  if (payload == "") return 0
  gsub(/[ \t]/, "", payload)
  if (payload == "") return 0
  return split(payload, a, ",")
}
function mark_terminal_vector_dw(    end, i, j, n, remaining, total) {
  end = max_fnr
  while (end > 0 && trim(lines[end]) ~ /^($|;)/) end--
  if (trim(lines[end]) ~ /^\.END([ \t]|$)/) {
    end--
    while (end > 0 && trim(lines[end]) ~ /^($|;)/) end--
  }
  i = end
  total = 0
  while (i > 0 && dw_entry_count(lines[i]) > 0) {
    total += dw_entry_count(lines[i])
    i--
  }
  if (total < 3) return
  remaining = 3
  for (i=end; i > 0 && remaining > 0 && dw_entry_count(lines[i]) > 0; i--) {
    n = dw_entry_count(lines[i])
    if (n <= remaining) {
      for (j=1; j<=n; j++) {
        skip_dw_entry[i, j] = 1
      }
      remaining -= n
    } else {
      for (j=n-remaining+1; j<=n; j++) {
        skip_dw_entry[i, j] = 1
      }
      remaining = 0
    }
  }
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
  if (tok ~ /^(@@)?[A-Za-z_][A-Za-z0-9_]*:$/) return ""
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
  max_fnr=0
}
FNR==NR {
  lines[FNR] = $0
  max_fnr = FNR
  line = $0
  if (match(line, /^[ \t]*[A-Za-z_][A-Za-z0-9_]*[ \t]+\.[Ee][Qq][Uu][ \t]/)) {
    lbl = line
    sub(/^[ \t]+/, "", lbl)
    sub(/[ \t]+\.[Ee][Qq][Uu].*/, "", lbl)
    label_kind[lbl] = "data"
    next
  }
  lbl = line_label(line)
  if (lbl != "") {
    if (lbl !~ /^@@/) {
      pending[++pending_n] = lbl
      cur = lbl
    }
    line = strip_label(line)
    if (line ~ /^[ \t]*$/) next
  }
  k = token_kind(line)
  if (k != "" && pending_n > 0) {
    flush_pending(k)
  }
  next
}
FNR==1 && NR!=1 {
  mark_terminal_vector_dw()
  if (pending_n > 0) flush_pending("unknown")
}
{
  line = $0
  lbl = line_label(line)
  if (lbl != "") {
    if (lbl !~ /^@@/) {
      cur = lbl
      cur_entry = 0
    }
    line = strip_label(line)
  }
  payload = dw_payload(line)
  if (payload != "") {
    dw = payload
    gsub(/[ \t]/, "", dw)
    n = split(dw, a, ",")
    for (i=1; i<=n; i++) {
      if (skip_dw_entry[FNR, i]) continue
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
