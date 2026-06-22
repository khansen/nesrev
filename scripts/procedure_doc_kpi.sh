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

report="$(
  awk '
    function is_blank(s) { return s ~ /^[[:space:]]*$/ }
    function is_comment(s) { return s ~ /^[[:space:]]*;/ }
    function is_global_label(s,   t) {
      t=s
      sub(/^[[:space:]]+/, "", t)
      return (t ~ /^[A-Za-z_][A-Za-z0-9_]*:/)
    }
    function extract_label(s,   t) {
      t=s
      sub(/^[[:space:]]+/, "", t)
      sub(/:.*/, "", t)
      return t
    }
    function extract_operand(s,   t) {
      t=s
      sub(/^[[:space:]]*[A-Za-z]{3}(\.[A-Za-z])?[[:space:]]+/, "", t)
      sub(/[[:space:];].*$/, "", t)
      return t
    }
    function normalize_target(op,   t) {
      t=op
      if (t ~ /^[\(\[]/) return ""
      if (t ~ /^#/) return ""
      if (t ~ /^\$/) return ""
      if (t ~ /^[0-9]/) return ""
      sub(/[,+].*$/, "", t)
      if (t ~ /^[A-Za-z_][A-Za-z0-9_]*$/) return t
      return ""
    }
    function has_doc_header(lbl,   i, saw_comment, nonempty_comment) {
      if (!(lbl in label_line)) return 0
      i = label_line[lbl] - 1
      while (i >= 1 && is_blank(lines[i])) i--
      if (i < 1 || !is_comment(lines[i])) return 0
      saw_comment = 0
      nonempty_comment = 0
      while (i >= 1 && is_comment(lines[i])) {
        saw_comment = 1
        if (lines[i] !~ /^[[:space:]]*;[[:space:]]*$/) nonempty_comment = 1
        i--
      }
      return (saw_comment && nonempty_comment) ? 1 : 0
    }
    {
      lines[NR]=$0
      if (is_global_label($0)) {
        lbl=extract_label($0)
        label_line[lbl]=NR
      }

      op=toupper($1)
      if (op ~ /^(JSR|JMP)(\.[A-Z])?$/) {
        tgt=normalize_target(extract_operand($0))
        if (tgt != "") called[tgt]=1
      }
    }
    END {
      total=0
      documented=0
      undocumented=0
      for (lbl in called) {
        if (!(lbl in label_line)) continue
        total++
        if (has_doc_header(lbl)) documented++
        else undocumented++
      }
      coverage = (total > 0) ? int((documented * 100) / total) : 100
      print "strict_callable_procedures_total=" total
      print "strict_callable_procedures_documented=" documented
      print "strict_callable_procedures_undocumented=" undocumented
      print "strict_callable_procedure_doc_coverage_pct=" coverage
    }
  ' "${ASM_FILE}"
)"

echo "${report}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: procedure-doc KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_UNDOCUMENTED_PROCEDURES="$(
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_UNDOCUMENTED_PROCEDURES[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
)"

if [[ -z "${MAX_UNDOCUMENTED_PROCEDURES}" ]]; then
  echo "error: KPI config must define MAX_UNDOCUMENTED_PROCEDURES: ${KPI_CONF}" >&2
  exit 67
fi

STRICT_ACTIVE_UNDOCUMENTED_PROCEDURES="$(
  printf '%s\n' "${report}" | awk -F= '/strict_callable_procedures_undocumented=/{print $2}'
)"

if (( STRICT_ACTIVE_UNDOCUMENTED_PROCEDURES > MAX_UNDOCUMENTED_PROCEDURES )); then
  echo "FAIL: strict_callable_procedures_undocumented (${STRICT_ACTIVE_UNDOCUMENTED_PROCEDURES}) exceeds KPI max (${MAX_UNDOCUMENTED_PROCEDURES})" >&2
  exit 68
fi

echo "OK: procedure documentation KPI gate passed"
