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

# If KPI_DETAIL_FILE is set, write the per-label undocumented detail list
# there and leave it for the caller to read. Otherwise use a temp file
# scoped to this invocation.
if [[ -n "${KPI_DETAIL_FILE:-}" ]]; then
  tmp_details="${KPI_DETAIL_FILE}"
  : > "${tmp_details}"
else
  tmp_details="$(mktemp)"
  trap 'rm -f "${tmp_details}"' EXIT
fi

report="$(
  awk -v details_file="${tmp_details}" '
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
    function is_data_directive(s,   t) {
      t=s
      sub(/^[[:space:]]+/, "", t)
      return (toupper(t) ~ /^\.(DB|DW|BYTE|WORD|DS|INCBIN)([[:space:]]|$)/)
    }
    function is_code_label(lbl,   i) {
      if (!(lbl in label_line)) return 0
      i = label_line[lbl] + 1
      while (i <= NR && (is_blank(lines[i]) || is_comment(lines[i]))) i++
      if (i > NR) return 0
      if (is_global_label(lines[i])) return 0
      if (is_data_directive(lines[i])) return 0
      return 1
    }
    function has_doc_header(lbl,   i, saw_comment, nonempty_comment) {
      if (!(lbl in label_line)) return 0
      i = label_line[lbl] - 1
      while (i >= 1 && is_blank(lines[i])) i--

      # Allow one doc header to cover contiguous alias labels at the same code
      # entry point.
      while (i >= 1 && is_global_label(lines[i])) i--
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
        label_order[++label_count]=lbl
      }
    }
    END {
      total=0
      documented=0
      undocumented=0
      for (k=1; k<=label_count; k++) {
        lbl=label_order[k]
        if (!is_code_label(lbl)) continue
        total++
        if (has_doc_header(lbl)) {
          documented++
        } else {
          undocumented++
          print label_line[lbl] ":" lbl >> details_file
        }
      }
      coverage = (total > 0) ? int((documented * 100) / total) : 100
      print "strict_global_code_labels_total=" total
      print "strict_global_code_labels_documented=" documented
      print "strict_global_code_labels_undocumented=" undocumented
      print "strict_global_code_label_doc_coverage_pct=" coverage
    }
  ' "${ASM_FILE}"
)"

echo "${report}"

MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS=0
if [[ -n "${KPI_CONF}" && -f "${KPI_CONF}" ]]; then
  configured_max="$(
    awk -F= '
      /^[[:space:]]*#/ { next }
      /^[[:space:]]*$/ { next }
      $1 ~ /^[[:space:]]*MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS[[:space:]]*$/ {
        gsub(/[[:space:]]/, "", $2)
        print $2
        exit
      }
    ' "${KPI_CONF}"
  )"
  if [[ -n "${configured_max}" ]]; then
    MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS="${configured_max}"
  fi
fi

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

STRICT_ACTIVE_UNDOCUMENTED_GLOBAL_CODE_LABELS="$(
  printf '%s\n' "${report}" | awk -F= '/strict_global_code_labels_undocumented=/{print $2}'
)"

if (( STRICT_ACTIVE_UNDOCUMENTED_GLOBAL_CODE_LABELS > MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS )); then
  echo "FAIL: strict_global_code_labels_undocumented (${STRICT_ACTIVE_UNDOCUMENTED_GLOBAL_CODE_LABELS}) exceeds KPI max (${MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS})" >&2
  if [[ -s "${tmp_details}" ]]; then
    echo "Undocumented global code labels:" >&2
    sed 's/^/  /' "${tmp_details}" >&2
  fi
  exit 68
fi

echo "OK: global code-label documentation KPI gate passed"
