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

# If KPI_DETAIL_FILE is set, write one line per noncompliant data label there:
# <line>:<label>:<problem> (<header source>). Otherwise use a temp file scoped
# to this invocation so a gate failure can still name offenders.
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
    function is_data_directive(s,   t) {
      t=s
      sub(/^[[:space:]]+/, "", t)
      return (toupper(t) ~ /^\.(DB|DW|BYTE|WORD|DS|INCBIN)([[:space:]]|$)/)
    }
    function parse_direct_header(lbl,   i, saw_comment, nonempty_comment, line_text, low) {
      header_has_comment[lbl]=0
      header_has_format[lbl]=0
      header_has_usage[lbl]=0
      header_line[lbl]=0

      if (!(lbl in label_line)) return

      i = label_line[lbl] - 1
      while (i >= 1 && is_blank(lines[i])) i--
      # Allow one doc header to cover contiguous alias labels:
      # walk upward across adjacent global labels before checking comments.
      while (i >= 1 && is_global_label(lines[i])) i--
      while (i >= 1 && is_blank(lines[i])) i--
      if (i < 1 || !is_comment(lines[i])) return
      header_line[lbl] = i

      saw_comment = 0
      nonempty_comment = 0
      while (i >= 1 && is_comment(lines[i])) {
        saw_comment = 1
        line_text = lines[i]
        if (line_text !~ /^[[:space:]]*;[[:space:]]*$/) nonempty_comment = 1
        low = tolower(line_text)
        if (low ~ /;[[:space:]]*format:/) header_has_format[lbl]=1
        if (low ~ /;[[:space:]]*(consumer|used by):/) header_has_usage[lbl]=1
        i--
      }

      if (saw_comment && nonempty_comment) header_has_comment[lbl]=1
    }

    # A comment with Format: or Used by: is a header and must be complete on its
    # own. A comment with neither is a note: the label, and later labels in the
    # same contiguous family, keep inheriting the family header above it.
    function is_tagged_header(lbl) {
      return header_has_comment[lbl] && (header_has_format[lbl] || header_has_usage[lbl])
    }

    function inherit_family_header(lbl,   i, cand) {
      if (!(lbl in label_line)) return 0

      i = label_line[lbl] - 1
      while (i >= 1 && is_comment(lines[i])) i--
      if (i < 1) return 0
      if (!is_global_label(lines[i]) && !is_data_directive(lines[i])) return 0

      while (i >= 1) {
        if (is_comment(lines[i])) {
          i--
          continue
        }
        if (is_blank(lines[i])) return 0
        if (is_data_directive(lines[i])) {
          i--
          continue
        }
        if (is_global_label(lines[i])) {
          cand = lines[i]
          sub(/:.*/, "", cand)
          if (cand != lbl) {
            parse_direct_header(cand)
            if (is_tagged_header(cand)) {
              header_has_comment[lbl] = 1
              header_has_format[lbl] = header_has_format[cand]
              header_has_usage[lbl] = header_has_usage[cand]
              header_source[lbl] = "family header of " cand " at line " header_line[cand]
              return 1
            }
          }
          i--
          continue
        }
        return 0
      }
      return 0
    }

    function parse_header(lbl,   note_line) {
      parse_direct_header(lbl)
      if (is_tagged_header(lbl)) {
        header_source[lbl] = "own header at line " header_line[lbl]
        return
      }
      note_line = header_has_comment[lbl] ? header_line[lbl] : 0
      header_source[lbl] = note_line ? "note comment at line " note_line ", no family header" : "no header"
      if (inherit_family_header(lbl)) return
      if (note_line) {
        header_has_comment[lbl] = 1
        header_has_format[lbl] = 0
        header_has_usage[lbl] = 0
      }
    }

    function record_detail(lbl, problem) {
      print label_line[lbl] ":" lbl ":" problem " (" header_source[lbl] ")" > details_file
    }

    {
      lines[NR] = $0
      if (is_global_label($0)) {
        lbl=$0
        sub(/:.*/, "", lbl)
        label_line[lbl]=NR
        label_order[++label_count]=lbl
      }
    }

    END {
      total=0
      documented=0
      undocumented=0
      missing_format=0
      missing_usage=0
      noncompliant=0

      for (k=1; k<=label_count; k++) {
        lbl = label_order[k]
        # Structural end markers (e.g., TableEnd/PacketEnd) do not require
        # standalone data-label documentation headers.
        if (lbl ~ /End$/) continue
        i = label_line[lbl] + 1
        while (i <= NR && (is_blank(lines[i]) || is_comment(lines[i]))) i++

        if (i > NR) continue
        if (is_global_label(lines[i])) continue
        if (!is_data_directive(lines[i])) continue

        total++
        parse_header(lbl)

        if (!header_has_comment[lbl]) {
          undocumented++
          noncompliant++
          record_detail(lbl, "undocumented")
          continue
        }

        bad=0
        problem=""
        if (!header_has_format[lbl]) {
          missing_format++
          bad=1
          problem="missing Format:"
        }
        if (!header_has_usage[lbl]) {
          missing_usage++
          bad=1
          problem=(problem == "" ? "missing Used by:" : problem " and Used by:")
        }

        if (bad) {
          noncompliant++
          record_detail(lbl, problem)
        }
        else documented++
      }

      coverage = (total > 0) ? int((documented * 100) / total) : 100
      print "strict_data_labels_total=" total
      print "strict_data_labels_documented=" documented
      print "strict_data_labels_undocumented=" undocumented
      print "strict_data_labels_missing_format=" missing_format
      print "strict_data_labels_missing_usage=" missing_usage
      print "strict_data_labels_noncompliant=" noncompliant
      print "strict_data_label_doc_coverage_pct=" coverage
      close(details_file)
    }
  ' "${ASM_FILE}"
)"

echo "${report}"

if [[ -z "${KPI_CONF}" ]]; then
  exit 0
fi

if [[ ! -f "${KPI_CONF}" ]]; then
  echo "error: data-label-doc KPI config not found: ${KPI_CONF}" >&2
  exit 66
fi

MAX_UNDOCUMENTED_DATA_LABELS="$({
  awk -F'=' '
    /^[[:space:]]*#/ { next }
    /^[[:space:]]*$/ { next }
    $1 ~ /^[[:space:]]*MAX_UNDOCUMENTED_DATA_LABELS[[:space:]]*$/ {
      gsub(/[[:space:]]/, "", $2)
      print $2
      exit
    }
  ' "${KPI_CONF}"
})"

if [[ -z "${MAX_UNDOCUMENTED_DATA_LABELS}" ]]; then
  echo "error: KPI config must define MAX_UNDOCUMENTED_DATA_LABELS: ${KPI_CONF}" >&2
  exit 67
fi

STRICT_ACTIVE_NONCOMPLIANT_DATA_LABELS="$({
  printf '%s\n' "${report}" | awk -F= '/strict_data_labels_noncompliant=/{print $2}'
})"

if (( STRICT_ACTIVE_NONCOMPLIANT_DATA_LABELS > MAX_UNDOCUMENTED_DATA_LABELS )); then
  echo "FAIL: strict_data_labels_noncompliant (${STRICT_ACTIVE_NONCOMPLIANT_DATA_LABELS}) exceeds KPI max (${MAX_UNDOCUMENTED_DATA_LABELS})" >&2
  if [[ -s "${tmp_details}" ]]; then
    echo "Noncompliant data labels (line:label:problem (header source)):" >&2
    sed 's/^/  /' "${tmp_details}" >&2
  fi
  exit 68
fi

echo "OK: data-label documentation KPI gate passed"
