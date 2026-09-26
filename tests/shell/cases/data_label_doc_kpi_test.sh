#!/usr/bin/env bash
# Tests data-label documentation KPI family inheritance, note comments and
# failure detail.

DATA_LABEL_DOC_KPI="${REPO_ROOT}/scripts/data_label_doc_kpi.sh"

_write_family_fixture() {
  local asm="$1" middle_comment="$2"
  {
    cat <<'ASM'
.ORG $C000
Reset:
  LDA FirstStream
  RTS

; Format: zero-terminated byte streams.
; Used by: Reset.
FirstStream:
.DB $01,$02,$00
SecondStream:
.DB $03,$00
ASM
    if [[ -n "${middle_comment}" ]]; then
      printf '%s\n' "${middle_comment}"
    fi
    cat <<'ASM'
ThirdStream:
.DB $04,$00
FourthStream:
.DB $05,$00

LoneTable:
.DB $06,$07
ASM
  } > "${asm}"
}

test_data_label_doc_kpi_family_header_covers_contiguous_labels() {
  local asm="${NESREV_TEST_TMPDIR}/family.asm"
  _write_family_fixture "${asm}" ""

  local output
  output="$(bash "${DATA_LABEL_DOC_KPI}" "${asm}")"

  assert_match "strict_data_labels_total=5" "${output}"
  assert_match "strict_data_labels_documented=4" "${output}"
  assert_match "strict_data_labels_undocumented=1" "${output}"
  assert_match "strict_data_labels_noncompliant=1" "${output}"
}

test_data_label_doc_kpi_note_comment_keeps_family_header() {
  local asm="${NESREV_TEST_TMPDIR}/note.asm"
  _write_family_fixture "${asm}" "; The third stream is shorter than the others."

  local output
  output="$(bash "${DATA_LABEL_DOC_KPI}" "${asm}")"

  assert_match "strict_data_labels_documented=4" "${output}" \
    "a note without Format/Used by must not cut family inheritance"
  assert_match "strict_data_labels_noncompliant=1" "${output}"
}

test_data_label_doc_kpi_partial_header_must_be_complete() {
  local asm="${NESREV_TEST_TMPDIR}/partial.asm"
  local detail="${NESREV_TEST_TMPDIR}/partial_detail.txt"
  _write_family_fixture "${asm}" "; Format: one byte and a terminator."
  printf 'stale detail\n' > "${detail}"

  local output
  output="$(KPI_DETAIL_FILE="${detail}" bash "${DATA_LABEL_DOC_KPI}" "${asm}")"

  assert_match "strict_data_labels_missing_usage=2" "${output}" \
    "a tagged header is complete on its own and later labels inherit it"
  assert_match "strict_data_labels_noncompliant=3" "${output}"
  local details
  details="$(cat "${detail}")"
  assert_match "[0-9]+:ThirdStream:missing Used by: \\(own header at line [0-9]+\\)" "${details}"
  assert_match "[0-9]+:FourthStream:missing Used by: \\(family header of ThirdStream at line [0-9]+\\)" "${details}"
  assert_match "[0-9]+:LoneTable:undocumented \\(no header\\)" "${details}"
  assert_not_match "stale detail|FirstStream|SecondStream" "${details}"
}

test_data_label_doc_kpi_detail_file_empty_when_compliant() {
  local asm="${NESREV_TEST_TMPDIR}/compliant.asm"
  local detail="${NESREV_TEST_TMPDIR}/compliant_detail.txt"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reset:
  LDA OnlyTable
  RTS

; Format: two bytes.
; Used by: Reset.
OnlyTable:
.DB $01,$02
ASM
  printf 'stale detail\n' > "${detail}"

  KPI_DETAIL_FILE="${detail}" bash "${DATA_LABEL_DOC_KPI}" "${asm}" >/dev/null

  assert_eq "$(cat "${detail}")" "" "compliant labels must leave the detail file empty"
}

test_data_label_doc_kpi_failure_prints_header_sources() {
  local asm="${NESREV_TEST_TMPDIR}/fail.asm"
  local kpi_conf="${NESREV_TEST_TMPDIR}/kpis.conf"
  _write_family_fixture "${asm}" "; Format: one byte and a terminator."
  printf 'MAX_UNDOCUMENTED_DATA_LABELS=0\n' > "${kpi_conf}"

  local rc
  set +e
  bash "${DATA_LABEL_DOC_KPI}" "${asm}" "${kpi_conf}" \
    >"${NESREV_TEST_TMPDIR}/stdout" \
    2>"${NESREV_TEST_TMPDIR}/stderr"
  rc=$?
  set -e

  assert_eq "${rc}" "68" "data-label KPI must fail when noncompliant count exceeds max"
  local stderr
  stderr="$(cat "${NESREV_TEST_TMPDIR}/stderr")"
  assert_match "Noncompliant data labels" "${stderr}"
  assert_match "FourthStream:missing Used by: \\(family header of ThirdStream" "${stderr}"
}
