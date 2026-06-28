#!/usr/bin/env bash
# Tests callable-procedure documentation KPI reporting and detail output.

PROCEDURE_DOC_KPI="${REPO_ROOT}/scripts/procedure_doc_kpi.sh"

_write_procedure_kpi_fixture() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
; Reset calls both documented and undocumented procedures.
Reset:
  JSR DocumentedProc
  JSR UndocumentedProc
  JMP UndocumentedTail

; Helper contract that should count as documented.
DocumentedProc:
  RTS

UndocumentedProc:
  RTS

UndocumentedTail:
  RTS

UncalledGlobal:
  RTS
ASM
}

_write_documented_procedure_kpi_fixture() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
; Reset calls documented procedures only.
Reset:
  JSR DocumentedProc
  JMP DocumentedTail

; Helper contract that should count as documented.
DocumentedProc:
  RTS

; Tail contract that should count as documented.
DocumentedTail:
  RTS
ASM
}

test_procedure_doc_kpi_counts_called_targets_only() {
  local asm="${NESREV_TEST_TMPDIR}/procedure_fixture.asm"
  _write_procedure_kpi_fixture "${asm}"

  local output
  output="$(bash "${PROCEDURE_DOC_KPI}" "${asm}")"

  assert_match "strict_callable_procedures_total=3" "${output}"
  assert_match "strict_callable_procedures_documented=1" "${output}"
  assert_match "strict_callable_procedures_undocumented=2" "${output}"
}

test_procedure_doc_kpi_detail_file_lists_undocumented_callables() {
  local asm="${NESREV_TEST_TMPDIR}/procedure_fixture.asm"
  local detail="${NESREV_TEST_TMPDIR}/procedure_detail.txt"
  _write_procedure_kpi_fixture "${asm}"
  printf 'stale detail\n' > "${detail}"

  KPI_DETAIL_FILE="${detail}" bash "${PROCEDURE_DOC_KPI}" "${asm}" >/dev/null

  local details
  details="$(cat "${detail}")"
  assert_match "^[0-9]+:UndocumentedProc"$'\n'"[0-9]+:UndocumentedTail$" "${details}"
  if grep -q 'DocumentedProc\|Reset\|UncalledGlobal\|stale detail' "${detail}"; then
    fail "procedure detail output included documented, uncalled, or stale entries: ${details}"
  fi
}

test_procedure_doc_kpi_detail_file_empty_when_all_callables_documented() {
  local asm="${NESREV_TEST_TMPDIR}/documented_procedure_fixture.asm"
  local detail="${NESREV_TEST_TMPDIR}/documented_procedure_detail.txt"
  _write_documented_procedure_kpi_fixture "${asm}"
  printf 'stale detail\n' > "${detail}"

  KPI_DETAIL_FILE="${detail}" bash "${PROCEDURE_DOC_KPI}" "${asm}" >/dev/null

  assert_eq "$(cat "${detail}")" "" \
    "documented callable set must leave requested detail file empty"
}

test_procedure_doc_kpi_without_detail_env_leaves_no_temp_detail_file() {
  local asm="${NESREV_TEST_TMPDIR}/procedure_fixture.asm"
  local detail_tmp="${NESREV_TEST_TMPDIR}/detail_tmp"
  _write_procedure_kpi_fixture "${asm}"
  mkdir -p "${detail_tmp}"

  TMPDIR="${detail_tmp}/" bash "${PROCEDURE_DOC_KPI}" "${asm}" >/dev/null

  local leftover_count
  leftover_count="$(find "${detail_tmp}" -type f | wc -l | tr -d '[:space:]')"
  assert_eq "${leftover_count}" "0" \
    "unset KPI_DETAIL_FILE must not leave a caller-visible detail artifact"
}

test_procedure_doc_kpi_failure_prints_detail() {
  local asm="${NESREV_TEST_TMPDIR}/procedure_fixture.asm"
  local kpi_conf="${NESREV_TEST_TMPDIR}/kpis.conf"
  _write_procedure_kpi_fixture "${asm}"
  printf 'MAX_UNDOCUMENTED_PROCEDURES=1\n' > "${kpi_conf}"

  local rc
  set +e
  bash "${PROCEDURE_DOC_KPI}" "${asm}" "${kpi_conf}" \
    >"${NESREV_TEST_TMPDIR}/stdout" \
    2>"${NESREV_TEST_TMPDIR}/stderr"
  rc=$?
  set -e

  assert_eq "${rc}" "68" "procedure KPI must fail when undocumented count exceeds max"
  local stderr
  stderr="$(cat "${NESREV_TEST_TMPDIR}/stderr")"
  assert_match "Undocumented callable procedures:" "${stderr}"
  assert_match "UndocumentedProc" "${stderr}"
  assert_match "UndocumentedTail" "${stderr}"
}
