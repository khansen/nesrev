#!/usr/bin/env bash
# Tests for mechanically checkable `; Used by:` xref validation.

USED_BY_CHECK="${REPO_ROOT}/scripts/used_by_xref_check.py"

test_used_by_xref_check_accepts_direct_data_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_direct.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader.
DataTable:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" "${asm}" >/dev/null
}

test_used_by_xref_check_rejects_stale_direct_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_stale.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS
OtherReader:
  RTS

; Format: one byte.
; Used by: OtherReader.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --strict "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "stale Used by comment must fail"
  assert_match "OtherReader" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_accepts_consumer_through_pointer_table() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_indirect.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA PtrTable
  RTS

; Format: pointer table.
; Used by: Reader.
PtrTable:
.DW Payload

; Format: payload bytes.
; Used by: Reader through PtrTable.
Payload:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" "${asm}" >/dev/null
}

test_used_by_xref_check_rejects_prg_banking_without_consumer_symbol() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_banking.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS

; Format: one byte.
; Used by: selected through MMC1 PRG banking.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "generic MMC1 banking Used by comment must fail"
  assert_match "PRG banking" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}
