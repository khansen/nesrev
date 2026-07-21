#!/usr/bin/env bash
# Tests the advisory scan that flags bounded-index data tables which lack a
# data_extent_assertions.csv entry. The scan consumes the --data-consumers
# cache (it does not re-assemble), so the tests generate that cache first.

MISSING_SCAN="${REPO_ROOT}/scripts/data_extent_missing_scan.py"

# Fixture: DefaultTable is read via `AND #$03 / TAY / LDA DefaultTable,Y`
# (a masked index proving a 4-entry bound). UnboundedTable is read via a plain
# `LDA UnboundedTable,Y` with no mask/count, so it must NOT be flagged.
_write_missing_scan_fixture_asm() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
FillFromDefaults:
  AND #$03
  TAY
  LDA DefaultTable,Y
  RTS
DefaultTable:
.DB $00,$55,$AA,$FF
ReadUnbounded:
  LDY $10
  LDA UnboundedTable,Y
  RTS
UnboundedTable:
.DB $10,$20,$30,$40
Done:
  RTS
ASM
}

_gen_data_consumers() {
  local asm="$1" json="$2"
  xasm --pure-binary -o "${NESREV_TEST_TMPDIR}/dc.o" \
    --data-consumers --data-consumers-output="${json}" \
    --data-consumers-format=json "${asm}" >/dev/null
}

test_missing_scan_flags_bounded_unasserted_table() {
  local asm="${NESREV_TEST_TMPDIR}/missing.asm"
  local json="${NESREV_TEST_TMPDIR}/data_consumers.json"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_missing_scan_fixture_asm "${asm}"
  _gen_data_consumers "${asm}" "${json}"
  printf 'label,expected_size,reason\n' > "${csv}"

  # With no assertion, the masked-index table must be reported (exit 1).
  assert_exit 1 python3 "${MISSING_SCAN}" "${json}" "${asm}" "${csv}"

  local out
  out="$(python3 "${MISSING_SCAN}" "${json}" "${asm}" "${csv}" 2>&1 || true)"
  assert_match 'DefaultTable' "${out}" "masked-index table should be flagged"
  if [[ "${out}" == *UnboundedTable* ]]; then
    fail "unbounded-index table must not be flagged"
  fi
}

test_missing_scan_quiet_when_asserted() {
  local asm="${NESREV_TEST_TMPDIR}/missing.asm"
  local json="${NESREV_TEST_TMPDIR}/data_consumers.json"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_missing_scan_fixture_asm "${asm}"
  _gen_data_consumers "${asm}" "${json}"
  cat > "${csv}" <<'CSV'
label,expected_size,reason
DefaultTable,4,fixture default table indexed by a masked value
CSV

  # Once asserted, the only candidate drops out -> no findings (exit 0).
  assert_exit 0 python3 "${MISSING_SCAN}" "${json}" "${asm}" "${csv}"
}

# False positive guard: an unrelated `AND #$03` (feeding a store, not the index)
# in the same routine as an UNBOUNDED index into a coincidentally size-4 table
# must NOT be flagged, because the mask never reaches the index register.
_write_unrelated_mask_fixture_asm() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
Routine:
  LDA $10
  AND #$03        ; masks a flag -> store, NOT the table index
  STA $11
  LDY $12         ; index has no bound proof
  LDA CoincidentTable,Y
  RTS
CoincidentTable:
.DB $00,$01,$02,$03
Done:
  RTS
ASM
}

test_missing_scan_ignores_unrelated_mask_in_routine() {
  local asm="${NESREV_TEST_TMPDIR}/fp_mask.asm"
  local json="${NESREV_TEST_TMPDIR}/data_consumers.json"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_unrelated_mask_fixture_asm "${asm}"
  _gen_data_consumers "${asm}" "${json}"
  printf 'label,expected_size,reason\n' > "${csv}"

  # Mask feeds a store, not TAY -> no bound proof -> no findings (exit 0).
  assert_exit 0 python3 "${MISSING_SCAN}" "${json}" "${asm}" "${csv}"
}

# False positive guard: a mask transferred to the WRONG index register (masked
# into X, but the table is read with Y) must NOT be flagged.
_write_register_mismatch_fixture_asm() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
Routine:
  AND #$03        ; masked value goes to X ...
  TAX
  LDY $12         ; ... but the table is indexed by Y (unbounded)
  LDA MismatchTable,Y
  RTS
MismatchTable:
.DB $00,$01,$02,$03
Done:
  RTS
ASM
}

test_missing_scan_ignores_wrong_index_register() {
  local asm="${NESREV_TEST_TMPDIR}/fp_reg.asm"
  local json="${NESREV_TEST_TMPDIR}/data_consumers.json"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_register_mismatch_fixture_asm "${asm}"
  _gen_data_consumers "${asm}" "${json}"
  printf 'label,expected_size,reason\n' > "${csv}"

  # AND -> TAX but read via Y -> register mismatch -> no findings (exit 0).
  assert_exit 0 python3 "${MISSING_SCAN}" "${json}" "${asm}" "${csv}"
}

test_missing_scan_skips_without_cache() {
  local asm="${NESREV_TEST_TMPDIR}/missing.asm"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_missing_scan_fixture_asm "${asm}"
  printf 'label,expected_size,reason\n' > "${csv}"

  # No data-consumers cache -> advisory skips cleanly (exit 0), no assembly.
  assert_exit 0 python3 "${MISSING_SCAN}" \
    "${NESREV_TEST_TMPDIR}/absent_data_consumers.json" "${asm}" "${csv}"
}
