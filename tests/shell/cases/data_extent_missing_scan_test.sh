#!/usr/bin/env bash
# Tests the advisory scan that flags bounded-index data tables which lack a
# data_extent_assertions.csv entry. The scan is a pure join of two cached
# artifacts (index_patterns.json + data_consumers.json) that xasm produces; it
# never assembles. The tests generate both artifacts, then run the scan.

MISSING_SCAN="${REPO_ROOT}/scripts/data_extent_missing_scan.py"
XASM="${XASM_BIN:-xasm}"

# Fixture exercising every case the scan must get right:
#  - RawMaskTable : AND #$03 / TAY / LDA T,Y            -> bound 4, flagged
#  - SymMaskTable : MASK EQU $03 / AND #MASK / TAY      -> resolves to 4, flagged
#  - LoopTable    : LDA T,X / INX / CPX #$08            -> bound 8, flagged
#  - MismTable    : AND #$03 / TAX  but read via Y      -> no bound, not flagged
#  - UnrelTable   : AND #$03 feeds a store, unbounded Y -> no bound, not flagged
_write_missing_scan_fixture_asm() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
SELMASK EQU $03
RawMask:
  AND #$03
  TAY
  LDA RawMaskTable,Y
  RTS
RawMaskTable:
.DB $00,$55,$AA,$FF
SymMask:
  LDA $10
  AND #SELMASK
  TAY
  LDA SymMaskTable,Y
  RTS
SymMaskTable:
.DB $00,$55,$AA,$FF
CompareLoop:
  LDX #$00
CopyLoop:
  LDA LoopTable,X
  STA $0300,X
  INX
  CPX #$08
  BNE CopyLoop
  RTS
LoopTable:
.DB 0,1,2,3,4,5,6,7
RegMismatch:
  AND #$03
  TAX
  LDY $11
  LDA MismTable,Y
  RTS
MismTable:
.DB $00,$01,$02,$03
Unrelated:
  LDA $12
  AND #$03
  STA $13
  LDY $14
  LDA UnrelTable,Y
  RTS
UnrelTable:
.DB $00,$01,$02,$03
Done:
  RTS
ASM
}

# Produce the two cached artifacts the scan consumes.
_gen_artifacts() {
  local asm="$1" ip="$2" dc="$3"
  "${XASM}" --pure-binary -o "${NESREV_TEST_TMPDIR}/mscan.o" \
    --analyze-index-patterns --index-patterns-output="${ip}" --index-patterns-format=json \
    --data-consumers --data-consumers-output="${dc}" --data-consumers-format=json \
    "${asm}" >/dev/null
}

test_missing_scan_flags_bounded_tables_including_symbolic() {
  local asm="${NESREV_TEST_TMPDIR}/mscan.asm"
  local ip="${NESREV_TEST_TMPDIR}/index_patterns.json"
  local dc="${NESREV_TEST_TMPDIR}/data_consumers.json"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_missing_scan_fixture_asm "${asm}"
  _gen_artifacts "${asm}" "${ip}" "${dc}"
  printf 'label,expected_size,reason\n' > "${csv}"

  # With no assertions, all three bounded tables are reported (exit 1).
  assert_exit 1 python3 "${MISSING_SCAN}" "${ip}" "${dc}" "${csv}"

  local out
  out="$(python3 "${MISSING_SCAN}" "${ip}" "${dc}" "${csv}" 2>&1 || true)"
  assert_match 'RawMaskTable' "${out}" "raw-mask table should be flagged"
  # The symbolic mask (AND #MASK) is the case the old regex detector missed;
  # xasm resolves it, so it must now be flagged.
  assert_match 'SymMaskTable' "${out}" "symbolic-mask table should be flagged"
  assert_match 'LoopTable' "${out}" "compare-loop table should be flagged"
  if [[ "${out}" == *MismTable* ]]; then
    fail "register-mismatch table must not be flagged"
  fi
  if [[ "${out}" == *UnrelTable* ]]; then
    fail "unrelated-mask table must not be flagged"
  fi
}

test_missing_scan_quiet_when_asserted() {
  local asm="${NESREV_TEST_TMPDIR}/mscan.asm"
  local ip="${NESREV_TEST_TMPDIR}/index_patterns.json"
  local dc="${NESREV_TEST_TMPDIR}/data_consumers.json"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_missing_scan_fixture_asm "${asm}"
  _gen_artifacts "${asm}" "${ip}" "${dc}"
  cat > "${csv}" <<'CSV'
label,expected_size,reason
RawMaskTable,4,masked index
SymMaskTable,4,symbolic masked index
LoopTable,8,compare loop
CSV

  # All bounded tables asserted -> nothing left to report (exit 0).
  assert_exit 0 python3 "${MISSING_SCAN}" "${ip}" "${dc}" "${csv}"
}

test_missing_scan_skips_without_cache() {
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  printf 'label,expected_size,reason\n' > "${csv}"
  # No cached artifacts -> advisory skips cleanly (exit 0), never assembles.
  assert_exit 0 python3 "${MISSING_SCAN}" \
    "${NESREV_TEST_TMPDIR}/absent_index_patterns.json" \
    "${NESREV_TEST_TMPDIR}/absent_data_consumers.json" "${csv}"
}
