#!/usr/bin/env bash
# Tests explicit data-table extent assertions.

DATA_EXTENT_CHECK="${REPO_ROOT}/scripts/data_extent_assertions_check.sh"

_write_extent_fixture_asm() {
  local asm="$1"
  cat > "${asm}" <<'ASM'
.ORG $C000
IndexedTable:
.DB $01,$02,$03
AdjacentTail:
.DB $04,$05
Reset:
  RTS
ASM
}

test_data_extent_assertions_pass_for_matching_sizes() {
  local asm="${NESREV_TEST_TMPDIR}/extent.asm"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_extent_fixture_asm "${asm}"
  cat > "${csv}" <<'CSV'
label,expected_size,reason
IndexedTable,3,fixture table has three bytes
AdjacentTail,2,fixture tail has two bytes
CSV

  bash "${DATA_EXTENT_CHECK}" "${asm}" "${csv}" >/dev/null
}

test_data_extent_assertions_fail_for_size_drift() {
  local asm="${NESREV_TEST_TMPDIR}/extent.asm"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_extent_fixture_asm "${asm}"
  cat > "${csv}" <<'CSV'
label,expected_size,reason
IndexedTable,2,fixture table should fail with stale expected size
CSV

  assert_exit 1 bash "${DATA_EXTENT_CHECK}" "${asm}" "${csv}"
}

test_data_extent_assertions_fail_for_missing_label() {
  local asm="${NESREV_TEST_TMPDIR}/extent.asm"
  local csv="${NESREV_TEST_TMPDIR}/extents.csv"
  _write_extent_fixture_asm "${asm}"
  cat > "${csv}" <<'CSV'
label,expected_size,reason
MissingTable,1,fixture missing label should fail
CSV

  assert_exit 1 bash "${DATA_EXTENT_CHECK}" "${asm}" "${csv}"
}
