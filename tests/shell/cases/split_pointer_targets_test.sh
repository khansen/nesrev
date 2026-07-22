#!/usr/bin/env bash
# Tests split low/high pointer target inventories.

SPLIT_TARGETS="${REPO_ROOT}/scripts/split_pointer_targets.py"
SPLIT_TARGETS_CHECK="${REPO_ROOT}/scripts/split_pointer_targets_check.sh"

test_split_pointer_targets_extracts_paired_tables() {
  local asm="${NESREV_TEST_TMPDIR}/split_targets.asm"
  local csv="${NESREV_TEST_TMPDIR}/split_pointer_targets.csv"

  cat > "${asm}" <<'ASM'
CodeTarget:
  RTS

DataTarget:
  .DB $00

FramePtrLoTable:
  .DB <DataTarget,<CodeTarget
  .DB <(DataTarget+3)
FramePtrHiTable:
  .DB >DataTarget,>CodeTarget
  .DB >(DataTarget+3)
ASM

  python3 "${SPLIT_TARGETS}" "${asm}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
lo_source,hi_source,entry,target_label,target_type,confidence,notes
FramePtrLoTable,FramePtrHiTable,0,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive; split low/high table pair
FramePtrLoTable,FramePtrHiTable,1,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction; split low/high table pair
FramePtrLoTable,FramePtrHiTable,2,DataTarget+3,data_pointer,high confidence,auto-classified from target label leading data directive; split low/high table pair
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "split pointer target extractor must pair low/high entries and classify target kinds"
}

test_split_pointer_targets_check_rejects_stale_registry() {
  local asm="${NESREV_TEST_TMPDIR}/split_targets_stale.asm"
  local csv="${NESREV_TEST_TMPDIR}/split_pointer_targets.csv"

  cat > "${asm}" <<'ASM'
DataTarget:
  .DB $00

FramePtrLoTable:
  .DB <DataTarget
FramePtrHiTable:
  .DB >DataTarget
ASM

  cat > "${csv}" <<'CSV'
lo_source,hi_source,entry,target_label,target_type,confidence,notes
CSV

  assert_exit 67 bash "${SPLIT_TARGETS_CHECK}" "${asm}" "${csv}"
}

test_split_pointer_targets_rejects_raw_split_table_entries() {
  local asm="${NESREV_TEST_TMPDIR}/split_targets_raw.asm"

  cat > "${asm}" <<'ASM'
DataTarget:
  .DB $00

FramePtrLoTable:
  .DB $00
FramePtrHiTable:
  .DB >DataTarget
ASM

  set +e
  python3 "${SPLIT_TARGETS}" "${asm}" \
    >"${NESREV_TEST_TMPDIR}/raw.out" \
    2>"${NESREV_TEST_TMPDIR}/raw.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "68" "raw bytes in a named split pointer table must fail"
  assert_match "must use symbolic <Target" "$(cat "${NESREV_TEST_TMPDIR}/raw.err")"
}

test_split_pointer_targets_rejects_entry_target_mismatch() {
  local asm="${NESREV_TEST_TMPDIR}/split_targets_mismatch.asm"

  cat > "${asm}" <<'ASM'
TargetA:
  .DB $00
TargetB:
  .DB $00

FramePtrLoTable:
  .DB <TargetA
FramePtrHiTable:
  .DB >TargetB
ASM

  set +e
  python3 "${SPLIT_TARGETS}" "${asm}" \
    >"${NESREV_TEST_TMPDIR}/mismatch.out" \
    2>"${NESREV_TEST_TMPDIR}/mismatch.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "68" "mismatched low/high split pointer entries must fail"
  assert_match "target mismatch" "$(cat "${NESREV_TEST_TMPDIR}/mismatch.err")"
}

test_split_pointer_targets_ignores_non_pointer_low_high_tables() {
  local asm="${NESREV_TEST_TMPDIR}/split_targets_ignored.asm"
  local csv="${NESREV_TEST_TMPDIR}/split_pointer_targets.csv"

  cat > "${asm}" <<'ASM'
GradientLoTable:
  .DB $00,$10,$20
GradientHiTable:
  .DB $80,$90,$A0
ASM

  python3 "${SPLIT_TARGETS}" "${asm}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
lo_source,hi_source,entry,target_label,target_type,confidence,notes
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "non-pointer low/high table names must not be treated as split pointer registries"
}
