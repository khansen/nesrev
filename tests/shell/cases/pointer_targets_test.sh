#!/usr/bin/env bash
# Tests pointer_targets.sh source-relative entry indexing.

POINTER_TARGETS="${REPO_ROOT}/scripts/pointer_targets.sh"

test_dw_entry_indexes_continue_until_next_source_label() {
  local asm="${NESREV_TEST_TMPDIR}/pointers.asm"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${asm}" <<'ASM'
CodeTarget:
  RTS

DataTarget:
  .DB $00

MixedPointerTable:
  .DW CodeTarget
  .DW DataTarget,UnknownTarget
  .DW $C000,CodeTarget+1

OtherPointerTable: .DW DataTarget
  .DW CodeTarget
ASM

  bash "${POINTER_TARGETS}" "${asm}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
source,entry,target_label,target_type,confidence,notes
MixedPointerTable,0,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction
MixedPointerTable,1,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive
MixedPointerTable,2,UnknownTarget,unknown_pointer,inferred,auto-extracted from .DW entry (target kind unresolved)
MixedPointerTable,4,CodeTarget+1,code_pointer,high confidence,auto-classified from target label leading instruction
OtherPointerTable,0,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive
OtherPointerTable,1,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "pointer target indexes must continue across .DW rows and reset at the next source label"
}

test_cpu_vector_fetch_dw_is_not_owned_by_previous_label() {
  local asm="${NESREV_TEST_TMPDIR}/vectors.asm"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${asm}" <<'ASM'
Reset:
  RTS

NMI:
  RTI

MusicStream:
  .DB $FF

  .DW NMI
  .DW Reset
  .DW Reset
  .END
ASM

  bash "${POINTER_TARGETS}" "${asm}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
source,entry,target_label,target_type,confidence,notes
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "CPU vector fetch words must not be assigned to the preceding data label"
}

test_terminal_vectors_do_not_hide_adjacent_dw_table_entry() {
  local asm="${NESREV_TEST_TMPDIR}/adjacent_vectors.asm"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${asm}" <<'ASM'
Reset:
  RTS

NMI:
  RTI

  DataTarget: .db $00

  TerminalData: .dw DataTarget
  @@Vectors: .dw NMI
  .dw Reset
  .dw Reset
  .END
ASM

  bash "${POINTER_TARGETS}" "${asm}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
source,entry,target_label,target_type,confidence,notes
TerminalData,0,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "terminal CPU vectors must not suppress adjacent non-vector .DW entries"
}
