#!/usr/bin/env bash
# Tests the narrow current-pass procedure-name/rename-reason advisory.

CHECK="${REPO_ROOT}/scripts/rename_reason_consistency_check.py"

_write_rename_fixture() {
  local asm="$1"
  local ledger="$2"
  cat > "${asm}" <<'EOF'
AppendPpuBufferByte:
    INC RAM_PpuBufferCursor
    RTS
AdvancePpuBufferCursor:
    INC RAM_PpuBufferCursor
    RTS
StorePacketTable:
    .DB $10,$20,$30
RAM_AppendOnlyScratch .EQU $40
EOF
  cat > "${ledger}" <<'EOF'
old_name,new_name,reason,confidence,pass_id
L8000,AppendPpuBufferByte,advances the RAM PPU buffer cursor with a capacity guard,high,4
L8010,AdvancePpuBufferCursor,advances the RAM PPU buffer cursor with a capacity guard,high,5
L8020,StorePacketTable,reads three packet bytes,high,5
raw_$40,RAM_AppendOnlyScratch,reads a shared scratch byte,scoped-overlay,5
EOF
}

test_rename_reason_reports_opposing_action_classes() {
  local asm="${NESREV_TEST_TMPDIR}/candidate.asm"
  local ledger="${NESREV_TEST_TMPDIR}/renames.csv"
  _write_rename_fixture "${asm}" "${ledger}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${ledger}" --all-passes 2>&1)"
  assert_match 'candidates=1' "${out}"
  assert_match 'AppendPpuBufferByte names a write action but its reason begins with a motion action' "${out}" \
    "the original Hogan name/reason disagreement must be reviewable"
}

test_rename_reason_defaults_to_newest_pass_and_executable_labels() {
  local asm="${NESREV_TEST_TMPDIR}/current.asm"
  local ledger="${NESREV_TEST_TMPDIR}/renames.csv"
  _write_rename_fixture "${asm}" "${ledger}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${ledger}" 2>&1)"
  assert_match 'candidates=0 pass_scope=5' "${out}" \
    "historical rows and RAM symbols must stay outside the current-pass routine signal"
}

test_rename_reason_accepts_same_action_class() {
  local asm="${NESREV_TEST_TMPDIR}/compatible.asm"
  local ledger="${NESREV_TEST_TMPDIR}/renames.csv"
  cat > "${asm}" <<'EOF'
WritePpuByte:
    STA PPUDATA
    RTS
LoadPacketByte:
    LDA (ZP_Ptr),Y
    RTS
EOF
  cat > "${ledger}" <<'EOF'
old_name,new_name,reason,confidence,pass_id
L8000,WritePpuByte,stores one byte in PPUDATA,high,3
L8010,LoadPacketByte,reads one byte from the packet stream,high,3
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" "${ledger}" 2>/dev/null)"
  assert_match 'candidates=0' "${out}" \
    "inflected synonyms within one concrete action class must agree"
}

test_rename_reason_strict_mode_proves_bad_direction() {
  local asm="${NESREV_TEST_TMPDIR}/strict.asm"
  local ledger="${NESREV_TEST_TMPDIR}/renames.csv"
  _write_rename_fixture "${asm}" "${ledger}"
  assert_exit 68 python3 "${CHECK}" "${asm}" "${ledger}" --all-passes --strict
  assert_exit 0 python3 "${CHECK}" "${asm}" "${ledger}" --all-passes
}

test_rename_reason_rejects_bad_cli_and_malformed_input() {
  local asm="${NESREV_TEST_TMPDIR}/bad.asm"
  local ledger="${NESREV_TEST_TMPDIR}/bad.csv"
  printf 'Reset:\n    RTS\n' > "${asm}"
  printf 'wrong,header\nvalue,row\n' > "${ledger}"
  assert_exit 64 python3 "${CHECK}"
  assert_exit 64 python3 "${CHECK}" "${asm}" "${ledger}" --stict
  assert_exit 65 python3 "${CHECK}" "${NESREV_TEST_TMPDIR}/missing.asm" "${ledger}"
  assert_exit 65 python3 "${CHECK}" "${asm}" "${ledger}"
}

test_rename_reason_is_universal_process_advisory() {
  local process_check
  process_check="$(<"${REPO_ROOT}/scripts/project_process_check.sh")"
  assert_match 'rename_reason_consistency_check\.py' "${process_check}" \
    "every project's process check must surface current-pass name/reason disagreements"
  assert_not_match 'PROOF_DEBT_REQUIRED' "${process_check}"
  if printf '%s' "${process_check}" | grep -q 'rename_reason_consistency_check.py.*--strict'; then
    fail "name/reason candidates must remain advisory until individually reviewed"
  fi
}
