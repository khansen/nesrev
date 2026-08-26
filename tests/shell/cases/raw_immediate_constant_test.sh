#!/usr/bin/env bash
# Tests the raw-immediate-versus-existing-constant review signal.

CHECK="${REPO_ROOT}/scripts/raw_immediate_constant_check.py"

test_raw_immediate_constant_reports_matching_state_writer() {
  local asm="${NESREV_TEST_TMPDIR}/bad.asm"
  cat > "${asm}" <<'EOF'
ROUND_STATE_SCENE_START .EQU 9
ZP_RoundState .EQU $20
Writer:
    LDA #$09
    STA ZP_RoundState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "bypassed_constant_writers=1" "${out}" \
    "same-valued gameplay-state writer must be reported"
  assert_match "ROUND_STATE_SCENE_START" "${out}" \
    "diagnostic must name the applicable constant"
}

test_raw_immediate_constant_accepts_symbolic_writer() {
  local asm="${NESREV_TEST_TMPDIR}/good.asm"
  cat > "${asm}" <<'EOF'
ROUND_STATE_SCENE_START .EQU 9
ZP_RoundState .EQU $20
Writer:
    LDA #ROUND_STATE_SCENE_START
    STA ZP_RoundState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "symbolic writer must pass"
}

test_raw_immediate_constant_requires_semantic_family_overlap() {
  local asm="${NESREV_TEST_TMPDIR}/unrelated.asm"
  cat > "${asm}" <<'EOF'
SOUND_STATE_STOPPED .EQU 3
ZP_RoundState .EQU $20
Writer:
    LDA #3
    STA ZP_RoundState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "a same-valued constant from another family must not fire"
}

test_raw_immediate_constant_ignores_structural_field_constant() {
  local asm="${NESREV_TEST_TMPDIR}/field.asm"
  cat > "${asm}" <<'EOF'
OBJECT_SLOT_FIELD_STATE .EQU 0
RAM_ObjectSlotState .EQU $300
Writer:
    LDA #0
    STA RAM_ObjectSlotState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "a field offset must not be suggested as a state value"
}

test_raw_immediate_constant_ignores_address_equates() {
  local asm="${NESREV_TEST_TMPDIR}/address.asm"
  cat > "${asm}" <<'EOF'
ZP_RoundState .EQU 0
RAM_RoundStateBase .EQU $300
Writer:
    LDA #0
    STA RAM_RoundStateBase
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "ZP/RAM address equates must never be suggested as values"
}

test_raw_immediate_constant_requires_same_register_store() {
  local asm="${NESREV_TEST_TMPDIR}/register.asm"
  cat > "${asm}" <<'EOF'
ROUND_STATE_ACTIVE .EQU 3
ZP_RoundState .EQU $20
Writer:
    LDX #3
    STA ZP_RoundState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "a different-register store is not the reviewed writer shape"
}

test_raw_immediate_constant_skips_non_state_destination() {
  local asm="${NESREV_TEST_TMPDIR}/scalar.asm"
  cat > "${asm}" <<'EOF'
TITLE_DELAY_SHORT .EQU 3
ZP_TitleDelay .EQU $20
Writer:
    LDA #3
    STA ZP_TitleDelay
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "ordinary scalar destinations stay outside the narrow signal"
}

test_raw_immediate_constant_strict_mode_proves_bad_direction() {
  local asm="${NESREV_TEST_TMPDIR}/strict.asm"
  cat > "${asm}" <<'EOF'
TITLE_STATE_MENU .EQU 1
ZP_TitleState .EQU $21
Writer:
    LDA #1
    STA ZP_TitleState
EOF
  assert_exit 68 python3 "${CHECK}" "${asm}" --strict
}

test_raw_immediate_constant_does_not_skip_implicit_operand_opcode() {
  local asm="${NESREV_TEST_TMPDIR}/implicit_opcode.asm"
  cat > "${asm}" <<'EOF'
MENU_STATE_ACTIVE .EQU 1
ZP_MenuState .EQU $21
Writer:
    LDA #1
    ASL
    STA ZP_MenuState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "a bare accumulator opcode must stop immediate/store pairing"
}

test_raw_immediate_constant_does_not_cross_return_boundary() {
  local asm="${NESREV_TEST_TMPDIR}/return_boundary.asm"
  cat > "${asm}" <<'EOF'
MENU_STATE_ACTIVE .EQU 1
ZP_MenuState .EQU $21
FirstRoutine:
    LDA #1
    RTS
SecondRoutine:
    STA ZP_MenuState
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "bypassed_constant_writers=0" "${out}" \
    "a bare return must stop pairing across routine boundaries"
}

test_raw_immediate_constant_report_mode_is_advisory() {
  local asm="${NESREV_TEST_TMPDIR}/report.asm"
  cat > "${asm}" <<'EOF'
TITLE_STATE_MENU .EQU 1
ZP_TitleState .EQU $21
Writer:
    LDA #1
    STA ZP_TitleState
EOF
  assert_exit 0 python3 "${CHECK}" "${asm}"
}

test_raw_immediate_constant_missing_file_errors() {
  assert_exit 65 python3 "${CHECK}" "${NESREV_TEST_TMPDIR}/missing.asm"
}

test_raw_immediate_constant_rejects_unknown_option() {
  local asm="${NESREV_TEST_TMPDIR}/unknown_option.asm"
  printf 'Writer:\n    RTS\n' > "${asm}"
  assert_exit 64 python3 "${CHECK}" "${asm}" --stict
  assert_exit 64 python3 "${CHECK}" "${asm}" --strict=1
}

test_raw_immediate_constant_reports_non_utf8_input_cleanly() {
  local asm="${NESREV_TEST_TMPDIR}/non_utf8.asm"
  printf '\377' > "${asm}"
  assert_exit 65 python3 "${CHECK}" "${asm}"
}

test_raw_immediate_constant_is_opt_in_process_advisory() {
  local process_check
  process_check="$(cat "${REPO_ROOT}/scripts/project_process_check.sh")"
  assert_match 'PROOF_DEBT_REQUIRED.*==.*1' "${process_check}" \
    "legacy projects must stay outside the new advisory"
  assert_match 'raw_immediate_constant_check.py' "${process_check}" \
    "opted-in process checks must surface the signal"
  if printf '%s' "${process_check}" | grep -q 'raw_immediate_constant_check.py.*--strict'; then
    fail "corpus calibration does not support making the shared check strict"
  fi
}
