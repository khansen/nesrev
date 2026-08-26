#!/usr/bin/env bash

PRIOR_REUSE_CHECK="${REPO_ROOT}/scripts/prior_project_reuse_check.py"
SCORECARD_ANALOGUE="${REPO_ROOT}/scripts/scorecard_analogue.py"

_write_reuse_fixture() {
  local current="$1" analogue="$2"
  cat > "${analogue}" <<'ASM'
PAD_STROBE_ON       .EQU %00000001
PAD_BTN_START       .EQU %00010000
PAD_BTN_SELECT      .EQU %00100000
PAD_UNUSED_MASK     .EQU %01000000
ZAPPER_TRIGGER_BIT  .EQU %00010000
ZAPPER_LIGHT_BIT    .EQU %00001000
LONE_ENABLE_BIT     .EQU %10000000
ZP_AnalogueScratch  .EQU $10
ASM
  cat > "${current}" <<'ASM'
PAD_STROBE_ON       .EQU %00000001
PPUCTRL_BG_PT_1000  .EQU %00010000
ZP_JoypadHeld       .EQU $16
JOY2                .EQU $4017

PollInput:
    LDA ZP_JoypadHeld
    AND #$10
    CMP #%00100000
    RTS

PollZapper:
    LDA JOY2
    AND #%00010000
    LDA JOY2
    AND #$08
    RTS

Unrelated:
    ORA #$80
    LDA $10
    RTS
ASM
}

test_prior_project_reuse_reports_anchored_and_paired_bitmask_families() {
  local current="${NESREV_TEST_TMPDIR}/current.asm"
  local analogue="${NESREV_TEST_TMPDIR}/analogue.asm"
  _write_reuse_fixture "${current}" "${analogue}"

  local output
  output="$(python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${analogue}" --analogue-slug prior_project)"

  assert_match "PAD_BTN_START" "${output}"
  assert_match "PAD_BTN_SELECT" "${output}"
  assert_match "shared-family" "${output}"
  assert_match "ZAPPER_TRIGGER_BIT" "${output}"
  assert_match "ZAPPER_LIGHT_BIT" "${output}"
  assert_match "paired-bitmask-family" "${output}"
  assert_match "current_same_value=PPUCTRL_BG_PT_1000" "${output}"
}

test_prior_project_reuse_default_is_advisory_and_strict_proves_bad_direction() {
  local current="${NESREV_TEST_TMPDIR}/current.asm"
  local analogue="${NESREV_TEST_TMPDIR}/analogue.asm"
  _write_reuse_fixture "${current}" "${analogue}"

  assert_exit 0 python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${analogue}" --analogue-slug prior_project
  assert_exit 3 python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${analogue}" --analogue-slug prior_project --strict
}

test_prior_project_reuse_suppresses_unsupported_collisions_and_addresses() {
  local current="${NESREV_TEST_TMPDIR}/current.asm"
  local analogue="${NESREV_TEST_TMPDIR}/analogue.asm"
  _write_reuse_fixture "${current}" "${analogue}"

  local output
  output="$(python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${analogue}" --analogue-slug prior_project)"

  if [[ "${output}" == *"PAD_UNUSED_MASK"* ]]; then
    fail "an analogue constant with no matching raw immediate must not be suggested"
  fi
  if [[ "${output}" == *"LONE_ENABLE_BIT"* ]]; then
    fail "one unanchored same-value collision must not create a family candidate"
  fi
  if [[ "${output}" == *"ZP_AnalogueScratch"* ]]; then
    fail "RAM/ZP address families must not be analogue constant candidates"
  fi
}

test_prior_project_reuse_suppresses_low_values_identity_families_and_wrong_context() {
  local current="${NESREV_TEST_TMPDIR}/current.asm"
  local analogue="${NESREV_TEST_TMPDIR}/analogue.asm"
  cat > "${analogue}" <<'ASM'
PAD_STROBE_ON       .EQU %00000001
PAD_BTN_START       .EQU %00010000
PPU_PACKET_END      .EQU 0
GAME_MODE_C_CLAY    .EQU 2
GAME_MODE_A         .EQU 0
PAD_REPEAT_DELAY    .EQU 8
OAM_HIDDEN_Y        .EQU $F0
ASM
  cat > "${current}" <<'ASM'
PAD_STROBE_ON       .EQU %00000001
GAME_MODE_A         .EQU 0
UnrelatedMath:
    LDA #$10
    LDX #2
    LDA #0
    LDA ZP_JoypadHeld
    AND #$FB
    LDA RAM_OamShadowBase
    AND #$F0
    RTS
ASM

  local output
  output="$(python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${analogue}" --analogue-slug prior_project --strict)"
  assert_match "OK: no evidence-backed" "${output}"
}

test_prior_project_reuse_is_clean_after_symbolization() {
  local current="${NESREV_TEST_TMPDIR}/current.asm"
  local analogue="${NESREV_TEST_TMPDIR}/analogue.asm"
  cat > "${analogue}" <<'ASM'
PAD_STROBE_ON .EQU %00000001
PAD_BTN_START .EQU %00010000
ASM
  cat > "${current}" <<'ASM'
PAD_STROBE_ON .EQU %00000001
PAD_BTN_START .EQU %00010000
PollInput:
    AND #PAD_BTN_START
    RTS
ASM

  local output
  output="$(python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${analogue}" --analogue-slug prior_project --strict)"
  assert_match "OK: no evidence-backed" "${output}"
}

test_prior_project_reuse_reports_missing_input_cleanly() {
  local current="${NESREV_TEST_TMPDIR}/current.asm"
  printf 'Reset:\n    RTS\n' > "${current}"

  assert_exit 65 python3 "${PRIOR_REUSE_CHECK}" \
    "${current}" "${NESREV_TEST_TMPDIR}/missing.asm" --analogue-slug prior_project
}

test_scorecard_analogue_optional_mode_skips_legacy_pass_without_record() {
  local scorecard="${NESREV_TEST_TMPDIR}/PROGRESS_SCORECARD.md"
  cat > "${scorecard}" <<'MD'
| pass_id | notes |
|---|---|
| 1 | Imported before the analogue-note contract. |
MD

  assert_exit 1 python3 "${SCORECARD_ANALOGUE}" "${scorecard}"
  local output
  output="$(python3 "${SCORECARD_ANALOGUE}" "${scorecard}" --optional)"
  assert_eq "${output}" "" "legacy optional mode should emit no analogue"
}
