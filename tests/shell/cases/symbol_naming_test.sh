#!/usr/bin/env bash

test_accepts_upper_camel_ram_and_zp_names() {
  local asm="${NESREV_TEST_TMPDIR}/good.asm"
  printf '%s\n' \
    'ZP_PpuCtrlShadow .EQU $00' \
    'ZP_PlayerPosXLo .EQU $01' \
    'RAM_OamShadowBase .EQU $0200' \
    'RAM_P1ScoreBcd .EQU $0300' >"${asm}"

  python3 scripts/check_symbol_naming.py "${asm}"
}

test_tracked_primary_checks_current_tracked_project_asm() {
  local output
  output="$(python3 scripts/check_symbol_naming.py --tracked-primary)"
  assert_match "OK: canonical symbol naming in [0-9]+ asm file" "${output}"
}

test_rejects_additional_underscores() {
  local asm="${NESREV_TEST_TMPDIR}/bad_underscore.asm"
  printf '%s\n' 'ZP_PPUCTRL_SHADOW .EQU $00' >"${asm}"

  set +e
  local output
  output="$(python3 scripts/check_symbol_naming.py "${asm}" 2>&1)"
  local rc=$?
  set -e

  assert_eq "${rc}" "1" "underscore-separated ZP name must fail"
  assert_match "ZP_PPUCTRL_SHADOW must use" "${output}"
}

test_rejects_uppercase_acronyms_in_symbol_body() {
  local asm="${NESREV_TEST_TMPDIR}/bad_acronym.asm"
  printf '%s\n' 'RAM_OAMShadowBase .EQU $0200' >"${asm}"

  set +e
  local output
  output="$(python3 scripts/check_symbol_naming.py "${asm}" 2>&1)"
  local rc=$?
  set -e

  assert_eq "${rc}" "1" "uppercase acronym in RAM name must fail"
  assert_match "RAM_OAMShadowBase must use" "${output}"
}

test_accepts_canonical_ppuctrl_pattern_table_bits() {
  local asm="${NESREV_TEST_TMPDIR}/good_ppuctrl.asm"
  printf '%s\n' \
    'PPUCTRL_SPRITE_PT_1000 .EQU %00001000' \
    'PPUCTRL_BG_PT_1000 .EQU %00010000' >"${asm}"

  python3 scripts/check_symbol_naming.py "${asm}"
}

test_rejects_inverted_ppuctrl_pattern_table_names() {
  local asm="${NESREV_TEST_TMPDIR}/bad_ppuctrl.asm"
  printf '%s\n' \
    'PPUCTRL_BG_PT_1000 .EQU %00001000' \
    'PPUCTRL_SPRITE_PT_1000 .EQU $10' >"${asm}"

  set +e
  local output
  output="$(python3 scripts/check_symbol_naming.py "${asm}" 2>&1)"
  local rc=$?
  set -e

  assert_eq "${rc}" "1" "inverted PPUCTRL pattern-table names must fail"
  assert_match "PPUCTRL_BG_PT_1000 assigns PPUCTRL pattern-table bit 0x08" "${output}"
  assert_match "PPUCTRL_SPRITE_PT_1000 assigns PPUCTRL pattern-table bit 0x10" "${output}"
}

test_rejects_noncanonical_ppuctrl_pattern_aliases() {
  local asm="${NESREV_TEST_TMPDIR}/legacy_ppuctrl.asm"
  printf '%s\n' \
    'PPUCTRL_BG_CHR1 .EQU $10' \
    'PPUCTRL_SPRITE_PATTERN_TABLE .EQU $08' >"${asm}"

  set +e
  local output
  output="$(python3 scripts/check_symbol_naming.py "${asm}" 2>&1)"
  local rc=$?
  set -e

  assert_eq "${rc}" "1" "legacy PPUCTRL pattern aliases must fail"
  assert_match "use canonical PPUCTRL_BG_PT_1000" "${output}"
  assert_match "use canonical PPUCTRL_SPRITE_PT_1000" "${output}"
}

test_accepts_canonical_hardware_register_aliases() {
  local asm="${NESREV_TEST_TMPDIR}/good_hardware.asm"
  printf '%s\n' \
    'PPUCTRL .EQU $2000' \
    'APU_PULSE1_CTRL .EQU $4000' \
    'APU_NOISE_LENGTH .EQU $400F' \
    'JOY1_STROBE .EQU $4016' >"${asm}"

  python3 scripts/check_symbol_naming.py "${asm}"
}

test_rejects_legacy_hardware_register_aliases() {
  local asm="${NESREV_TEST_TMPDIR}/legacy_hardware.asm"
  printf '%s\n' \
    'SQ1_VOL .EQU $4000' \
    'NOISE_LEN .EQU $400F' \
    'JOY1 .EQU $4016' >"${asm}"

  set +e
  local output
  output="$(python3 scripts/check_symbol_naming.py "${asm}" 2>&1)"
  local rc=$?
  set -e

  assert_eq "${rc}" "1" "legacy hardware register aliases must fail"
  assert_match "use canonical APU_PULSE1_CTRL" "${output}"
  assert_match "use canonical APU_NOISE_LENGTH" "${output}"
  assert_match "use canonical JOY1_STROBE" "${output}"
}
