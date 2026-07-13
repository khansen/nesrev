#!/usr/bin/env bash
# Tests the advisory base-readability KPI (scripts/base_readability_kpi.sh) and
# its opt-in plumbing (BASE_READABILITY_ADVISORY in project_common.sh).

BASE_READABILITY="${REPO_ROOT}/scripts/base_readability_kpi.sh"

_write_fixture() {
  local path="$1"
  cat > "${path}" <<'EOF'
Foo:
    LDX #$00        ; flag: index seed
    LDY #$01        ; flag: index seed
    CPX #$00        ; flag: index compare
    CPY #$01        ; flag: index compare
    ADC #$01        ; flag: unit-step add
    SBC #$01        ; flag: unit-step subtract
    SBC #$00        ; ignore: borrow fold, not #$01
    ADC #$00        ; ignore: carry fold, not #$01
    LDA #$00        ; ignore: could be tile/sentinel
    LDA #$01        ; ignore: could be flag/token
    AND #$00        ; ignore: mask
    ORA #$00        ; ignore: mask
    LDX #0          ; ignore: already decimal
Bar: LDY #$00       ; flag: label-prefixed index seed
EOF
}

test_base_readability_flags_index_and_unit_step() {
  local fx="${NESREV_TEST_TMPDIR}/flag.asm"
  _write_fixture "${fx}"
  local out
  out="$(bash "${BASE_READABILITY}" "${fx}" 2>/dev/null)"
  # 6 index-register hits (LDX/LDY/CPX/CPY $00/$01) + 2 unit-step (ADC/SBC #$01)
  # + 1 label-prefixed LDY #$00 = 7 total.
  assert_match "strict_hex_quantity_immediates=7" "${out}" \
    "expected 7 flagged quantity immediates"
}

test_base_readability_ignores_noncount_and_decimal() {
  local fx="${NESREV_TEST_TMPDIR}/ignore.asm"
  cat > "${fx}" <<'EOF'
    SBC #$00
    ADC #$00
    LDA #$00
    LDA #$01
    AND #$00
    ORA #$00
    LDX #0
    LDY #1
EOF
  local out
  out="$(bash "${BASE_READABILITY}" "${fx}" 2>/dev/null)"
  assert_match "strict_hex_quantity_immediates=0" "${out}" \
    "borrow/carry folds, LDA/AND/ORA zeros, and decimal must not be flagged"
}

test_base_readability_reports_site_hint_on_stderr() {
  local fx="${NESREV_TEST_TMPDIR}/hint.asm"
  printf '    LDX #$00\n' > "${fx}"
  local err
  err="$(bash "${BASE_READABILITY}" "${fx}" 2>&1 1>/dev/null)"
  assert_match "use LDX #0" "${err}" "report should suggest the decimal form"
  assert_match "index/count context" "${err}" "report should name the context"
}

test_base_readability_report_mode_exits_zero_with_hits() {
  local fx="${NESREV_TEST_TMPDIR}/report.asm"
  printf '    LDX #$00\n    ADC #$01\n' > "${fx}"
  # Without --strict the check is a non-failing report even with hits.
  assert_exit 0 bash "${BASE_READABILITY}" "${fx}"
}

test_base_readability_strict_fails_on_hits() {
  local fx="${NESREV_TEST_TMPDIR}/strict_fail.asm"
  printf '    LDX #$00\n    ADC #$01\n' > "${fx}"
  # --strict hard-fails (exit 68) when the count is non-zero.
  assert_exit 68 bash "${BASE_READABILITY}" "${fx}" --strict
}

test_base_readability_strict_passes_when_clean() {
  local fx="${NESREV_TEST_TMPDIR}/strict_ok.asm"
  printf 'Loop:\n    LDX #0\n    LDA #$00\n    AND #$00\n    DEX\n' > "${fx}"
  # Machine-oriented hex zeros (LDA/AND) do not count, so --strict passes.
  assert_exit 0 bash "${BASE_READABILITY}" "${fx}" --strict
}

test_base_readability_clean_file_reports_zero() {
  local fx="${NESREV_TEST_TMPDIR}/clean.asm"
  printf 'Loop:\n    LDX #0\n    LDA #$00\n    DEX\n' > "${fx}"
  local out
  out="$(bash "${BASE_READABILITY}" "${fx}" 2>/dev/null)"
  assert_match "strict_hex_quantity_immediates=0" "${out}" "clean file should report zero"
}

test_base_readability_missing_file_errors() {
  assert_exit 65 bash "${BASE_READABILITY}" "${NESREV_TEST_TMPDIR}/does_not_exist.asm"
}

_load_flag() {
  local slug="$1"
  bash -c '
    set -euo pipefail
    cd "'"${REPO_ROOT}"'"
    source scripts/project_common.sh
    load_project_conf "'"${slug}"'" >/dev/null 2>&1
    echo "${BASE_READABILITY_REQUIRED}"
  '
}

test_base_readability_required_defaults_off() {
  local slug rom
  slug="$(unique_slug brreq_off)"
  rom="${NESREV_TEST_TMPDIR}/rom.nes"
  make_ines "${rom}"
  scaffold_project "${slug}" "${rom}"
  local flag
  flag="$(_load_flag "${slug}")"
  cleanup_project "${slug}"
  assert_eq "0" "${flag}" "legacy projects default BASE_READABILITY_REQUIRED off"
}

test_base_readability_required_opt_in_via_conf() {
  local slug rom
  slug="$(unique_slug brreq_on)"
  rom="${NESREV_TEST_TMPDIR}/rom.nes"
  make_ines "${rom}"
  scaffold_project "${slug}" "${rom}"
  printf 'BASE_READABILITY_REQUIRED="1"\n' >> "projects/${slug}/project.conf"
  local flag
  flag="$(_load_flag "${slug}")"
  cleanup_project "${slug}"
  assert_eq "1" "${flag}" "project.conf opt-in must enable the gate flag"
}
