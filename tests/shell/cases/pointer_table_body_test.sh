#!/usr/bin/env bash
# Tests the pointer-table body check (scripts/pointer_table_body_check.py) and
# the mandatory project-verify gate.

CHECK="${REPO_ROOT}/scripts/pointer_table_body_check.py"

_fixture() {
  cat > "$1" <<'EOF'
RawPtrTable:
.DB $76,$ED,$98,$ED,$B0,$ED
SymbolicPtrTable:
.DW SymTarget0,SymTarget1
HeaderThenSymbolicPtrTable:
.DB $FF,$00
.DW HdrTarget0,HdrTarget1
MisnamedPointerTable:
.DB $4E,$10,$4B,$26,$E5,$28
SplitPtrTable:
.DB <SplitTarget0,<SplitTarget1
LonePtr:
.DW OneThing
EOF
}

test_pointer_table_flags_raw_prg_body() {
  local fx="${NESREV_TEST_TMPDIR}/p.asm"; _fixture "${fx}"
  local out; out="$(python3 "${CHECK}" "${fx}" 2>/dev/null)"
  assert_match "raw_pointer_table_bodies=1" "${out}" "only the raw PRG table should count"
}

test_pointer_table_flags_name_and_hint_on_stderr() {
  local fx="${NESREV_TEST_TMPDIR}/p2.asm"; _fixture "${fx}"
  local err; err="$(python3 "${CHECK}" "${fx}" 2>&1 1>/dev/null)"
  assert_match "RawPtrTable" "${err}" "advisory should name the offending label"
  assert_match "relocate" "${err}" "advisory should say to relocate"
  # None of the skip cases may appear.
  if printf '%s' "${err}" | grep -qE 'SymbolicPtrTable|HeaderThenSymbolicPtrTable|MisnamedPointerTable|SplitPtrTable|LonePtr'; then
    fail "a skip-case label was flagged: ${err}"
  fi
}

test_pointer_table_flags_leading_pointer_prefix_before_payload() {
  local fx="${NESREV_TEST_TMPDIR}/prefix.asm"
  cat > "${fx}" <<'EOF'
SharedPointerTable:
.DB $00,$90,$20,$90
.DB $20,$00,$18,$11,$22,$33,$44,$55,$66,$77,$88,$99,$AA,$BB,$CC,$DD
EOF
  local out
  out="$(python3 "${CHECK}" "${fx}" 2>&1)"
  assert_match "raw_pointer_table_bodies=1" "${out}" \
    "a leading pointer run must survive dilution by payload words"
  assert_match "2 in the leading prefix" "${out}" \
    "the diagnostic must identify the prefix proof"
  assert_match "proof: leading prefix" "${out}" \
    "the diagnostic must distinguish the staged prefix-only proof"
}

test_pointer_table_report_mode_exits_zero_with_findings() {
  local fx="${NESREV_TEST_TMPDIR}/p3.asm"; _fixture "${fx}"
  assert_exit 0 python3 "${CHECK}" "${fx}"
}

test_pointer_table_strict_fails_on_findings() {
  local fx="${NESREV_TEST_TMPDIR}/p4.asm"; _fixture "${fx}"
  assert_exit 68 python3 "${CHECK}" "${fx}" --strict
}

test_pointer_table_whole_body_strict_preserves_old_gate_boundary() {
  local whole="${NESREV_TEST_TMPDIR}/whole.asm"; _fixture "${whole}"
  local prefix="${NESREV_TEST_TMPDIR}/prefix_only.asm"
  cat > "${prefix}" <<'EOF'
SharedPointerTable:
.DB $00,$90,$20,$90
.DB $20,$00,$18,$11,$22,$33,$44,$55,$66,$77,$88,$99,$AA,$BB,$CC,$DD
EOF
  assert_exit 68 python3 "${CHECK}" "${whole}" --strict-whole-body
  assert_exit 0 python3 "${CHECK}" "${prefix}" --strict-whole-body
  assert_exit 68 python3 "${CHECK}" "${prefix}" --strict
}

test_pointer_table_strict_passes_when_clean() {
  local fx="${NESREV_TEST_TMPDIR}/p5.asm"
  cat > "${fx}" <<'EOF'
GoodPtrTable:
.DW T0,T1,T2
GoodSplitPtrTable:
.DB <T0,>T0,<T1,>T1
NotAPointerTable:
.DB $01,$02,$03,$04
EOF
  assert_exit 0 python3 "${CHECK}" "${fx}" --strict
}

test_pointer_table_missing_file_errors() {
  assert_exit 65 python3 "${CHECK}" "${NESREV_TEST_TMPDIR}/nope.asm"
}

test_pointer_table_rejects_unknown_option_and_non_utf8() {
  local fx="${NESREV_TEST_TMPDIR}/cli.asm"
  printf 'Reset:\n    RTS\n' > "${fx}"
  assert_exit 64 python3 "${CHECK}" "${fx}" --stict
  assert_exit 64 python3 "${CHECK}" "${fx}" --strict=1
  assert_exit 64 python3 "${CHECK}" "${fx}" --strict --strict-whole-body
  printf '\377' > "${fx}"
  assert_exit 65 python3 "${CHECK}" "${fx}"
}

test_project_verify_stages_prefix_findings_but_maturity_is_strict() {
  local verify maturity common
  verify="$(cat "${REPO_ROOT}/scripts/project_verify.sh")"
  maturity="$(cat "${REPO_ROOT}/scripts/project_maturity_check.sh")"
  common="$(cat "${REPO_ROOT}/scripts/project_common.sh")"
  assert_match "pointer_table_body_check.py" "${verify}" \
    "project-verify must invoke the pointer-table body gate"
  if printf '%s\n%s\n' "${verify}" "${common}" | grep -q "POINTER_TABLE_RELOCATION_REQUIRED"; then
    fail "pointer-table body gate must not be guarded by POINTER_TABLE_RELOCATION_REQUIRED"
  fi
  assert_match '--strict-whole-body' "${verify}" \
    "project-verify must stage prefix-only findings as advisory"
  assert_match 'pointer_table_body_check.py' "${maturity}" \
    "project-maturity-check must invoke the pointer-table body gate"
  if printf '%s' "${maturity}" | grep -q -- '--strict-whole-body'; then
    fail "maturity must retain the full strict pointer-prefix check"
  fi
}
