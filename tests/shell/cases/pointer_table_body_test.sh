#!/usr/bin/env bash
# Tests the pointer-table body check (scripts/pointer_table_body_check.py) and
# its opt-in plumbing (POINTER_TABLE_RELOCATION_REQUIRED in project_common.sh).

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

test_pointer_table_report_mode_exits_zero_with_findings() {
  local fx="${NESREV_TEST_TMPDIR}/p3.asm"; _fixture "${fx}"
  assert_exit 0 python3 "${CHECK}" "${fx}"
}

test_pointer_table_strict_fails_on_findings() {
  local fx="${NESREV_TEST_TMPDIR}/p4.asm"; _fixture "${fx}"
  assert_exit 68 python3 "${CHECK}" "${fx}" --strict
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

_load_flag() {
  bash -c '
    set -euo pipefail
    cd "'"${REPO_ROOT}"'"
    source scripts/project_common.sh
    load_project_conf "'"$1"'" >/dev/null 2>&1
    echo "${POINTER_TABLE_RELOCATION_REQUIRED}"
  '
}

test_pointer_table_required_defaults_off() {
  local slug rom; slug="$(unique_slug ptreloc_off)"; rom="${NESREV_TEST_TMPDIR}/rom.nes"
  make_ines "${rom}"; scaffold_project "${slug}" "${rom}"
  local flag; flag="$(_load_flag "${slug}")"; cleanup_project "${slug}"
  assert_eq "0" "${flag}" "legacy projects default POINTER_TABLE_RELOCATION_REQUIRED off"
}

test_pointer_table_required_opt_in_via_conf() {
  local slug rom; slug="$(unique_slug ptreloc_on)"; rom="${NESREV_TEST_TMPDIR}/rom.nes"
  make_ines "${rom}"; scaffold_project "${slug}" "${rom}"
  printf 'POINTER_TABLE_RELOCATION_REQUIRED="1"\n' >> "projects/${slug}/project.conf"
  local flag; flag="$(_load_flag "${slug}")"; cleanup_project "${slug}"
  assert_eq "1" "${flag}" "project.conf opt-in must enable the gate flag"
}
