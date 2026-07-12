#!/usr/bin/env bash
# Tests embedded pointer target inventories and raw .DB pointer auditing.

EMBEDDED_TARGETS="${REPO_ROOT}/scripts/embedded_pointer_targets.py"
EMBEDDED_TARGETS_CHECK="${REPO_ROOT}/scripts/embedded_pointer_targets_check.sh"
EMBEDDED_AUDIT="${REPO_ROOT}/scripts/embedded_pointer_audit.py"

test_embedded_pointer_audit_parse_int_accepts_xasm_address_formats() {
  python3 - "${EMBEDDED_AUDIT}" <<'PY'
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("embedded_pointer_audit", sys.argv[1])
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

cases = {
    "$C000": 0xC000,
    "0xC000": 0xC000,
    "C000": 0xC000,
    "8000": 0x8000,
    "49152": 49152,
}
for raw, expected in cases.items():
    actual = mod.parse_int(raw)
    if actual != expected:
        raise SystemExit(f"{raw}: expected {expected}, got {actual}")
PY
}

test_embedded_pointer_targets_extracts_db_low_high_pairs() {
  local asm="${NESREV_TEST_TMPDIR}/embedded_targets.asm"
  local csv="${NESREV_TEST_TMPDIR}/embedded_pointer_targets.csv"

  cat > "${asm}" <<'ASM'
CodeTarget:
  RTS

DataTarget:
  .DB $00

DispatchRecord:
  .DB <DataTarget,>DataTarget,<CodeTarget,>CodeTarget,$04
  .DB <(DataTarget+3),>(DataTarget+3),$00
ASM

  python3 "${EMBEDDED_TARGETS}" "${asm}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
source,entry,target_label,target_type,confidence,notes
DispatchRecord,0,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive
DispatchRecord,1,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction
DispatchRecord,2,DataTarget+3,data_pointer,high confidence,auto-classified from target label leading data directive
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "embedded pointer target extractor must preserve source-relative entries and classify target kinds"
}

test_embedded_pointer_targets_check_rejects_stale_registry() {
  local asm="${NESREV_TEST_TMPDIR}/embedded_targets_stale.asm"
  local csv="${NESREV_TEST_TMPDIR}/embedded_pointer_targets.csv"

  cat > "${asm}" <<'ASM'
DataTarget:
  .DB $00

DispatchRecord:
  .DB <DataTarget,>DataTarget
ASM

  cat > "${csv}" <<'CSV'
source,entry,target_label,target_type,confidence,notes
CSV

  assert_exit 67 bash "${EMBEDDED_TARGETS_CHECK}" "${asm}" "${csv}"
}

test_embedded_pointer_audit_fails_confirmed_raw_pointer_table() {
  local asm="${NESREV_TEST_TMPDIR}/raw_pointer_table.asm"

  cat > "${asm}" <<'ASM'
ZP_TestPtrLo .EQU $00
ZP_TestPtrHi .EQU $01

.ORG $8000
LoadRawPointer:
  LDY #$00
  LDA RawPointerTable,Y
  STA ZP_TestPtrLo
  LDA RawPointerTable+1,Y
  STA ZP_TestPtrHi
  LDA [ZP_TestPtrLo],Y
  RTS

RawPointerTable: .DB $40,$80,$42,$80,$44,$80,$46,$80,$48,$80,$4A,$80

.ORG $8040
TargetData:
  .DB $AA,$BB,$CC
ASM

  assert_exit 68 python3 "${EMBEDDED_AUDIT}" "${asm}"
}

test_embedded_pointer_audit_ignores_monotonic_data_without_pointer_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/raw_monotonic_data.asm"

  cat > "${asm}" <<'ASM'
.ORG $8000
RawGraphicsLikeData:
  .DB $40,$80,$42,$80,$44,$80,$46,$80,$48,$80,$4A,$80

Reader:
  LDY #$00
  LDA RawGraphicsLikeData,Y
  RTS
ASM

  python3 "${EMBEDDED_AUDIT}" "${asm}" > "${NESREV_TEST_TMPDIR}/audit.out"
  assert_match "embedded_pointer_raw_runs_strong=1" "$(<"${NESREV_TEST_TMPDIR}/audit.out")" \
    "monotonic data should still be visible as an advisory strong run"
  assert_match "embedded_pointer_confirmed_unrelocated=0" "$(<"${NESREV_TEST_TMPDIR}/audit.out")" \
    "monotonic data without paired-read pointer proof must not fail"
}

test_embedded_pointer_audit_ignores_comment_only_deref() {
  local asm="${NESREV_TEST_TMPDIR}/raw_pointer_comment_deref.asm"

  cat > "${asm}" <<'ASM'
ZP_TestPtrLo .EQU $00
ZP_TestPtrHi .EQU $01

.ORG $8000
LoadRawPointer:
  LDY #$00
  LDA RawPointerTable,Y
  STA ZP_TestPtrLo
  LDA RawPointerTable+1,Y
  STA ZP_TestPtrHi
  ; No runtime dereference here: LDA [ZP_TestPtrLo],Y
  RTS

RawPointerTable: .DB $40,$80,$42,$80,$44,$80,$46,$80,$48,$80,$4A,$80

.ORG $8040
TargetData:
  .DB $AA,$BB,$CC
ASM

  python3 "${EMBEDDED_AUDIT}" "${asm}" >"${NESREV_TEST_TMPDIR}/audit.out"
  assert_match "embedded_pointer_raw_runs_strong=1" "$(<"${NESREV_TEST_TMPDIR}/audit.out")" \
    "comment-only deref fixture should still surface the strong raw run"
  assert_match "embedded_pointer_confirmed_unrelocated=0" "$(<"${NESREV_TEST_TMPDIR}/audit.out")" \
    "comment-only deref text must not confirm an embedded pointer table"
}

test_embedded_pointer_audit_reports_xasm_diagnostics() {
  local asm="${NESREV_TEST_TMPDIR}/raw_pointer_bad_asm.asm"

  cat > "${asm}" <<'ASM'
.ORG $8000
Broken:
  LDA MissingLabel
  RTS
ASM

  set +e
  python3 "${EMBEDDED_AUDIT}" "${asm}" \
    >"${NESREV_TEST_TMPDIR}/audit_bad.out" \
    2>"${NESREV_TEST_TMPDIR}/audit_bad.err"
  local rc=$?
  set -e

  if [[ "${rc}" == "0" ]]; then
    fail "embedded pointer audit must fail when xasm fails"
  fi
  assert_match "error: xasm analysis failed" "$(cat "${NESREV_TEST_TMPDIR}/audit_bad.err")"
  assert_match "MissingLabel" "$(cat "${NESREV_TEST_TMPDIR}/audit_bad.err")"
}
