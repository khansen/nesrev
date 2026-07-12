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

test_embedded_pointer_audit_uses_last_prg_bank_as_fixed_window() {
  python3 - "${EMBEDDED_AUDIT}" <<'PY'
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("embedded_pointer_audit", sys.argv[1])
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

banked = {0: (0x8000, 0xBFFF), 1: (0x8000, 0xBFFF), 2: (0x8000, 0xBFFF), 3: (0xC000, 0xFFFF)}
if not mod.in_same_window(3, 0xC000, banked, 3):
    raise SystemExit("fixed bank should own its $C000-$FFFF window")
if mod.in_same_window(3, 0x8000, banked, 3):
    raise SystemExit("fixed bank should not own the $8000 switchable window")
if not mod.in_same_window(2, 0x8000, banked, 3):
    raise SystemExit("switchable bank should own its $8000 window")
if not mod.in_same_window(2, 0xC000, banked, 3):
    raise SystemExit("switchable bank should reach the shared fixed window")

# NROM-128 assembled at $C000: the $8000-$BFFF mirror must be rejected.
nrom = {0: (0xC000, 0xFFFF)}
if not mod.in_same_window(0, 0xC000, nrom, 0):
    raise SystemExit("NROM-128 rom window $C000-$FFFF should be in-window")
if mod.in_same_window(0, 0x8125, nrom, 0):
    raise SystemExit("NROM-128 $8000 mirror must not be treated as a valid target")
PY
}

test_embedded_pointer_audit_derives_windows_and_aliases_generically() {
  python3 - "${EMBEDDED_AUDIT}" <<'PY'
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("embedded_pointer_audit", sys.argv[1])
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

# Windows are derived from assembled .ORG spans, not hardcoded per mapper.
records = [
    {"output_offset_start": 0, "cpu_address_start": "0xC000"},
    {"output_offset_start": 0x1000, "cpu_address_start": "0xD000"},
    {"output_offset_start": 0x3FFF, "cpu_address_start": "0xFFFF"},
]
windows = mod.compute_bank_windows(records)
if windows.get(0) != (0xC000, 0xFFFF):
    raise SystemExit(f"expected NROM-128 window (0xC000, 0xFFFF), got {windows.get(0)}")

# EQU aliases are read from the asm; a consumer reading via the alias still
# resolves to the owner label.
aliases = mod.build_equ_aliases(["Foo .EQU FooBank1", "Bar .EQU Baz"])
if aliases.get("Foo") != "FooBank1":
    raise SystemExit("alias map should map Foo -> FooBank1")
if "Foo" not in mod.names_for_owner("FooBank1", aliases):
    raise SystemExit("owner FooBank1 should include its alias Foo")
PY
}

test_embedded_pointer_audit_confirms_struct_block_end_to_end() {
  # A non-monotonic pointer struct copied into ZP and dereferenced must fail;
  # the identical struct without a runtime dereference must not.
  local asm="${NESREV_TEST_TMPDIR}/struct_block.asm"
  cat > "${asm}" <<'ASM'
ZP_StructBase .EQU $10
.ORG $8000
CopyStruct:
  LDX #$0B
@@loop:
  LDA StructBlock,X
  STA ZP_StructBase,X
  DEX
  BPL @@loop
Reader:
  LDY #$00
  LDA [ZP_StructBase],Y
  RTS
StructBlock: .DB $40,$80,$00,$81,$80,$80,$C0,$80,$40,$81,$00,$80
ASM
  assert_exit 68 python3 "${EMBEDDED_AUDIT}" "${asm}"

  local noderef="${NESREV_TEST_TMPDIR}/struct_block_noderef.asm"
  sed 's/  LDA \[ZP_StructBase\],Y/  ; no deref/' "${asm}" > "${noderef}"
  assert_exit 0 python3 "${EMBEDDED_AUDIT}" "${noderef}"
}

test_embedded_pointer_audit_confirms_nonmonotonic_pointer_struct() {
  python3 - "${EMBEDDED_AUDIT}" <<'PY'
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("embedded_pointer_audit", sys.argv[1])
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

# A struct of pointers to different tables is not sorted; the monotonic scan
# skips it. Non-monotonic in-window pairs form a candidate...
label_by_bank_cpu = {(0, 0x8500): "TableA", (0, 0x8700): "TableB", (0, 0x8400): "StructBlock"}
windows = {0: (0x8000, 0xBFFF)}
span = {
    "bank": 0,
    "labels": [(0x10, "StructBlock")],
    # bytes: (offset, cpu, value); pointers $8700 then $8500 (descending = non-monotonic)
    "bytes": [
        (0x10, 0x8400, 0x00), (0x11, 0x8401, 0x87),
        (0x12, 0x8402, 0x00), (0x13, 0x8403, 0x85),
        (0x14, 0x8404, 0x00), (0x15, 0x8405, 0x87),
        (0x16, 0x8406, 0x00), (0x17, 0x8407, 0x85),
        (0x18, 0x8408, 0x00), (0x19, 0x8409, 0x87),
        (0x1A, 0x840A, 0x00), (0x1B, 0x840B, 0x85),
    ],
}
structs = mod.find_pointer_struct_runs([span], label_by_bank_cpu, windows, 0, 6, [])
if not any(h["owner"] == "StructBlock" for h in structs):
    raise SystemExit("non-monotonic in-window pointer struct should be a candidate")

# ...and it confirms when the block is copied to a ZP base that is dereferenced,
# including when the copy reads through an .EQU alias.
asm_lines = [
    "CopyBlock:",
    "  LDA StructAlias,X",
    "  STA ZP_StructBase,X",
    "  RTS",
    "Reader:",
    "  LDA [ZP_StructBase],Y",
    "  RTS",
]
aliases = {"StructAlias": "StructBlock"}
proof = mod.struct_copy_deref_proof(asm_lines, "StructBlock", 0x8400, aliases)
if not proof:
    raise SystemExit("struct copied via alias to a dereferenced ZP base should confirm")
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
