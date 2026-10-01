#!/usr/bin/env bash
# Tests split low/high pointer inventories from xasm JSON xref version 2.

SPLIT_TARGETS="${REPO_ROOT}/scripts/split_pointer_targets.py"
SPLIT_TARGETS_CHECK="${REPO_ROOT}/scripts/split_pointer_targets_check.sh"

test_split_pointer_targets_preserves_entries_after_selector_rename() {
  local fixture="${NESREV_TEST_TMPDIR}/split.asm"
  cat > "${fixture}" <<'ASM'
.ORG $C000
ImagePtrLoTable:
  .DB <North,<South,<West,<East
ImagePtrHiTable:
  .DB >North,>South,>West,>East
MaskPtrLoTable:
  .DB <East,<West,<South,<North
MaskPtrHiTable:
  .DB >East,>West,>South,>North
North: .DB 1
South: .DB 2
West: .DB 3
East: .DB 4
ASM
  local form
  for form in table selector; do
    "${XASM_BIN:-$(command -v xasm)}" --pure-binary \
      --xref="${NESREV_TEST_TMPDIR}/${form}.json" --xref-format=json \
      --xref-data=true --xref-include-owner=true \
      -o "${NESREV_TEST_TMPDIR}/${form}.bin" "${fixture}"
    python3 "${SPLIT_TARGETS}" "${NESREV_TEST_TMPDIR}/${form}.json" \
      "${NESREV_TEST_TMPDIR}/${form}.csv"
    if [[ "${form}" == table ]]; then
      python3 - "${fixture}" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
path.write_text(path.read_text().replace("Table", "BySide"))
PY
    fi
  done
  cmp "${NESREV_TEST_TMPDIR}/table.bin" "${NESREV_TEST_TMPDIR}/selector.bin" \
    || fail "renaming split tables must preserve emitted bytes"
  python3 - "${NESREV_TEST_TMPDIR}" <<'PY'
import csv
import sys
from pathlib import Path

root = Path(sys.argv[1])
with (root / "table.csv").open() as source:
    before = list(csv.DictReader(source))
with (root / "selector.csv").open() as source:
    after = list(csv.DictReader(source))
assert len(before) == 8, before
assert len(after) == 8, f"selector rename lost split pointer targets: {after!r}"
for row in before:
    for field in ("lo_source", "hi_source"):
        row[field] = row[field].replace("Table", "BySide")
assert after == before, (before, after)
PY
  assert_exit 0 bash "${SPLIT_TARGETS_CHECK}" \
    "${NESREV_TEST_TMPDIR}/selector.json" "${NESREV_TEST_TMPDIR}/selector.csv"
  printf 'lo_source,hi_source,entry,target_label,target_type,confidence,notes\n' \
    > "${NESREV_TEST_TMPDIR}/missing.csv"
  assert_exit 67 bash "${SPLIT_TARGETS_CHECK}" \
    "${NESREV_TEST_TMPDIR}/selector.json" "${NESREV_TEST_TMPDIR}/missing.csv"
}

test_split_pointer_targets_selector_names_keep_validation() {
  python3 - "${REPO_ROOT}/scripts" <<'PY'
import sys
sys.path.insert(0, sys.argv[1])
from split_pointer_targets import inventory_rows

for low, high in (("PtrLo", "PtrHi"), ("PointerLo", "PointerHi"),
                  ("PtrLow", "PtrHigh"), ("LoPtr", "HiPtr"), ("LowPtr", "HighPtr")):
    lo, hi = f"Frame{low}ByVariant", f"Frame{high}ByVariant"
    payload = {"symbols": [
        {"name": name, "kind": "label", "scope": "global",
         "definition": {"file": "input.asm", "line": line, "output_offset": offset}}
        for name, line, offset in ((lo, 1, 0), (hi, 2, 1), ("End", 3, 2))
    ], "data_directive_references": [
        {"directive": ".DB", "width_bytes": 1, "owner_symbol": name,
         "owner_item_index": 0, "expression": expression,
         "target_projection": projection, "target_kind": "data"}
        for name, expression, projection in ((lo, "<Target", "low"), (hi, ">Target", "high"))
    ]}
    rows, errors = inventory_rows(payload)
    assert not errors and len(rows) == 1, (lo, rows, errors)
    high_record = payload["data_directive_references"][1]
    high_record["expression"] = ">OtherTarget"
    rows, errors = inventory_rows(payload)
    assert not rows and any("target mismatch" in error for error in errors), (lo, errors)
    high_record["expression"] = "<Target"
    high_record["target_projection"] = "low"
    rows, errors = inventory_rows(payload)
    assert not rows and any("must use symbolic >Target" in error for error in errors), (lo, errors)
    high_record["expression"] = ">Target"
    high_record["target_projection"] = "high"
    # A different selector is a different family, even when target bytes agree.
    high_record["owner_symbol"] = hi.replace("Variant", "Side")
    payload["symbols"][1]["name"] = high_record["owner_symbol"]
    rows, errors = inventory_rows(payload)
    assert not rows and not errors, (lo, rows, errors)
PY
}

test_split_pointer_targets_extracts_paired_tables() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets.json"
  local csv="${NESREV_TEST_TMPDIR}/split_pointer_targets.csv"

  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":3}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":6}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<DataTarget","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":1,"expression":"<CodeTarget","target_projection":"low","target_kind":"code"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":2,"expression":"<(DataTarget+3)","target_projection":"low","target_kind":"equate"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">DataTarget","target_projection":"high","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":1,"expression":">CodeTarget","target_projection":"high","target_kind":"code"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":2,"expression":">(DataTarget+3)","target_projection":"high","target_kind":"equate"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"GradientLoTable","owner_item_index":0,"expression":"GradientStart","target_kind":"data"}
]}
JSON

  python3 "${SPLIT_TARGETS}" "${xref}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
lo_source,hi_source,entry,target_label,target_type,confidence,notes
FramePtrLoTable,FramePtrHiTable,0,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive; split low/high table pair
FramePtrLoTable,FramePtrHiTable,1,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction; split low/high table pair
FramePtrLoTable,FramePtrHiTable,2,DataTarget+3,data_pointer,high confidence,auto-classified from target label leading data directive; split low/high table pair
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "split pointer inventory must preserve xasm owners, entry order, expressions, and target kinds"
}

test_split_pointer_targets_check_rejects_stale_registry() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_stale.json"
  local csv="${NESREV_TEST_TMPDIR}/split_pointer_targets.csv"

  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":1}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":2}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<DataTarget","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">DataTarget","target_projection":"high","target_kind":"data"}
]}
JSON
  printf 'lo_source,hi_source,entry,target_label,target_type,confidence,notes\n' > "${csv}"

  assert_exit 67 bash "${SPLIT_TARGETS_CHECK}" "${xref}" "${csv}"
}

test_split_pointer_targets_rejects_missing_symbolic_operand() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_gap.json"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":2}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":4}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<TargetA","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":2,"expression":"<TargetB","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">TargetA","target_projection":"high","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":1,"expression":">TargetB","target_projection":"high","target_kind":"data"}
]}
JSON

  local output rc
  set +e
  output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "xref gaps in named split tables must fail conservatively"
  assert_match "without a symbolic xref record" "${output}"
}

test_split_pointer_targets_rejects_trailing_unrecorded_byte() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_trailing.json"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":2}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":3}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<DataTarget","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">DataTarget","target_projection":"high","target_kind":"data"}
]}
JSON

  local output rc
  set +e
  output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "a trailing literal in a named split table must not disappear from xref validation"
  assert_match "body contains bytes without symbolic xref records" "${output}"
}

test_split_pointer_targets_ignores_unpaired_suffix_match() {
  local fixture="${NESREV_TEST_TMPDIR}/lone.asm"
  local xref="${NESREV_TEST_TMPDIR}/lone.json"
  local csv="${NESREV_TEST_TMPDIR}/lone.csv"
  local suffix half projection
  for suffix in Table ByFrame Bytes; do
    for half in Lo Hi; do
      projection='<'
      [[ "${half}" != Hi ]] || projection='>'
      printf '%s\n' '.ORG $C000' "SpritePtr${half}${suffix}:" \
        "  .DB ${projection}TargetA,${projection}TargetB,\$FF" \
        'TargetA: .DB 1' 'TargetB: .DB 2' > "${fixture}"
      "${XASM_BIN:-$(command -v xasm)}" --pure-binary \
        --xref="${xref}" --xref-format=json --xref-data=true --xref-include-owner=true \
        -o "${NESREV_TEST_TMPDIR}/lone.bin" "${fixture}"
      python3 "${SPLIT_TARGETS}" "${xref}" "${csv}"
      assert_eq "$(wc -l < "${csv}" | tr -d ' ')" "1" \
        "a lone ${half}${suffix} table must not require a fully symbolic body"
      assert_exit 0 bash "${SPLIT_TARGETS_CHECK}" "${xref}" "${csv}"
    done
  done
}

test_split_pointer_targets_requires_selector_word_boundary() {
  local fixture="${NESREV_TEST_TMPDIR}/suffix.asm"
  local xref="${NESREV_TEST_TMPDIR}/suffix.json"
  local csv="${NESREV_TEST_TMPDIR}/suffix.csv"
  local suffix expected
  for suffix in ByX By2Frames ByFrame_Index Byte Bytes Bypass By By_frame Byframe; do
    case "${suffix}" in
      ByX|By2Frames|ByFrame_Index) expected=3 ;;
      *) expected=1 ;;
    esac
    printf '%s\n' '.ORG $C000' "ScorePtrLo${suffix}:" \
      '  .DB <TargetA,<TargetB' "ScorePtrHi${suffix}:" \
      '  .DB >TargetA,>TargetB' 'TargetA: .DB 1' 'TargetB: .DB 2' > "${fixture}"
    "${XASM_BIN:-$(command -v xasm)}" --pure-binary \
      --xref="${xref}" --xref-format=json --xref-data=true --xref-include-owner=true \
      -o "${NESREV_TEST_TMPDIR}/suffix.bin" "${fixture}"
    python3 "${SPLIT_TARGETS}" "${xref}" "${csv}"
    assert_eq "$(wc -l < "${csv}" | tr -d ' ')" "${expected}" \
      "${suffix} must follow the By<index> naming boundary"
  done
}

test_split_pointer_targets_ignores_mixed_naming_families() {
  local fixture="${NESREV_TEST_TMPDIR}/mixed.asm"
  local xref="${NESREV_TEST_TMPDIR}/mixed.json"
  local csv="${NESREV_TEST_TMPDIR}/mixed.csv"
  local low high form
  for form in ending spelling; do
    low=FramePtrLoByX
    high=FramePointerHiByX
    if [[ "${form}" == ending ]]; then
      low=FramePtrLoTable
      high=FramePtrHiByX
    fi
    printf '%s\n' '.ORG $C000' "${low}:" '  .DB <TargetA,$FF' \
      "${high}:" '  .DB >TargetA,$FF' 'TargetA: .DB 1' > "${fixture}"
    "${XASM_BIN:-$(command -v xasm)}" --pure-binary \
      --xref="${xref}" --xref-format=json --xref-data=true --xref-include-owner=true \
      -o "${NESREV_TEST_TMPDIR}/mixed.bin" "${fixture}"
    python3 "${SPLIT_TARGETS}" "${xref}" "${csv}"
    assert_eq "$(wc -l < "${csv}" | tr -d ' ')" "1" \
      "mixed ${form} tables must not pair or validate each other's bodies"
  done
}

test_split_pointer_targets_ignores_literal_pairs_without_xrefs() {
  local fixture="${NESREV_TEST_TMPDIR}/literal.asm"
  local xref="${NESREV_TEST_TMPDIR}/literal.json"
  local csv="${NESREV_TEST_TMPDIR}/literal.csv"
  local suffix
  for suffix in Table ByX; do
    printf '%s\n' '.ORG $C000' "FramePtrLo${suffix}:" '  .DB $38,$52' \
      "FramePtrHi${suffix}:" '  .DB $04,$04' 'AfterTables: .DB 0' > "${fixture}"
    "${XASM_BIN:-$(command -v xasm)}" --pure-binary \
      --xref="${xref}" --xref-format=json --xref-data=true --xref-include-owner=true \
      -o "${NESREV_TEST_TMPDIR}/literal.bin" "${fixture}"
    python3 "${SPLIT_TARGETS}" "${xref}" "${csv}"
    assert_eq "$(wc -l < "${csv}" | tr -d ' ')" "1" \
      "literal ${suffix} pairs must remain outside the symbolic inventory"
  done
}

test_split_pointer_targets_selector_pairs_require_complete_bodies() {
  local fixture="${NESREV_TEST_TMPDIR}/complete.asm"
  local xref="${NESREV_TEST_TMPDIR}/complete.json"
  local low high scenario expected diagnostic output rc
  for scenario in count trailing gap literal_half; do
    low='<TargetA,<TargetB'
    high='>TargetA,>TargetB'
    expected=65
    case "${scenario}" in
      count) high='>TargetA'; expected=68; diagnostic='entry count mismatch' ;;
      trailing) low='<TargetA,$FF'; diagnostic='body contains bytes without symbolic xref records' ;;
      gap) low='$FF,<TargetB'; diagnostic='operand without a symbolic xref record' ;;
      literal_half) high='$C0,$C0'; diagnostic='has no symbolic xref records' ;;
    esac
    printf '%s\n' '.ORG $C000' 'FramePtrLoByX:' "  .DB ${low}" \
      'FramePtrHiByX:' "  .DB ${high}" 'TargetA: .DB 1' 'TargetB: .DB 2' > "${fixture}"
    "${XASM_BIN:-$(command -v xasm)}" --pure-binary \
      --xref="${xref}" --xref-format=json --xref-data=true --xref-include-owner=true \
      -o "${NESREV_TEST_TMPDIR}/complete.bin" "${fixture}"
    set +e
    output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
    rc=$?
    set -e
    assert_eq "${rc}" "${expected}" "${scenario} must fail for a By pair"
    assert_match "${diagnostic}" "${output}"
  done
}

test_split_pointer_targets_rejects_unequal_entry_counts() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_counts.json"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":2}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":3}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<TargetA","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":1,"expression":"<TargetB","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">TargetA","target_projection":"high","target_kind":"data"}
]}
JSON

  local output rc
  set +e
  output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "68" "unequal split pointer table lengths must fail"
  assert_match "entry count mismatch" "${output}"
}

test_split_pointer_targets_rejects_wrong_projection() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_projection.json"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":1}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":2}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"TargetA","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">TargetA","target_projection":"high","target_kind":"data"}
]}
JSON

  local output rc
  set +e
  output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "68" "split low tables must carry low-projection records"
  assert_match "must use symbolic <Target" "${output}"
}

test_split_pointer_targets_rejects_entry_target_mismatch() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_mismatch.json"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":1}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":2}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<TargetA","target_projection":"low","target_kind":"data"},
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">TargetB","target_projection":"high","target_kind":"data"}
]}
JSON

  local output rc
  set +e
  output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "68" "mismatched low/high split pointer entries must fail"
  assert_match "target mismatch" "${output}"
}

test_split_pointer_targets_rejects_incompatible_xref() {
  local xref="${NESREV_TEST_TMPDIR}/split_targets_v1.json"
  printf '{"version":"1","references":[]}\n' > "${xref}"

  local output rc
  set +e
  output="$(python3 "${SPLIT_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "split pointer inventory must require xref version 2"
  assert_match "xref schema version 2 required" "${output}"
}
