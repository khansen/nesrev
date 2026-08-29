#!/usr/bin/env bash
# Tests split low/high pointer inventories from xasm JSON xref version 2.

SPLIT_TARGETS="${REPO_ROOT}/scripts/split_pointer_targets.py"
SPLIT_TARGETS_CHECK="${REPO_ROOT}/scripts/split_pointer_targets_check.sh"

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
  local xref="${NESREV_TEST_TMPDIR}/split_targets_missing.json"
  local csv="${NESREV_TEST_TMPDIR}/split_targets_missing.csv"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"AfterTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":1}}
],"data_directive_references":[
  {"directive":".DB","width_bytes":1,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<DataTarget","target_projection":"low","target_kind":"data"}
]}
JSON

  python3 "${SPLIT_TARGETS}" "${xref}" "${csv}"
  assert_eq "$(wc -l < "${csv}" | tr -d ' ')" "1" \
    "a lone low-byte table may use a constant high byte outside the inventory"
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
