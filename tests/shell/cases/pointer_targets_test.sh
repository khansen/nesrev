#!/usr/bin/env bash
# Tests .DW inventory extraction from xasm JSON xref version 2.

POINTER_TARGETS="${REPO_ROOT}/scripts/pointer_targets.sh"

test_dw_entry_indexes_and_target_kinds_come_from_xref() {
  local xref="${NESREV_TEST_TMPDIR}/xref.json"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${xref}" <<'JSON'
{
  "version": "2",
  "data_directive_references": [
    {"directive":".DW","width_bytes":2,"expression":"CodeTarget","use_cpu_address":"0xC000","owner_symbol":"MixedPointerTable","owner_item_index":0,"target_kind":"code"},
    {"directive":".DW","width_bytes":2,"expression":"DataTarget","use_cpu_address":"0xC002","owner_symbol":"MixedPointerTable","owner_item_index":1,"target_kind":"data"},
    {"directive":".DW","width_bytes":2,"expression":"UnknownTarget","use_cpu_address":"0xC004","owner_symbol":"MixedPointerTable","owner_item_index":2},
    {"directive":".DB","width_bytes":1,"expression":"IgnoredByteTarget","use_cpu_address":"0xC006","owner_symbol":"MixedPointerTable","owner_item_index":0,"target_kind":"data"},
    {"directive":".DW","width_bytes":2,"expression":"CodeTarget+1","use_cpu_address":"0xC007","owner_symbol":"MixedPointerTable","owner_item_index":4,"target_kind":"code"},
    {"directive":".DW","width_bytes":2,"expression":"DataEquate","use_cpu_address":"0xC009","owner_symbol":"OtherPointerTable","owner_item_index":0,"target_kind":"equate"},
    {"directive":".DW","width_bytes":2,"expression":"CodeTarget","use_cpu_address":"0xC00B","owner_symbol":"OtherPointerTable","owner_item_index":1,"target_kind":"code"}
  ]
}
JSON

  bash "${POINTER_TARGETS}" "${xref}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
source,entry,target_label,target_type,confidence,notes
MixedPointerTable,0,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction
MixedPointerTable,1,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive
MixedPointerTable,2,UnknownTarget,unknown_pointer,inferred,auto-extracted from .DW entry (target kind unresolved)
MixedPointerTable,4,CodeTarget+1,code_pointer,high confidence,auto-classified from target label leading instruction
OtherPointerTable,0,DataEquate,data_pointer,high confidence,auto-classified from target label leading data directive
OtherPointerTable,1,CodeTarget,code_pointer,high confidence,auto-classified from target label leading instruction
CSV

  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "pointer inventory must preserve xasm owners, width-relative indexes, expressions, and target kinds"
}

test_cpu_vector_addresses_are_consumer_policy_exclusions() {
  local xref="${NESREV_TEST_TMPDIR}/vectors.json"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${xref}" <<'JSON'
{
  "version": "2",
  "data_directive_references": [
    {"directive":".DW","width_bytes":2,"expression":"NMI","use_cpu_address":"0xFFFA","owner_symbol":"MusicStream","owner_item_index":0,"target_kind":"code"},
    {"directive":".DW","width_bytes":2,"expression":"Reset","use_cpu_address":"0xFFFC","owner_symbol":"MusicStream","owner_item_index":1,"target_kind":"code"},
    {"directive":".DW","width_bytes":2,"expression":"IRQ","use_cpu_address":"0xFFFE","owner_symbol":"MusicStream","owner_item_index":2,"target_kind":"code"}
  ]
}
JSON

  bash "${POINTER_TARGETS}" "${xref}" "${csv}"

  printf 'source,entry,target_label,target_type,confidence,notes\n' \
    > "${NESREV_TEST_TMPDIR}/expected.csv"
  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "NES CPU vector words must stay outside pointer_targets.csv"
}

test_vector_exclusion_does_not_hide_adjacent_dw_table_entry() {
  local xref="${NESREV_TEST_TMPDIR}/adjacent-vectors.json"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${xref}" <<'JSON'
{
  "version": "2",
  "data_directive_references": [
    {"directive":".DW","width_bytes":2,"expression":"DataTarget","use_cpu_address":"0xFFF8","owner_symbol":"TerminalData","owner_item_index":0,"target_kind":"data"},
    {"directive":".DW","width_bytes":2,"expression":"NMI","use_cpu_address":"0xFFFA","owner_symbol":"TerminalData","owner_item_index":1,"target_kind":"code"},
    {"directive":".DW","width_bytes":2,"expression":"Reset","use_cpu_address":"0xFFFC","owner_symbol":"TerminalData","owner_item_index":2,"target_kind":"code"},
    {"directive":".DW","width_bytes":2,"expression":"IRQ","use_cpu_address":"0xFFFE","owner_symbol":"TerminalData","owner_item_index":3,"target_kind":"code"}
  ]
}
JSON

  bash "${POINTER_TARGETS}" "${xref}" "${csv}"

  cat > "${NESREV_TEST_TMPDIR}/expected.csv" <<'CSV'
source,entry,target_label,target_type,confidence,notes
TerminalData,0,DataTarget,data_pointer,high confidence,auto-classified from target label leading data directive
CSV
  cmp "${NESREV_TEST_TMPDIR}/expected.csv" "${csv}" \
    || fail "CPU vector exclusion must not suppress the adjacent table word"
}

test_unowned_dw_operand_is_not_assigned_a_guessed_source() {
  local xref="${NESREV_TEST_TMPDIR}/unowned.json"
  local csv="${NESREV_TEST_TMPDIR}/pointer_targets.csv"

  cat > "${xref}" <<'JSON'
{"version":"2","data_directive_references":[
  {"directive":".DW","width_bytes":2,"expression":"Target","use_cpu_address":"0xC000","owner_item_index":0,"target_kind":"code"}
]}
JSON

  bash "${POINTER_TARGETS}" "${xref}" "${csv}"
  assert_eq "$(wc -l < "${csv}" | tr -d ' ')" "1" \
    "an unowned xasm record must not borrow a neighbouring source label"
}

test_version_one_xref_fails_with_lockstep_contract_message() {
  local xref="${NESREV_TEST_TMPDIR}/v1.json"
  printf '{"version":"1","references":[]}\n' > "${xref}"

  local output rc
  set +e
  output="$(bash "${POINTER_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "the pointer inventory must reject pre-contract xref JSON"
  assert_match "xref schema version 2 required" "${output}"
}

test_malformed_owner_index_fails_instead_of_becoming_zero() {
  local xref="${NESREV_TEST_TMPDIR}/bad-index.json"
  cat > "${xref}" <<'JSON'
{"version":"2","data_directive_references":[
  {"directive":".DW","width_bytes":2,"expression":"Target","use_cpu_address":"0xC000","owner_symbol":"Table","owner_item_index":true,"target_kind":"code"}
]}
JSON

  local output rc
  set +e
  output="$(bash "${POINTER_TARGETS}" "${xref}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "boolean owner indexes must not pass Python's integer subtype check"
  assert_match "owner_item_index must be int" "${output}"
}
