#!/usr/bin/env bash
# Tests for mechanically checkable `; Used by:` xref validation.

USED_BY_CHECK="${REPO_ROOT}/scripts/used_by_xref_check.py"

_make_used_by_docs_project() {
  local slug="$1"
  local root="projects/${slug}"

  cleanup_project "${slug}"
  mkdir -p \
    "${root}/asm" \
    "${root}/build" \
    "${root}/reference" \
    "${root}/docs/reverse_engineering/inventory"

  cat > "${root}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="${root}/asm/${slug}.asm"
REF_NES="${root}/reference/${slug}.nes"
DOC_ROOT="${root}/docs/reverse_engineering"
SYSTEMS_DOC="${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
NESREV_RECOVERY_STATUS="none"
OUT_BIN="${root}/build/${slug}.o"
EOF

  cat > "${root}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: FakeMissingConsumer.
DataTable:
.DB $01
ASM

  : > "${root}/reference/${slug}.nes"
  : > "${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
  : > "${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
  : > "${root}/docs/reverse_engineering/ONBOARDING.md"
  : > "${root}/docs/reverse_engineering/QUICK_REFERENCE.md"
  printf 'old_name,new_name,reason,confidence,pass_id\n' \
    > "${root}/docs/reverse_engineering/inventory/renames.csv"
}

test_used_by_xref_check_accepts_direct_data_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_direct.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader.
DataTable:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" --generate-xref --strict "${asm}" >/dev/null
}

test_used_by_xref_check_accepts_direct_claim_through_derived_equ() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_derived_equ.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
BaseTable:
.DB $00

; Format: one byte.
; Used by: Reader.
DataTable:
.DB $01

DATA_TABLE_CURSOR .EQU (DataTable-BaseTable)
Reader:
  LDX #DATA_TABLE_CURSOR
  RTS
ASM

  python3 "${USED_BY_CHECK}" --generate-xref --strict "${asm}" >/dev/null
}

test_used_by_xref_check_rejects_stale_direct_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_stale.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS
OtherReader:
  RTS

; Format: one byte.
; Used by: OtherReader.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --generate-xref --strict "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "stale Used by comment must fail"
  assert_match "OtherReader" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_reports_owner_mismatch_advisory_without_strict() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_advisory.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS
OtherReader:
  RTS

; Format: one byte.
; Used by: OtherReader.
DataTable:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" --generate-xref "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"

  assert_match "Used by hard-error scan passed" "$(cat "${NESREV_TEST_TMPDIR}/used_by.out")"
  assert_match "ADVISORY: Used by xref" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
  assert_match "OtherReader" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_reports_missing_xasm_cleanly() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_missing_xasm.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader.
DataTable:
.DB $01
ASM

  set +e
  XASM_BIN="${NESREV_TEST_TMPDIR}/missing-xasm" \
    python3 "${USED_BY_CHECK}" --generate-xref "${asm}" \
    >"${NESREV_TEST_TMPDIR}/used_by.out" \
    2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "66" "missing xasm must return a stable error code"
  assert_match "xasm not found" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_splits_and_case_insensitively() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_upper_and.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader AND FakeMissingConsumer.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --generate-xref "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "uppercase AND must still split Used by consumer symbols"
  assert_match "FakeMissingConsumer" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_accepts_consumer_through_pointer_table() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_indirect.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA PtrTable
  RTS

; Format: pointer table.
; Used by: Reader.
PtrTable:
.DW Payload

; Format: payload bytes.
; Used by: Reader through PtrTable.
Payload:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" --generate-xref "${asm}" >/dev/null
}

test_used_by_xref_check_accepts_direct_claim_via_symbolic_pointer_table() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_table_transitive.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
ProcessRequest:
  LDX RequestPointerTable,Y
  LDA RequestPointerTable+1,Y
  RTS

RequestPointerTable:
.DW Payload

; Format: payload bytes.
; Used by: ProcessRequest.
Payload:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" --generate-xref --strict "${asm}" >/dev/null
}

test_used_by_xref_check_uses_data_owner_for_pointer_table_edge() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_xref_graph.asm"
  local xref="${NESREV_TEST_TMPDIR}/used_by_xref_graph.json"
  cat > "${asm}" <<'ASM'
.ORG $C000
ProcessRequest:
  LDX RequestPointerTable,Y
  RTS
PriorRoutine:
  RTS

RequestPointerTable:
.DW Payload

; Format: payload bytes.
; Used by: ProcessRequest.
Payload:
.DB $01
ASM
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"ProcessRequest"},
  {"name":"PriorRoutine"},
  {"name":"RequestPointerTable"},
  {"name":"Payload"}
],"references":[
  {"symbol":"RequestPointerTable","owner_routine":"ProcessRequest"},
  {"symbol":"Payload","owner_routine":"PriorRoutine"}
],"data_reads":[],"data_writes":[],"data_directive_references":[
  {"owner_symbol":"RequestPointerTable","referenced_symbols":["Payload"]}
]}
JSON

  XASM_BIN=/usr/bin/false \
    python3 "${USED_BY_CHECK}" --strict "${asm}" "${xref}" >/dev/null
}

test_used_by_xref_check_does_not_reconstruct_pointer_edges_from_source() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_no_source_graph.asm"
  local xref="${NESREV_TEST_TMPDIR}/used_by_no_source_graph.json"
  cat > "${asm}" <<'ASM'
.ORG $C000
ProcessRequest:
  LDX RequestPointerTable,Y
  RTS

RequestPointerTable:
.DW Payload

; Format: payload bytes.
; Used by: ProcessRequest.
Payload:
.DB $01
ASM
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"ProcessRequest"},
  {"name":"RequestPointerTable"},
  {"name":"Payload"}
],"references":[],"data_reads":[],"data_writes":[],
"data_directive_references":[
  {"owner_symbol":"RequestPointerTable","referenced_symbols":["Payload"]}
]}
JSON

  set +e
  XASM_BIN=/usr/bin/false \
    python3 "${USED_BY_CHECK}" --strict "${asm}" "${xref}" \
      >"${NESREV_TEST_TMPDIR}/no_source_graph.out" \
      2>"${NESREV_TEST_TMPDIR}/no_source_graph.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "source text must not supply a missing xref edge"
  assert_match "xref owners are: none" "$(cat "${NESREV_TEST_TMPDIR}/no_source_graph.err")"
}

test_used_by_xref_check_rejects_arbitrary_two_hop_xref_path() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_arbitrary_hop.asm"
  local xref="${NESREV_TEST_TMPDIR}/used_by_arbitrary_hop.json"
  cat > "${asm}" <<'ASM'
.ORG $C000
ProcessRequest:
  LDA HelperData
  RTS

HelperData:
.DW Payload

; Format: payload bytes.
; Used by: ProcessRequest.
Payload:
.DB $01
ASM
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"ProcessRequest"},
  {"name":"HelperData"},
  {"name":"Payload"}
],"references":[
  {"symbol":"HelperData","owner_routine":"ProcessRequest"}
],"data_reads":[],"data_writes":[],"data_directive_references":[
  {"owner_symbol":"HelperData","referenced_symbols":["Payload"]}
]}
JSON

  set +e
  XASM_BIN=/usr/bin/false \
    python3 "${USED_BY_CHECK}" --strict "${asm}" "${xref}" \
      >"${NESREV_TEST_TMPDIR}/arbitrary_hop.out" \
      2>"${NESREV_TEST_TMPDIR}/arbitrary_hop.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "an arbitrary two-hop xref path must not prove a consumer"
  assert_match "xref owners are: none" "$(cat "${NESREV_TEST_TMPDIR}/arbitrary_hop.err")"
}

test_used_by_xref_check_requires_explicit_standalone_generation() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_explicit_fallback.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS
ASM

  set +e
  python3 "${USED_BY_CHECK}" "${asm}" \
    >"${NESREV_TEST_TMPDIR}/explicit_fallback.out" \
    2>"${NESREV_TEST_TMPDIR}/explicit_fallback.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "64" "standalone xref generation must require an explicit flag"
  assert_match "--generate-xref" "$(cat "${NESREV_TEST_TMPDIR}/explicit_fallback.err")"
}

test_used_by_xref_check_rejects_incompatible_shared_xref() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_v1.asm"
  local xref="${NESREV_TEST_TMPDIR}/used_by_v1.json"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS
ASM
  cat > "${xref}" <<'JSON'
{"version":"1","symbols":[],"references":[]}
JSON

  set +e
  XASM_BIN=/usr/bin/false \
    python3 "${USED_BY_CHECK}" "${asm}" "${xref}" \
      >"${NESREV_TEST_TMPDIR}/used_by_v1.out" \
      2>"${NESREV_TEST_TMPDIR}/used_by_v1.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "65" "Used by validation must reject an incompatible shared xref"
  assert_match "xref schema version 2 required" "$(cat "${NESREV_TEST_TMPDIR}/used_by_v1.err")"
}

test_used_by_xref_check_rejects_malformed_data_reference_symbols() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_bad_data_refs.asm"
  local xref="${NESREV_TEST_TMPDIR}/used_by_bad_data_refs.json"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS
ASM
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[{"name":"Reader"}],"references":[],
"data_reads":[],"data_writes":[],"data_directive_references":[
  {"owner_symbol":"Table","referenced_symbols":"Target"}
]}
JSON

  set +e
  XASM_BIN=/usr/bin/false \
    python3 "${USED_BY_CHECK}" "${asm}" "${xref}" \
      >"${NESREV_TEST_TMPDIR}/bad_data_refs.out" \
      2>"${NESREV_TEST_TMPDIR}/bad_data_refs.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "65" "malformed data-reference symbol arrays must fail"
  assert_match "referenced_symbols must be list\[str\]" "$(cat "${NESREV_TEST_TMPDIR}/bad_data_refs.err")"
}

test_used_by_xref_check_rejects_stale_shared_xref() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_stale_xref.asm"
  local xref="${NESREV_TEST_TMPDIR}/used_by_stale_xref.json"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[],"references":[],"data_reads":[],
"data_writes":[],"data_directive_references":[]}
JSON
  touch -t 200001010000 "${xref}"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS
ASM

  set +e
  XASM_BIN=/usr/bin/false \
    python3 "${USED_BY_CHECK}" "${asm}" "${xref}" \
      >"${NESREV_TEST_TMPDIR}/stale_xref.out" \
      2>"${NESREV_TEST_TMPDIR}/stale_xref.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "65" "stale shared xref must fail instead of assembling silently"
  assert_match "xref file is older than asm" "$(cat "${NESREV_TEST_TMPDIR}/stale_xref.err")"
}

test_used_by_xref_check_rejects_unconnected_consumer_despite_pointer_table() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_table_unconnected.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
ActualReader:
  LDX RequestPointerTable,Y
  RTS

RequestPointerTable:
.DW Payload

OtherReader:
  RTS

; Format: payload bytes.
; Used by: OtherReader.
Payload:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --generate-xref --strict "${asm}" \
    >"${NESREV_TEST_TMPDIR}/table_unconnected.out" \
    2>"${NESREV_TEST_TMPDIR}/table_unconnected.err"
  local rc=$?
  set -e
  assert_eq "${rc}" "2" "an unrelated consumer must remain a stale claim"
  assert_match "OtherReader" "$(cat "${NESREV_TEST_TMPDIR}/table_unconnected.err")"
}

test_used_by_xref_check_through_producer_advisory_unless_strict() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_indirect_stale.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA PtrTable
  RTS

; Format: pointer table.
; Used by: Reader.
PtrTable:
.DW OtherPayload

; Format: payload bytes.
; Used by: Reader through PtrTable.
Payload:
.DB $01

OtherPayload:
.DB $02
ASM

  # Non-strict: a through/via producer with no proven target edge may still
  # reach it through runtime dispatch, so the mismatch remains advisory.
  set +e
  python3 "${USED_BY_CHECK}" --generate-xref "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "through-producer must be advisory (not hard) without --strict"
  assert_match "ADVISORY" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
  assert_match "PtrTable does not reference Payload" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"

  # --strict opt-in still enforces it as a hard failure.
  set +e
  python3 "${USED_BY_CHECK}" --generate-xref --strict "${asm}" >"${NESREV_TEST_TMPDIR}/used_by_s.out" 2>"${NESREV_TEST_TMPDIR}/used_by_s.err"
  local rc_strict=$?
  set -e
  assert_eq "${rc_strict}" "2" "through-producer must hard-fail under --strict"
  assert_match "PtrTable does not reference Payload" "$(cat "${NESREV_TEST_TMPDIR}/used_by_s.err")"
}

test_used_by_xref_check_rejects_unresolved_consumer_label() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_unresolved_label.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
L1234:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: L1234.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --generate-xref "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "Used by comments must not cite unresolved LXXXX labels"
  assert_match "unresolved consumer label L1234" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_rejects_prg_banking_without_consumer_symbol() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_banking.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS

; Format: one byte.
; Used by: selected through MMC1 PRG banking.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --generate-xref "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "generic MMC1 banking Used by comment must fail"
  assert_match "PRG banking" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_project_docs_check_hard_fails_unknown_used_by_consumer() {
  local slug; slug="$(unique_slug used_by_docs_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_used_by_docs_project "${slug}"

  set +e
  make project-docs-check "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/docs.out" 2>"${NESREV_TEST_TMPDIR}/docs.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "project-docs-check must hard-fail stale Used by comments"
  assert_match "FakeMissingConsumer" "$(cat "${NESREV_TEST_TMPDIR}/docs.err")"
}

test_project_docs_check_reuses_shared_xref_for_used_by_validation() {
  local slug; slug="$(unique_slug used_by_docs_shared)"
  local xref="${NESREV_TEST_TMPDIR}/used_by_docs_shared.json"
  trap "cleanup_project ${slug}" EXIT
  _make_used_by_docs_project "${slug}"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"Reader"},
  {"name":"DataTable"}
],"references":[
  {"symbol":"DataTable","owner_routine":"Reader"}
],"data_reads":[],"data_writes":[],"data_directive_references":[]}
JSON

  set +e
  NESREV_XREF_FILE="${xref}" XASM_BIN=/usr/bin/false \
    make project-docs-check "PROJECT=${slug}" \
      >"${NESREV_TEST_TMPDIR}/docs_shared.out" \
      2>"${NESREV_TEST_TMPDIR}/docs_shared.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "shared xref must reach Used by validation without another assembly"
  assert_match "FakeMissingConsumer" "$(cat "${NESREV_TEST_TMPDIR}/docs_shared.err")"
}
