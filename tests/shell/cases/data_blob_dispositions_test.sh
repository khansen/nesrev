#!/usr/bin/env bash
# Tests the per-label data-blob disposition checker.

DATA_BLOB_CHECK="${REPO_ROOT}/scripts/data_blob_dispositions_check.py"

_write_blob_header() {
  local path="$1"
  cat > "${path}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
CSV
}

_write_blob_coverage() {
  local path="$1"
  cat > "${path}" <<'JSON'
[
  {
    "label": "RoomBlobPayload",
    "declared_size": 32,
    "uncovered_size": 32,
    "access_count": 0,
    "has_indexed_accesses_without_exact_coverage": false
  },
  {
    "label": "TinyPadding",
    "declared_size": 4,
    "uncovered_size": 4,
    "access_count": 0,
    "has_indexed_accesses_without_exact_coverage": false
  },
  {
    "label": "RoomBlobPayloadEnd",
    "declared_size": 48,
    "uncovered_size": 48,
    "access_count": 0,
    "has_indexed_accesses_without_exact_coverage": false
  }
]
JSON
}

test_data_blob_dispositions_process_warns_for_missing_candidates() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local coverage="${NESREV_TEST_TMPDIR}/data_coverage.json"
  mkdir -p "${doc_root}"
  _write_blob_header "${inv}"
  _write_blob_coverage "${coverage}"

  assert_exit 0 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --data-coverage "${coverage}" --mode process --required
}

test_data_blob_dispositions_maturity_rejects_missing_candidates() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local coverage="${NESREV_TEST_TMPDIR}/data_coverage.json"
  mkdir -p "${doc_root}"
  _write_blob_header "${inv}"
  _write_blob_coverage "${coverage}"

  assert_exit 1 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --data-coverage "${coverage}" --mode maturity --required
}

test_data_blob_dispositions_maturity_accepts_reviewed_candidate() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local coverage="${NESREV_TEST_TMPDIR}/data_coverage.json"
  mkdir -p "${doc_root}"
  printf '# Room Format\n' > "${doc_root}/ROOM_FORMAT.md"
  _write_blob_coverage "${coverage}"
  cat > "${inv}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
RoomBlobPayload,record_table,room_record,ROOM_FORMAT.md,Room loader walks 4-byte records,No raw little-endian ROM pointer pairs found in the span,data_extent_assertions.csv pins the 32-byte extent,reflowed,rows are one room record each
CSV

  assert_exit 0 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --data-coverage "${coverage}" --mode maturity --required
}

test_data_blob_dispositions_maturity_accepts_label_pattern() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local coverage="${NESREV_TEST_TMPDIR}/data_coverage.json"
  mkdir -p "${doc_root}"
  printf '# Room Format\n' > "${doc_root}/ROOM_FORMAT.md"
  _write_blob_coverage "${coverage}"
  cat > "${inv}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
RoomBlob*,record_table,room_record,ROOM_FORMAT.md,Room loader walks 4-byte records,No raw little-endian ROM pointer pairs found in the span,data_extent_assertions.csv pins the 32-byte extent,reflowed,pattern covers repeated same-format room blobs
CSV

  assert_exit 0 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --data-coverage "${coverage}" --mode maturity --required
}

test_data_blob_dispositions_maturity_rejects_pending_rows() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  mkdir -p "${doc_root}"
  cat > "${inv}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
RoomBlobPayload,queued_static_pass,,,,,,blocked_unknown_format,needs a data-flow pass
CSV

  assert_exit 1 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode maturity --required
}

test_data_blob_dispositions_requires_structural_evidence() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  mkdir -p "${doc_root}"
  printf '# Room Format\n' > "${doc_root}/ROOM_FORMAT.md"
  cat > "${inv}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
RoomBlobPayload,record_table,room_record,ROOM_FORMAT.md,,,data_extent_assertions.csv pins the extent,reflowed,missing consumer and pointer evidence
CSV

  assert_exit 1 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode process
}

test_data_blob_dispositions_rejects_unquoted_commas() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  mkdir -p "${doc_root}"
  cat > "${inv}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
RoomBlobPayload,known_unreferenced,,,no static consumer,none found,extent checked,not_applicable,note with, comma
CSV

  assert_exit 1 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode process
}

test_data_blob_dispositions_ignores_stale_cached_label_missing_from_asm() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local coverage="${NESREV_TEST_TMPDIR}/data_coverage.json"
  local asm="${NESREV_TEST_TMPDIR}/current.asm"
  mkdir -p "${doc_root}"
  _write_blob_header "${inv}"
  cat > "${coverage}" <<'JSON'
[{"label":"FormerRoomBlobPayload","declared_size":32,"uncovered_size":32,"access_count":0}]
JSON
  cat > "${asm}" <<'ASM'
CurrentRoomData:
    .DB $00
ASM

  local output
  output="$(python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --data-coverage "${coverage}" \
    --asm "${asm}" --mode process --required 2>&1)"
  if [[ "${output}" == *"FormerRoomBlobPayload"* ]]; then
    fail "a cached label absent from current asm must not remain a blob candidate: ${output}"
  fi
  assert_match "candidate_spans=0" "${output}" \
    "stale cached labels should be filtered against current asm globals"
}

test_data_blob_dispositions_closeout_rejects_current_pass_formatted_rename_without_row() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local renames="${NESREV_TEST_TMPDIR}/renames.csv"
  local asm="${NESREV_TEST_TMPDIR}/current.asm"
  mkdir -p "${doc_root}"
  _write_blob_header "${inv}"
  cat > "${renames}" <<'CSV'
old_name,new_name,reason,confidence,pass_id
L8123,SmallOamTemplate,two OAM records,high,2
L9000,CodeRoutine,code owner,high,2
CSV
  cat > "${asm}" <<'ASM'
; Format: two 4-byte OAM records [y, tile, attributes, x].
SmallOamTemplate:
    .DB $10,$20,$00,$30
    .DB $18,$21,$00,$38

CodeRoutine:
; Format: A contains a packed request token on entry.
    LDA #$00
    RTS
ASM

  assert_exit 1 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --asm "${asm}" \
    --renames "${renames}" --renamed-pass 2 --mode process --required
}

test_data_blob_dispositions_closeout_accepts_current_pass_formatted_rename_with_row() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local renames="${NESREV_TEST_TMPDIR}/renames.csv"
  local asm="${NESREV_TEST_TMPDIR}/current.asm"
  mkdir -p "${doc_root}"
  printf '# OAM Format\n' > "${doc_root}/OAM_FORMAT.md"
  cat > "${inv}" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
SmallOamTemplate,record_table,two 4-byte OAM records,OAM_FORMAT.md,Title renderer copies both records,direct indexed label load,eight bytes ending at NextData,reflowed,title cursor records
CSV
  cat > "${renames}" <<'CSV'
old_name,new_name,reason,confidence,pass_id
L8123,SmallOamTemplate,two OAM records,high,2
CSV
  cat > "${asm}" <<'ASM'
SmallOamTemplate:
; Format: two 4-byte OAM records [y, tile, attributes, x].
    .DB $10,$20,$00,$30
    .DB $18,$21,$00,$38
NextData:
    .DB $00
ASM

  assert_exit 0 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --asm "${asm}" \
    --renames "${renames}" --renamed-pass 2 --mode process --required
}

test_data_blob_dispositions_closeout_scopes_formatted_rename_to_requested_pass() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local renames="${NESREV_TEST_TMPDIR}/renames.csv"
  local asm="${NESREV_TEST_TMPDIR}/current.asm"
  mkdir -p "${doc_root}"
  _write_blob_header "${inv}"
  cat > "${renames}" <<'CSV'
old_name,new_name,reason,confidence,pass_id
L8123,HistoricalSmallTable,historical table,high,1
CSV
  cat > "${asm}" <<'ASM'
; Format: four-byte historical lookup.
HistoricalSmallTable:
    .DB $00,$01,$02,$03
ASM

  assert_exit 0 python3 "${DATA_BLOB_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --asm "${asm}" \
    --renames "${renames}" --renamed-pass 2 --mode process --required
}
