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
