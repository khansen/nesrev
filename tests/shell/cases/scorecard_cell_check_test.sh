#!/usr/bin/env bash
# Tests the scorecard cell lint that rejects a raw '|' in a Markdown table cell.

CHECK="${REPO_ROOT}/scripts/scorecard_cell_check.py"
LIFECYCLE_CHECK="${REPO_ROOT}/scripts/scorecard_lifecycle_check.py"

_write_scorecard() {  # $1 path, $2 note-cell text
  cat > "$1" <<EOF
# Progress Scorecard

| pass_id | focus | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|
| 1 | Intake | pass | pass | 0 | $2 |
EOF
}

test_scorecard_cell_check_passes_on_pipe_free_notes() {
  local sc="${NESREV_TEST_TMPDIR}/sc_ok.md"
  # Pipe-free prose form for a codeentries reference.
  _write_scorecard "${sc}" "recovered island; codeentries bank 1 \$A64C"
  python3 "${CHECK}" "${sc}" >/dev/null
}

test_scorecard_cell_check_fails_on_raw_pipe_in_note() {
  local sc="${NESREV_TEST_TMPDIR}/sc_bad.md"
  # A codeentries reference written with a raw pipe (bank|$addr) -> phantom column.
  _write_scorecard "${sc}" "recovered island; codeentries \`1|\$A64C\`"

  assert_exit 1 python3 "${CHECK}" "${sc}"

  local out
  out="$(python3 "${CHECK}" "${sc}" 2>&1 || true)"
  assert_match "is not allowed in scorecard cells" "${out}" \
    "should report the clear raw-pipe message"
  assert_match "bank 1" "${out}" \
    "should suggest the pipe-free prose form"
}

_write_lifecycle_scorecard() {  # $1 path, remaining rows on stdin
  {
    cat <<'EOF'
# Progress Scorecard

| pass_id | focus | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|
EOF
    cat
  } > "$1"
}

test_scorecard_lifecycle_allows_latest_pending() {
  local sc="${NESREV_TEST_TMPDIR}/sc_lifecycle_ok.md"
  _write_lifecycle_scorecard "${sc}" <<'EOF'
| 0 | Intake | pass | pass | 0 | Intake baseline. |
| 1 | Current pass | pending | pending | 0 | Closeout in progress. |
EOF

  python3 "${LIFECYCLE_CHECK}" "${sc}" >/dev/null
}

test_scorecard_lifecycle_rejects_duplicate_pass_id() {
  local sc="${NESREV_TEST_TMPDIR}/sc_lifecycle_dup.md"
  _write_lifecycle_scorecard "${sc}" <<'EOF'
| 0 | Intake | pass | pass | 0 | Intake baseline. |
| 1 | First pass | pass | pass | 0 | Complete. |
| 1 | Duplicate pass | pending | pending | 0 | Bad ledger. |
EOF

  assert_exit 1 python3 "${LIFECYCLE_CHECK}" "${sc}"

  local out
  out="$(python3 "${LIFECYCLE_CHECK}" "${sc}" 2>&1 || true)"
  assert_match "duplicate pass_id 1" "${out}"
}

test_scorecard_lifecycle_rejects_out_of_order_pass_id() {
  local sc="${NESREV_TEST_TMPDIR}/sc_lifecycle_order.md"
  _write_lifecycle_scorecard "${sc}" <<'EOF'
| 0 | Intake | pass | pass | 0 | Intake baseline. |
| 2 | Second pass | pass | pass | 0 | Complete. |
| 1 | First pass late | pending | pending | 0 | Bad ledger. |
EOF

  assert_exit 1 python3 "${LIFECYCLE_CHECK}" "${sc}"

  local out
  out="$(python3 "${LIFECYCLE_CHECK}" "${sc}" 2>&1 || true)"
  assert_match "pass_id 1 is out of order after 2" "${out}"
}

test_scorecard_lifecycle_rejects_historical_pending_gate() {
  local sc="${NESREV_TEST_TMPDIR}/sc_lifecycle_pending.md"
  _write_lifecycle_scorecard "${sc}" <<'EOF'
| 0 | Intake | pass | pass | 0 | Intake baseline. |
| 1 | Stale pass | pending | pass | 0 | Bad ledger. |
| 2 | Current pass | pending | pending | 0 | Closeout in progress. |
EOF

  assert_exit 1 python3 "${LIFECYCLE_CHECK}" "${sc}"

  local out
  out="$(python3 "${LIFECYCLE_CHECK}" "${sc}" 2>&1 || true)"
  assert_match "non-latest pass 1 has verify='pending'" "${out}"
}
