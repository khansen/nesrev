#!/usr/bin/env bash
# Tests the scorecard cell lint that rejects a raw '|' in a Markdown table cell.

CHECK="${REPO_ROOT}/scripts/scorecard_cell_check.py"

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
