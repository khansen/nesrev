#!/usr/bin/env bash
# Tests scripts/csv_row_update.py's safe row-update contract.

CSV_ROW_UPDATE="${REPO_ROOT}/scripts/csv_row_update.py"

test_csv_row_update_quotes_a_comma_bearing_field() {
  local ledger="${NESREV_TEST_TMPDIR}/ledger.csv"
  printf 'label,disposition,notes\nFoo,queued_static_pass,todo\nBar,queued_static_pass,todo\n' \
    > "${ledger}"

  python3 "${CSV_ROW_UPDATE}" "${ledger}" --where label=Foo \
    --set disposition=record_table --set "notes=has, a comma" >/dev/null

  local body; body="$(cat "${ledger}")"
  assert_match 'Foo,record_table,"has, a comma"' "${body}" \
    "a comma-bearing field must be quoted, not left to break the column count"
  assert_match 'Bar,queued_static_pass,todo' "${body}" \
    "an unrelated row must be preserved unchanged"
}

test_csv_row_update_refuses_ambiguous_match() {
  local ledger="${NESREV_TEST_TMPDIR}/ledger.csv"
  printf 'label,disposition,notes\nFoo,queued_static_pass,todo\nBar,queued_static_pass,todo\n' \
    > "${ledger}"

  local rc
  set +e
  python3 "${CSV_ROW_UPDATE}" "${ledger}" --where disposition=queued_static_pass \
    --set notes=x >/dev/null 2>&1
  rc=$?
  set -e

  assert_eq "${rc}" "1" "an unscoped --where matching two rows must be refused without --allow-multiple"
  assert_match 'Foo,queued_static_pass,todo' "$(cat "${ledger}")" \
    "a refused update must leave the ledger untouched"
}

test_csv_row_update_refuses_and_does_not_touch_a_ledger_with_a_preexisting_corrupt_row() {
  # A row that already has more fields than the header (an earlier unquoted
  # comma) used to make writerows() raise partway through, after the target
  # file had already been truncated and partially rewritten -- destroying
  # every row, not just the corrupt one. This is the reproduction from the
  # code review that caught it: update a valid row that sorts before the
  # corrupt one, so the corrupt row would previously have been reached only
  # after real data was already lost.
  local ledger="${NESREV_TEST_TMPDIR}/ledger.csv"
  printf 'label,disposition,notes\nAaa,queued_static_pass,fine\nZzz,queued_static_pass,uh oh, unquoted comma\n' \
    > "${ledger}"
  local before; before="$(cat "${ledger}")"

  local rc output
  set +e
  output="$(python3 "${CSV_ROW_UPDATE}" "${ledger}" --where label=Aaa --set disposition=record_table 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "a ledger with a pre-existing corrupt row must be refused, not partially rewritten"
  assert_match "more fields than the header" "${output}"
  assert_eq "$(cat "${ledger}")" "${before}" \
    "refusing the update must leave the file byte-for-byte untouched"
}
