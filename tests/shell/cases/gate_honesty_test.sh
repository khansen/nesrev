#!/usr/bin/env bash
# Tests for two gates that reported cleanliness they had not established:
# a metric that auto-filled its own best value, and a check that treated a
# missing file as proof of no debt.
#
# The deferral half of the notes check now lives in proof_debt as a rate-based
# signal behind one flag, so its coverage lives in proof_debt_test.sh.
#
# Each is exercised in both directions, so a gate that silently stops
# reporting fails the suite.

NOTES_CHECK="${REPO_ROOT}/scripts/working_notes_maturity_check.sh"

_scorecard_with_passes() {
  # $1 = output path, $2 = highest pass id, $3 = notes text for every row
  local out="$1" top="$2" notes="$3" i
  {
    printf '| pass_id | focus | verify | docs_check | rework_items | notes |\n'
    printf '|---|---|---|---|---|---|\n'
    for ((i = 1; i <= top; i++)); do
      printf '| %d | corridor | pass | pass | 0 | %s |\n' "${i}" "${notes}"
    done
  } > "${out}"
}

test_working_notes_still_enforces_line_budget() {
  local dir="${NESREV_TEST_TMPDIR}" i
  for ((i = 0; i < 30; i++)); do printf 'note line\n'; done > "${dir}/notes.md"
  assert_exit 1 bash "${NOTES_CHECK}" "${dir}/notes.md" 10
}

test_working_notes_accepts_file_within_budget() {
  local dir="${NESREV_TEST_TMPDIR}" i
  for ((i = 0; i < 5; i++)); do printf 'note line\n'; done > "${dir}/notes.md"
  local out
  out="$(bash "${NOTES_CHECK}" "${dir}/notes.md" 10)"
  assert_match "within maturity budget" "${out}" "a small notes file must pass"
}

test_closeout_does_not_backfill_rework_items() {
  # The operator's judgement cell must not be auto-filled with its best value.
  local closeout="${REPO_ROOT}/scripts/project_pass_closeout.sh"
  if grep -q '"rework_items": "0"' "${closeout}"; then
    fail "closeout still seeds rework_items with 0"
  fi
  if grep -qE 'cells\[rework_col\] = "0"' "${closeout}"; then
    fail "closeout still backfills rework_items with 0"
  fi
  assert_match 'rework_items.*pending' "$(grep -m1 'rework_items": ' "${closeout}")" \
    "new scorecard rows must start with rework_items unrecorded"
}

test_working_notes_missing_file_reports_only_the_budget() {
  # Deferral reporting belongs to proof_debt; this check owns the line budget
  # alone, so one condition is not surfaced twice with two thresholds.
  local out
  out="$(bash "${NOTES_CHECK}" "${NESREV_TEST_TMPDIR}/absent.md" 120)"
  assert_match "no line budget to enforce" "${out}" \
    "a missing notes file reports on the budget, not on deferrals"
}

test_lifecycle_rejects_a_closed_row_with_unanswered_rework() {
  # The latest row may hold pending cells while its pass runs. Once closeout
  # has marked verify and docs_check, an unanswered rework_items is the same
  # false cleanliness as the auto-zero it replaced.
  local sc="${NESREV_TEST_TMPDIR}/sc.md"
  printf '| pass_id | focus | verify | docs_check | rework_items | notes |\n|---|---|---|---|---|---|\n| 1 | a | pass | pass | 0 | n |\n| 2 | b | pass | pass | pending | n |\n' > "${sc}"
  local out rc=0
  out="$(python3 "${REPO_ROOT}/scripts/scorecard_lifecycle_check.py" "${sc}" 2>&1)" || rc=$?
  assert_eq "${rc}" "1" "a closed row with unanswered rework_items must fail"
  # A crash also exits 1. Asserting only the status is how the first version of
  # this check shipped green while emitting nothing but a NameError.
  case "${out}" in
    *Traceback*) fail "check crashed instead of reporting: ${out}" ;;
  esac
  assert_match "rework_items" "${out}" "failure must name the column at fault"
}

test_lifecycle_allows_pending_while_the_pass_is_in_flight() {
  local sc="${NESREV_TEST_TMPDIR}/sc.md"
  printf '| pass_id | focus | verify | docs_check | rework_items | notes |\n|---|---|---|---|---|---|\n| 1 | a | pass | pass | 0 | n |\n| 2 | b | pending | pending | pending | n |\n' > "${sc}"
  python3 "${REPO_ROOT}/scripts/scorecard_lifecycle_check.py" "${sc}" >/dev/null
}
