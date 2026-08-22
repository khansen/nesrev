#!/usr/bin/env bash
# Tests for the vocabulary-drift detectors and the two scorecard/notes gate
# fixes. Each check is exercised against a known-bad state as well as a good
# one, so a silently-passing detector fails the suite.

PROOF_DEBT="${REPO_ROOT}/scripts/proof_debt.py"
VOCAB_CHECK="${REPO_ROOT}/scripts/symbol_vocabulary_check.py"

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

_crosswalk() {
  # $1 = output path; remaining args = "term|symbol|confidence" rows
  local out="$1"; shift
  {
    printf '| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |\n'
    printf '|---|---|---|---|\n'
    local row
    for row in "$@"; do
      IFS='|' read -r term symbol confidence <<< "${row}"
      printf '| %s | %s | %s | manual |\n' "${term}" "${symbol}" "${confidence}"
    done
  } > "${out}"
}

test_crosswalk_currency_reports_unmapped_after_enough_passes() {
  local dir="${NESREV_TEST_TMPDIR}"
  _crosswalk "${dir}/cw.md" "Hero||reference-only" "Villain||reference-only"
  _scorecard_with_passes "${dir}/PROGRESS_SCORECARD.md" 9 "named things"

  local out
  out="$(python3 "${PROOF_DEBT}" "${dir}" "${dir}/cw.md" --crosswalk-only)"
  assert_match "2 reference terms, none mapped" "${out}" "unmapped crosswalk must be reported"
  assert_match "after 9 passes" "${out}" "report must cite the pass count"
}

test_crosswalk_currency_quiet_before_min_passes() {
  local dir="${NESREV_TEST_TMPDIR}"
  _crosswalk "${dir}/cw.md" "Hero||reference-only"
  _scorecard_with_passes "${dir}/PROGRESS_SCORECARD.md" 2 "named things"

  local out
  out="$(python3 "${PROOF_DEBT}" "${dir}" "${dir}/cw.md" --crosswalk-only)"
  assert_eq "${out}" "" "an early project must not be reported"
}

test_crosswalk_currency_accepts_mapped_terms() {
  local dir="${NESREV_TEST_TMPDIR}"
  _crosswalk "${dir}/cw.md" "Hero|RunHero|high" "Villain||reference-only"
  _scorecard_with_passes "${dir}/PROGRESS_SCORECARD.md" 9 "named things"

  local out
  out="$(python3 "${PROOF_DEBT}" "${dir}" "${dir}/cw.md" --crosswalk-only)"
  assert_match "^OK: crosswalk currency 1/2" "${out}" "a mapped crosswalk must pass"
}

test_symbol_vocabulary_reports_dominant_unaccounted_family() {
  local dir="${NESREV_TEST_TMPDIR}" i
  _crosswalk "${dir}/cw.md" "Hero||reference-only"
  {
    printf '.ORG $C000\n'
    for ((i = 0; i < 120; i++)); do
      printf 'UpdateWidgetHolderStage%d:\n    RTS\n' "${i}"
    done
  } > "${dir}/game.asm"

  local out
  out="$(python3 "${VOCAB_CHECK}" "${dir}/game.asm" "${dir}/cw.md" --dominant 100)"
  assert_match "WidgetHolder: 120 symbols" "${out}" "dominant private family must be reported"
  assert_match "not in crosswalk" "${out}" "coverage annotation must be present"
}

test_symbol_vocabulary_accepts_family_named_by_crosswalk() {
  local dir="${NESREV_TEST_TMPDIR}" i
  _crosswalk "${dir}/cw.md" "Widget Holder|RunWidgetHolder|high"
  {
    printf '.ORG $C000\n'
    for ((i = 0; i < 120; i++)); do
      printf 'UpdateWidgetHolderStage%d:\n    RTS\n' "${i}"
    done
  } > "${dir}/game.asm"

  local out
  out="$(python3 "${VOCAB_CHECK}" "${dir}/game.asm" "${dir}/cw.md" --dominant 100)"
  assert_match "^OK: dominant symbol families are accounted for" "${out}" \
    "a family the crosswalk names must not be reported as drift"
}

test_symbol_vocabulary_ignores_unresolved_labels() {
  local dir="${NESREV_TEST_TMPDIR}" i
  _crosswalk "${dir}/cw.md" "Hero||reference-only"
  {
    printf '.ORG $C000\n'
    for ((i = 0; i < 200; i++)); do
      printf 'L%04X:\n    RTS\n' "$((0xC000 + i))"
    done
  } > "${dir}/game.asm"

  local out
  out="$(python3 "${VOCAB_CHECK}" "${dir}/game.asm" "${dir}/cw.md" --dominant 100)"
  assert_match "^OK: no symbol phrase dominates" "${out}" \
    "unresolved LXXXX labels must not count as vocabulary"
}


test_symbol_vocabulary_suppresses_partial_match_when_crosswalk_is_well_mapped() {
  # A project demonstrably naming what the reference material names is more
  # likely to have found a real subsystem than invented private vocabulary.
  local dir="${NESREV_TEST_TMPDIR}" i
  _crosswalk "${dir}/cw.md" "Widget|RunWidget|high" "Holder|RunHolder|high" "Gadget|RunGadget|high"
  {
    printf '.ORG $C000\n'
    for ((i = 0; i < 120; i++)); do printf 'UpdateWidgetSprocketStage%d:\n    RTS\n' "${i}"; done
  } > "${dir}/game.asm"

  local out
  out="$(python3 "${VOCAB_CHECK}" "${dir}/game.asm" "${dir}/cw.md" --dominant 100)"
  assert_match "^OK:" "${out}" \
    "a partial match must be suppressed when the crosswalk is well mapped"
}

test_symbol_vocabulary_still_reports_partial_match_when_crosswalk_is_unmapped() {
  local dir="${NESREV_TEST_TMPDIR}" i
  _crosswalk "${dir}/cw.md" "Widget||reference-only" "Holder||reference-only"
  {
    printf '.ORG $C000\n'
    for ((i = 0; i < 120; i++)); do printf 'UpdateWidgetSprocketStage%d:\n    RTS\n' "${i}"; done
  } > "${dir}/game.asm"

  local out
  out="$(python3 "${VOCAB_CHECK}" "${dir}/game.asm" "${dir}/cw.md" --dominant 100)"
  assert_match "WidgetSprocket: 120 symbols" "${out}" \
    "an unmapped crosswalk must not suppress anything"
}
