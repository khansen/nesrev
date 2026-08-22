#!/usr/bin/env bash
# Tests for proof-debt signals, the acknowledgement escape hatch, and
# closeout deferral capture.
#
# Every signal is exercised in both directions: a known-bad state that must
# report, and a healthy state that must stay silent. A detector that cannot be
# shown to fire is not a detector.

PROOF_DEBT="${REPO_ROOT}/scripts/proof_debt.py"
DEFERRAL_CAPTURE="${REPO_ROOT}/scripts/deferral_capture.py"

# Build a doc root with a scorecard of N passes, a renames ledger of M rows,
# and whatever evidence artifacts the caller asks for.
_fixture() {
  # $5 = labels_remaining cell; default leaves naming visibly incomplete, so
  # gold-closeout signals stay quiet unless a test asks for a finished project.
  local root="$1" passes="$2" renames="$3" notes_text="$4" labels="${5:-500 / 900}" i
  mkdir -p "${root}/inventory"
  {
    printf '| pass_id | focus | labels_remaining | verify | docs_check | rework_items | notes |\n'
    printf '|---|---|---|---|---|---|---|\n'
    for ((i = 1; i <= passes; i++)); do
      printf '| %d | corridor %d | %s | pass | pass | 0 | %s |\n' "${i}" "${i}" "${labels}" "${notes_text}"
    done
  } > "${root}/PROGRESS_SCORECARD.md"
  {
    printf 'old_name,new_name,reason,confidence,pass_id\n'
    for ((i = 0; i < renames; i++)); do
      printf 'L%04X,Name%d,proven,high,1\n' "$((0xC000 + i))" "${i}"
    done
  } > "${root}/inventory/renames.csv"
}

_crosswalk() {
  local out="$1" symbol="${2:-}" confidence="${3:-reference-only}"
  {
    printf '| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |\n'
    printf '|---|---|---|---|\n'
    printf '| Widget | %s | %s | manual |\n' "${symbol}" "${confidence}"
  } > "${out}"
}

test_proof_debt_reports_unmapped_crosswalk_after_sustained_work() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "900 renames logged across 40 passes" "${out}" \
    "sustained naming work with no mapped term must be reported"
  assert_match "0 of 1 crosswalk terms" "${out}" "report must be specific"
}

test_proof_debt_quiet_when_crosswalk_is_mapped() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" "a mapped crosswalk must be silent"
}

test_proof_debt_quiet_on_young_project() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 3 900 "named the corridor"
  _crosswalk "${root}/cw.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "a young project must not be reported however little it has proved"
}

test_proof_debt_reports_empty_semantic_claims_once_naming_is_complete() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor" "0 / 0"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf '# Semantic Claims\n\nNo claims recorded yet.\n' > "${root}/SEMANTIC_CLAIMS.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "records no claims" "${out}" \
    "sustained work with no recorded claim must be reported"
}

test_proof_debt_scaffold_template_does_not_count_as_a_claim() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor" "0 / 0"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf '# Semantic Claims\n\n## Claim: semantic-slug\n\nSubject: X\n' \
    > "${root}/SEMANTIC_CLAIMS.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "records no claims" "${out}" \
    "the scaffold template heading must not read as a recorded claim"
}

test_proof_debt_quiet_when_a_real_claim_exists() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf '# Semantic Claims\n\n## Claim: widget-ownership\n\nSubject: RunWidget\n' \
    > "${root}/SEMANTIC_CLAIMS.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" "a recorded claim must silence the signal"
}

test_proof_debt_reports_systematic_deferral_without_a_durable_home() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor; left broad RAM ownership out of scope"
  _crosswalk "${root}/cw.md" "RunWidget" "high"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "passes recorded a deferral" "${out}" \
    "systematic deferral with no durable home must be reported"
}

test_proof_debt_quiet_on_occasional_deferral() {
  # Ordinary scoped deferral is healthy and must never be reported.
  local root="${NESREV_TEST_TMPDIR}/doc" i
  _fixture "${root}" 40 900 "named the corridor and closed it"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  # one deferring pass out of forty
  printf '| 41 | corridor | pass | pass | 0 | left one byte out of scope |\n' \
    >> "${root}/PROGRESS_SCORECARD.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "an occasional deferral must not be reported as debt"
}

test_proof_debt_is_not_silenced_by_an_empty_notes_file() {
  # An existence conjunct lets one touched file silence a signal about
  # systematic deferral, which is the defect this branch set out to fix.
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor; left broad RAM ownership out of scope"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf '\n' > "${root}/WORKING_NOTES.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "no structured record" "${out}" \
    "creating an empty notes file must not silence the signal"
}

test_proof_debt_quiet_once_deferrals_are_captured() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor; left broad RAM ownership out of scope"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n1,c,ram-ownership,static,left ram ownership,trace the writer,open\n' \
    > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "a captured, closed deferral must satisfy the signal"
}

test_acknowledgement_ledger_silences_a_signal_permanently() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md"

  local before
  before="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "crosswalk terms" "${before}" "signal must fire before ack"

  printf 'signal,reason,pass_id\ncrosswalk_unmapped,concept has no single code owner in this ROM,40\n' \
    > "${root}/inventory/proof_debt_acknowledged.csv"

  local after
  after="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${after}" "an acknowledged signal must stay silent"
}

test_acknowledgement_without_a_reason_is_ignored() {
  # The ledger's value is the recorded judgement, not the silence.
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md"
  printf 'signal,reason,pass_id\ncrosswalk_unmapped,,40\n' \
    > "${root}/inventory/proof_debt_acknowledged.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "crosswalk terms" "${out}" \
    "a reasonless acknowledgement must not silence a signal"
}

test_deferral_capture_records_the_operators_own_words() {
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 12 --corridor "audio corridor" \
    --notes "Named the lanes. Left cue identities out of scope." >/dev/null

  local body; body="$(cat "${ledger}")"
  assert_match "cue identities" "${body}" "the deferred subject must be captured"
  assert_match "audio corridor" "${body}" "the corridor must be recorded"
  assert_match "open" "${body}" "a fresh capture must be open"
}

test_deferral_capture_is_idempotent() {
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  local args=(--pass-id 12 --corridor c --notes "Left cue identities out of scope.")
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" "${args[@]}" >/dev/null
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" "${args[@]}" >/dev/null

  local rows; rows="$(($(wc -l < "${ledger}") - 1))"
  assert_eq "${rows}" "1" "re-running closeout must not duplicate deferral rows"
}

test_deferral_capture_ignores_notes_without_a_deferral() {
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 12 --corridor c \
    --notes "Named the lanes and closed the corridor." >/dev/null
  if [[ -f "${ledger}" ]]; then
    fail "a pass that deferred nothing must not create a ledger"
  fi
}

test_proof_debt_reports_captured_deferrals_missing_a_revisit_condition() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n12,audio,cues,static,left cues out of scope,,open\n' \
    > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "no revisit condition" "${out}" \
    "a captured deferral with no revisit condition must be reported"
}

test_proof_debt_quiet_once_revisit_conditions_are_filled_in() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n12,audio,cues,static,left cues out of scope,capture a trace of the cue request byte,open\n' \
    > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "filling in the revisit condition must close the signal"
}

test_proof_debt_reports_a_repeatedly_deferred_subject_across_corridors() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  {
    printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n'
    printf '10,corridor a,feature-identity,static,left identity out of scope,trace it,open\n'
    printf '20,corridor b,feature-identity,static,left identity again,trace it,open\n'
    printf '30,corridor c,feature-identity,static,still deferred,trace it,open\n'
  } > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "deferred 3 times without closing" "${out}" \
    "a subject deferred across different corridors must still be caught"
}

test_deferral_capture_defaults_to_static_however_it_is_worded() {
  # Inferring runtime from a word like "dynamic" reproduces the exact
  # misclassification the runtime rule exists to prevent.
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 12 --corridor audio \
    --notes "Left dynamic feature-id meanings out of scope." >/dev/null

  assert_match ",static," "$(cat "${ledger}")" \
    "a deferral must default to static however it is phrased"
}

test_deferral_capture_accepts_an_explicit_runtime_promotion() {
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 12 --corridor audio --kind runtime \
    --notes "Left cue identities out of scope." >/dev/null

  assert_match ",runtime," "$(cat "${ledger}")" "an explicit promotion must be recorded"
}

test_proof_debt_reports_runtime_deferrals_with_no_trace_plan() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  {
    printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n'
    local i
    for ((i = 1; i <= 6; i++)); do
      printf '%d,corridor %d,subj%d,runtime,left identity to dynamic analysis,capture it,open\n' "${i}" "${i}" "${i}"
    done
  } > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "recorded as needing runtime evidence, but no trace plan exists" "${out}" \
    "runtime deferrals parked without a trace plan must be reported"
}

test_proof_debt_quiet_when_a_trace_plan_schedules_the_runtime_work() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  {
    printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n'
    local i
    for ((i = 1; i <= 6; i++)); do
      printf '%d,corridor %d,subj%d,runtime,left identity to dynamic analysis,capture it,open\n' "${i}" "${i}" "${i}"
    done
  } > "${root}/inventory/deferrals.csv"
  printf '# Cue Identity Trace Plan\n\nSignal: cue request byte.\n' \
    > "${root}/CUE_TRACE_PLAN.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "scheduling the runtime work must close the signal"
}

test_proof_debt_quiet_on_a_few_runtime_deferrals() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  {
    printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n'
    printf '1,a,subj1,runtime,left identity to dynamic analysis,capture it,open\n'
  } > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "one runtime deferral is normal and must not be reported"
}

test_proof_debt_does_not_nag_for_claims_before_naming_is_complete() {
  # Claims are a gold-closeout artifact. Nagging for them from the midpoint is
  # how a signal channel loses credibility.
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 40 900 "named the corridor" "500 / 900"
  _crosswalk "${root}/cw.md" "RunWidget" "high"
  printf '# Semantic Claims\n\nNo claims recorded yet.\n' > "${root}/SEMANTIC_CLAIMS.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "^OK: no proof debt" "${out}" \
    "an unfinished project must not be nagged for gold-closeout claims"
}

test_provenance_coverage_counts_only_reasoned_ledger_rows() {
  # A ledger row without a reason records that a rename happened, not why.
  local root="${NESREV_TEST_TMPDIR}/proj/docs/reverse_engineering"
  local asmdir="${NESREV_TEST_TMPDIR}/proj/asm"
  mkdir -p "${root}/inventory" "${asmdir}"
  printf 'RunWidget:\n    RTS\nRunGadget:\n    RTS\nL C000:\n' | sed 's/L C000/LC000/' > "${asmdir}/g.asm"
  {
    printf 'old_name,new_name,reason,confidence,pass_id\n'
    printf 'LC001,RunWidget,proven by callsites,high,1\n'
    printf 'LC002,RunGadget,,high,1\n'
  } > "${root}/inventory/renames.csv"
  _crosswalk "${root}/cw.md" "Widget|RunWidget|high"
  printf '| pass_id | focus | notes |\n|---|---|---|\n| 1 | c | n |\n' > "${root}/PROGRESS_SCORECARD.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md" --coverage)"
  assert_match "named labels -> rename ledger: 1/2" "${out}" \
    "only rows carrying a reason may count as provenance"
}

test_provenance_coverage_ignores_unresolved_labels() {
  # LXXXX labels are unnamed, so they are not yet decisions to justify.
  local root="${NESREV_TEST_TMPDIR}/proj/docs/reverse_engineering"
  local asmdir="${NESREV_TEST_TMPDIR}/proj/asm"
  mkdir -p "${root}/inventory" "${asmdir}"
  printf 'RunWidget:\n    RTS\nLC000:\n    RTS\nLC001:\n    RTS\n' > "${asmdir}/g.asm"
  printf 'old_name,new_name,reason,confidence,pass_id\nLC002,RunWidget,proven,high,1\n' \
    > "${root}/inventory/renames.csv"
  _crosswalk "${root}/cw.md" "Widget|RunWidget|high"
  printf '| pass_id | focus | notes |\n|---|---|---|\n| 1 | c | n |\n' > "${root}/PROGRESS_SCORECARD.md"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md" --coverage)"
  assert_match "named labels -> rename ledger: 1/1" "${out}" \
    "unresolved labels must not count against provenance coverage"
}

test_proof_debt_ledger_supersedes_the_prose_runtime_scan() {
  # A ledger that captured everything correctly as static, with no runtime
  # gaps, must not be warned about the prose it superseded.
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 20 900 "left dynamic feature-id meanings out of scope"
  _crosswalk "${root}/cw.md" "Widget" "RunWidget" "high"
  {
    printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n'
    local i
    for ((i = 1; i <= 8; i++)); do
      printf '%d,c,subj%d,static,left x,trace it,open\n' "${i}" "${i}"
    done
  } > "${root}/inventory/deferrals.csv"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  if printf '%s' "${out}" | grep -q 'runtime evidence'; then
    fail "an all-static ledger must supersede the prose runtime scan"
  fi
}

test_proof_debt_prose_scan_still_covers_a_project_with_no_ledger() {
  local root="${NESREV_TEST_TMPDIR}/doc"
  _fixture "${root}" 20 900 "left dynamic feature-id meanings out of scope"
  _crosswalk "${root}/cw.md" "Widget" "RunWidget" "high"

  local out
  out="$(python3 "${PROOF_DEBT}" "${root}" "${root}/cw.md")"
  assert_match "runtime evidence" "${out}" \
    "a project with no ledger must still be covered by the prose scan"
}

test_explicit_deferrals_bypass_prose_extraction() {
  # Prose parsing is the fallback. When the operator states the gap and what
  # would close it, nothing is inferred from a sentence written for a reader.
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 7 --corridor audio \
    --explicit "exact cue identities :: capture the cue request byte :: runtime" \
    --notes "Reflowed tables and left broad RAM ownership out of scope." >/dev/null

  local body; body="$(cat "${ledger}")"
  assert_match "capture the cue request byte" "${body}" "the stated condition must be recorded"
  assert_match ",runtime," "${body}" "an explicit runtime promotion must be honoured"
  if printf '%s' "${body}" | grep -q 'RAM ownership'; then
    fail "prose must not be parsed when explicit deferrals are supplied"
  fi
}

test_explicit_deferrals_default_to_static_without_a_kind() {
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 7 --corridor a \
    --explicit "broad RAM ownership :: prove the writer from the spawn table" >/dev/null
  assert_match ",static," "$(cat "${ledger}")" "an unmarked explicit deferral is static"
}

test_prose_extraction_still_runs_without_explicit_deferrals() {
  local ledger="${NESREV_TEST_TMPDIR}/deferrals.csv"
  python3 "${DEFERRAL_CAPTURE}" "${ledger}" --pass-id 7 --corridor a \
    --notes "Named the lanes. Left cue identities out of scope." >/dev/null
  assert_match "cue identities" "$(cat "${ledger}")" "prose remains the fallback"
}


# Execute the recommender against fixtures rather than reading its source.
# The fixtures must use the section names choose_recommended_pass actually
# reads (top_callables / top_data_labels / top_jump_targets) — an invented key
# means no corridor is present and every "outranks a corridor" test passes
# because there was nothing there to outrank.
_recommender() {
  python3 - "${REPO_ROOT}/scripts/project_next_pass.sh" "$@" <<'PY'
import json, re, sys
src = open(sys.argv[1]).read()
ns = {"re": re}
for start, end in (("GENERIC_RE = re.compile", "\n"),
                   ("def status_from_baseline", "def label_map"),
                   ("def top_named_routines", "def top_caller_sites"),
                   ("def choose_recommended_pass", "CORRIDOR_BUCKETS = {"),
                   ("CORRIDOR_BUCKETS = {", "def build_raw_ram_clusters")):
    at = src.index(start)
    exec(src[at:src.index(end, at + len(start))], ns)
case = json.loads(sys.argv[2])

def bl(parity="pass", docs="pass", process="pass", **metrics):
    return {"checks": {k: {"status": v} for k, v in
                       (("parity", parity), ("docs_check", docs), ("process_check", process))},
            "metrics": metrics}

def corridor(label, caller):
    return {"top_callables": [{"label": label, "total_ref_count": 9,
                               "top_referring_routines": [{"routine": caller}]}]}

generic = case.get("generic")
if generic is None and case.get("corridor"):
    generic = corridor(*case["corridor"])
ev = case.get("evidence")
rec = ns["choose_recommended_pass"](generic or {}, bl(**case.get("baseline", {})), [], [], ev)
chosen = rec["type"]
rec = ns["apply_identity_interception"](rec, case.get("families", []), ev)
# Report both halves so a test can tell "the corridor was never built" apart
# from "the corridor was built and then intercepted".
print(f"{chosen} {rec['type']}")
PY
}

# Every case below carries a real corridor, so identity_pass in the second
# field always means something was outranked or intercepted, never that the
# recommender fell through to its last resort.
#
# Fixture symbols are deliberately synthetic. This branch is master-based, so
# tracked files stay project-agnostic; borrowing a real family stem from a
# project's disassembly would also imply the rule under test is specific to
# that game's vocabulary, which it is not.
_SCREEN='"corridor":["RefreshFixtureFeatureState","UpdateFixtureFeatureState"],"baseline":{"lxxxx_definitions":772}'
_AUDIO='"corridor":["AdvanceFixtureQueueCursor","RunFixtureQueueFrame"],"baseline":{"lxxxx_definitions":772}'

test_recommender_urgent_deferral_outranks_an_available_corridor() {
  local out
  out="$(_recommender "{${_SCREEN},\"evidence\":{\"summary\":\"s\",\"reason\":\"deferred 5 times\",\"urgent\":true}}")"
  assert_eq "${out}" "identity_pass identity_pass" "three strikes must outrank a live corridor"
}

test_recommender_builds_the_corridor_when_nothing_flags_it() {
  # Guards the fixtures themselves: if this stops returning a corridor, every
  # "outranks" assertion above degrades into a vacuous pass.
  local out
  out="$(_recommender "{${_SCREEN}}")"
  assert_eq "${out}" "procedure_naming procedure_naming" "fixture must produce a real corridor"
}

test_recommender_intercepts_a_corridor_inside_the_flagged_family() {
  local out
  out="$(_recommender "{${_SCREEN},\"families\":[\"FixtureFeature\"],\"evidence\":{\"summary\":\"s\",\"reason\":\"drift\"}}")"
  assert_eq "${out}" "procedure_naming identity_pass" "a corridor anchored in the flagged family must be intercepted"
}

test_recommender_leaves_a_corridor_outside_the_family_alone() {
  # The interception is narrow: non-urgent identity evidence does not outrank
  # unresolved labels in general, only inside the family it flagged.
  local out
  out="$(_recommender "{${_AUDIO},\"families\":[\"FixtureFeature\"],\"evidence\":{\"summary\":\"s\",\"reason\":\"drift\"}}")"
  assert_eq "${out}" "procedure_naming procedure_naming" "an unrelated corridor must rank normally"
}

test_recommender_without_evidence_leaves_ranking_alone() {
  # An acknowledged signal arrives here as no evidence at all.
  local out
  out="$(_recommender "{${_SCREEN},\"families\":[\"FixtureFeature\"]}")"
  assert_eq "${out}" "procedure_naming procedure_naming" "an acknowledged signal must restore the normal ranking"
}

test_recommender_red_baseline_outranks_identity() {
  local out
  out="$(_recommender "{\"corridor\":[\"RefreshFixtureFeatureState\",\"UpdateFixtureFeatureState\"],\"baseline\":{\"parity\":\"fail\",\"lxxxx_definitions\":772},\"families\":[\"FixtureFeature\"],\"evidence\":{\"summary\":\"s\",\"reason\":\"deferred 5 times\",\"urgent\":true}}")"
  assert_eq "${out}" "baseline_repair baseline_repair" "a red baseline must outrank identity work"
}

# The cache-freshness block, sliced out of the script so the test stays coupled
# to the shipped source. Its first version compared `.git/HEAD` mtimes, which is
# inert in both directions: `.git` is a file in a linked worktree so the path
# does not exist, and a same-branch commit moves the branch ref, leaving HEAD
# untouched. Exercising it needs a real repo and a real commit.
_freshness_harness() {
  local repo="$1" prep_log="$2" out
  out="${NESREV_TEST_TMPDIR}/freshness.sh"
  {
    # A non-empty sources array on purpose: bash 3.2 under `set -u` treats an
    # empty one as unbound, and src.asm predates the cache so the mtime loop
    # runs without firing, leaving HEAD as the only thing under test.
    printf 'set -uo pipefail\nNEEDS_PREP=0\nPASS_CACHE_INPUTS=(cached.json)\n'
    printf 'PASS_CACHE_SOURCES=(%q)\n' "${repo}/src.asm"
    printf 'PREP_SCRIPT=%q\n' "${NESREV_TEST_TMPDIR}/fake_prep.sh"
    printf 'PASS_CACHE_DIR=%q\n' "${repo}/cache"
    awk '/HEAD_MARKER="\$\{PASS_CACHE_DIR\}\/\.head"/,/^fi$/' "${REPO_ROOT}/scripts/project_next_pass.sh" \
      | sed '$d'
  } > "${out}"
  printf '#!/usr/bin/env bash\necho x >> %q\n' "${prep_log}" > "${NESREV_TEST_TMPDIR}/fake_prep.sh"
  chmod +x "${NESREV_TEST_TMPDIR}/fake_prep.sh"
  ( cd "${repo}" && bash "${out}" ignored ) >/dev/null 2>&1
}

test_cache_freshness_reacts_to_a_same_branch_commit() {
  local repo="${NESREV_TEST_TMPDIR}/repo" log="${NESREV_TEST_TMPDIR}/prep.log"
  mkdir -p "${repo}/cache"; : > "${log}"
  ( cd "${repo}" && git init -q && git config user.email t@t && git config user.name t && git config commit.gpgsign false \
    && git commit -q --allow-empty -m one )
  : > "${repo}/src.asm"
  sleep 1
  echo '{}' > "${repo}/cache/cached.json"

  # First run: no marker yet, so the cache is stale by definition.
  _freshness_harness "${repo}" "${log}"
  assert_eq "$(wc -l < "${log}" | tr -d ' ')" "1" "a missing marker must refresh"

  # Nothing moved: a second run must not refresh, or the marker is being
  # ignored and every invocation pays for a prep.
  _freshness_harness "${repo}" "${log}"
  assert_eq "$(wc -l < "${log}" | tr -d ' ')" "1" "an unchanged HEAD must not refresh"

  # A commit on the same branch — the case the mtime version could not see.
  ( cd "${repo}" && git commit -q --allow-empty -m two )
  _freshness_harness "${repo}" "${log}"
  assert_eq "$(wc -l < "${log}" | tr -d ' ')" "2" "a same-branch commit must refresh"

  # And it settles afterwards rather than refreshing forever.
  _freshness_harness "${repo}" "${log}"
  assert_eq "$(wc -l < "${log}" | tr -d ' ')" "2" "the refresh must record the new HEAD"
}
