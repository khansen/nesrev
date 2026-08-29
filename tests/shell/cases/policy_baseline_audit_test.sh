#!/usr/bin/env bash
# Tests policy baseline scorecard marker validation.

POLICY_BASELINE_CHECK="${REPO_ROOT}/scripts/project_policy_baseline_check.sh"
PROJECT_MATURITY_CHECK="${REPO_ROOT}/scripts/project_maturity_check.sh"

_make_policy_baseline_project() {
  local slug="$1"
  local root="projects/${slug}"
  cleanup_project "${slug}"
  mkdir -p \
    "${root}/asm" \
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
EOF
  : > "${root}/reference/${slug}.nes"
  : > "${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
  _write_valid_retrofit_claim "${slug}"
}

_write_policy_baseline_partial_asm() {
  local slug="$1"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
; Reset enters the fixture call chain.
Reset:
  JSR DocumentedProc
  JSR UndocumentedProc
  JMP UndocumentedTail

; Documented helper contract.
DocumentedProc:
  RTS

UndocumentedProc:
  RTS

UndocumentedTail:
  RTS

; Documented public entry not called by the fixture.
DocumentedEntry:
  RTS

UndocumentedEntry:
  RTS

DataTable:
  .DB $00
ASM
}

_write_policy_baseline_documented_asm() {
  local slug="$1"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
; Reset is the only entry in this fully documented fixture.
Reset:
  RTS
ASM
}

_write_policy_baseline_scorecard() {
  local slug="$1" notes="$2"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<EOF
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---:|---:|---:|---:|---:|---|---|---|---:|---|
| 1 | Policy baseline audit | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pass | 0 | ${notes} |
EOF
}

_write_valid_retrofit_claim() {
  local slug="$1"
  cat > "projects/${slug}/docs/reverse_engineering/SEMANTIC_CLAIMS.md" <<'MD'
# Semantic Claims

## Claim: reset-entry

Subject: Reset
Kind: subsystem
Subsystem: boot
Claim: reset is the boot entry point for this fixture.
Confidence: high
Evidence:
- The fixture starts at `Reset`.
Caveats:
- None.
Canonical docs:
- SEMANTIC_CLAIMS.md
MD
}

_enable_policy_baseline_required() {
  local slug="$1"
  cat >> "projects/${slug}/project.conf" <<'EOF'
EOF
}

test_policy_baseline_marker_cross_checks_live_detail_denominators() {
  local slug; slug="$(unique_slug legacy_marker_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows."

  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require)"
  assert_match "procedures=2/2" "${output}"
  assert_match "global_code_labels=3/3" "${output}"
}

test_policy_baseline_marker_accepts_reordered_scorecard_header() {
  local slug; slug="$(unique_slug legacy_marker_reordered)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| notes | focus | pass_id | verify | docs_check | rework_items |
|---|---|---|---|---|---:|
| policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows. | Policy baseline audit | 1 | pass | pass | 0 |
EOF

  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require)"
  assert_match "procedures=2/2" "${output}"
  assert_match "global_code_labels=3/3" "${output}"
}

test_policy_baseline_marker_bad_denominator_fails() {
  local slug; slug="$(unique_slug legacy_marker_bad_den)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=2/99; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows."

  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "bad live denominator must fail"
  assert_match "procedures denominator 99 does not match live procedure detail line count 2" "${output}"
}

test_policy_baseline_marker_in_progress_is_advisory_until_required() {
  local slug; slug="$(unique_slug legacy_marker_in_progress)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=1/2; global_code_labels=3/3; retained_headerless=1; action=partial review remains."

  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}")"
  assert_match "in-progress" "${output}"

  local rc
  set +e
  bash "${POLICY_BASELINE_CHECK}" "${slug}" --require >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "1" "current-gold mode must reject incomplete fractions"
}

test_policy_baseline_marker_missing_is_advisory_until_required() {
  local slug; slug="$(unique_slug legacy_marker_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" "No retrofit marker yet."

  bash "${POLICY_BASELINE_CHECK}" "${slug}" >/dev/null

  local rc
  set +e
  bash "${POLICY_BASELINE_CHECK}" "${slug}" --require >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "1" "current-gold mode must require a marker"
}

test_policy_baseline_marker_malformed_fails_when_present() {
  local slug; slug="$(unique_slug legacy_marker_malformed)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=missing delimiter."

  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "malformed marker must fail even in advisory mode"
  assert_match "malformed policy-baseline-audit marker" "${output}"
}

test_policy_baseline_marker_must_live_in_notes_column() {
  local slug; slug="$(unique_slug legacy_marker_wrong_col)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | verify | docs_check | rework_items | notes |
|---|---|---|---|---:|---|
| 1 | policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows. | pass | pass | 0 | Marker text is in the wrong column. |
EOF

  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "marker in a non-notes column must fail clearly"
  assert_match "policy-baseline-audit marker must live in the notes column" "${output}"
}

test_policy_baseline_marker_zero_zero_is_complete() {
  local slug; slug="$(unique_slug legacy_marker_zero)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_documented_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=no undocumented detail rows remained."

  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require)"
  assert_match "complete" "${output}"
}

test_policy_baseline_required_rejects_advisory_semantic_claim_state() {
  local slug; slug="$(unique_slug policy_marker_advisory)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_documented_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=advisory; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=semantic claim audit remains provisional."

  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "maturity marker must not preserve advisory semantic claims"
  assert_match "requires semantic_claims=created or reviewed" "${output}"
}

test_policy_baseline_required_maturity_fails_without_marker() {
  local slug; slug="$(unique_slug legacy_maturity_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_documented_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" "No retrofit marker yet."
  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "universal maturity policy must require a baseline marker"
  assert_match "universal current-policy audit requires a valid policy-baseline-audit marker" "${output}"
  assert_match 'project_policy_baseline_check\.sh.*--require' \
    "$(<"${PROJECT_MATURITY_CHECK}")"
}

test_policy_baseline_required_maturity_accepts_valid_marker() {
  local slug; slug="$(unique_slug legacy_maturity_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_documented_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=no undocumented detail rows remained."
  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  assert_match "policy baseline audit marker complete" "${output}"
}

test_policy_baseline_marker_created_claims_requires_maturity_ledger() {
  local slug; slug="$(unique_slug legacy_marker_claims)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_documented_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=created; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=claims ledger promoted."

  rm "projects/${slug}/docs/reverse_engineering/SEMANTIC_CLAIMS.md"

  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "created claims marker must require a maturity-valid ledger"
  assert_match "semantic_claims=created requires" "${output}"

  _write_valid_retrofit_claim "${slug}"
  bash "${POLICY_BASELINE_CHECK}" "${slug}" --require >/dev/null
}
