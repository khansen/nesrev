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
  cat > "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv" <<'CSV'
symbol,inventory,disposition,localization,rationale
UndocumentedProc,callable+global,retained_headerless,retain_global,Public callable with a self-explanatory body.
UndocumentedTail,callable+global,retained_headerless,deferred,Localizing the tail needs a separate scope review; the body needs no header.
UndocumentedEntry,global,retained_headerless,retain_global,External fixture entry retained without a redundant header.
CSV
}

_write_policy_baseline_documented_asm() {
  local slug="$1"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
; Reset is the only entry in this fully documented fixture.
Reset:
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv" <<'CSV'
symbol,inventory,disposition,localization,rationale
CSV
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
    "policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=3; action=reviewed all detail rows."

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
| policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=3; action=reviewed all detail rows. | Policy baseline audit | 1 | pass | pass | 0 |
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
    "policy-baseline-audit: semantic_claims=reviewed; procedures=1/2; global_code_labels=2/3; retained_headerless=2; action=partial review remains."
  perl -pi -e 's/^UndocumentedProc,callable\+global,retained_headerless,retain_global,/UndocumentedProc,callable+global,pending,pending,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"

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

_make_complete_policy_manifest_fixture() {
  local slug="$1"
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_partial_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=3; action=reviewed the live union."
}

_assert_policy_manifest_failure() {
  local slug="$1" diagnostic="$2" output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "invalid active manifest must fail"
  assert_match "${diagnostic}" "${output}"
}

test_policy_manifest_equal_count_wrong_member_fails() {
  local slug; slug="$(unique_slug policy_wrong_member)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/^UndocumentedEntry,/DocumentedEntry,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "missing live detail symbol UndocumentedEntry"
  _assert_policy_manifest_failure "${slug}" "DocumentedEntry is not in the live detail union"
}

test_policy_manifest_missing_fails_including_zero_candidates() {
  local slug; slug="$(unique_slug policy_missing_manifest)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  _write_policy_baseline_documented_asm "${slug}"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=empty union reviewed."
  rm "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "cannot read active policy manifest"
}

test_policy_manifest_duplicate_symbol_fails() {
  local slug; slug="$(unique_slug policy_duplicate)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/^UndocumentedEntry,global,/UndocumentedProc,callable+global,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "duplicate manifest symbol UndocumentedProc"
}

test_policy_manifest_wrong_inventory_fails() {
  local slug; slug="$(unique_slug policy_wrong_inventory)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/^UndocumentedProc,callable\+global,/UndocumentedProc,global,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "UndocumentedProc inventory must be callable\+global"
}

test_policy_manifest_stale_disposition_fails() {
  local slug; slug="$(unique_slug policy_stale_disposition)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/retained_headerless/documented/g' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "invalid disposition 'documented'"
}

test_policy_manifest_invented_reviewed_count_fails() {
  local slug; slug="$(unique_slug policy_invented_count)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/^UndocumentedProc,callable\+global,retained_headerless,retain_global,/UndocumentedProc,callable+global,pending,pending,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "procedures reviewed count 2 does not match active manifest count 1"
}

test_policy_manifest_retained_count_is_distinct_union() {
  local slug; slug="$(unique_slug policy_distinct_count)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/retained_headerless=3/retained_headerless=5/' \
    "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"
  _assert_policy_manifest_failure "${slug}" "retained_headerless count 5 does not match active manifest count 3"
}

test_policy_manifest_reviewed_requires_localization_decision() {
  local slug; slug="$(unique_slug policy_localization)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/,retain_global,/,pending,/g' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "reviewed UndocumentedProc requires a localization decision"
}

test_policy_manifest_empty_rationale_fails() {
  local slug; slug="$(unique_slug policy_rationale)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/,retain_global,.*/,retain_global,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "rationale must not be empty"
}

test_policy_manifest_csv_schema_and_row_shape_fail() {
  local slug; slug="$(unique_slug policy_csv_shape)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/^symbol,/candidate,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "expected CSV header"
  _write_policy_baseline_partial_asm "${slug}"
  perl -pi -e 's/(^UndocumentedProc,.*)/$1,extra/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "manifest row column count mismatch"
}

test_policy_manifest_source_rename_with_equal_counts_fails() {
  local slug; slug="$(unique_slug policy_source_rename)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/UndocumentedEntry:/RenamedEntry:/' "projects/${slug}/asm/${slug}.asm"
  _assert_policy_manifest_failure "${slug}" "missing live detail symbol RenamedEntry"
}

test_policy_manifest_archived_snapshots_are_not_current_evidence() {
  local slug; slug="$(unique_slug policy_historical)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  local archive="projects/${slug}/docs/reverse_engineering/reviews/pass-0-policy-baseline-audit.md"
  mkdir -p "$(dirname "${archive}")"
  printf '%s\n' 'Historical candidate `OldName` was localized in a later pass.' > "${archive}"
  local before; before="$(cksum "${archive}")"
  bash "${POLICY_BASELINE_CHECK}" "${slug}" --require >/dev/null
  assert_eq "$(cksum "${archive}")" "${before}" "historical evidence must remain untouched"
  rm "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "cannot read active policy manifest"
}

test_policy_manifest_callable_only_alias_is_not_assumed_global() {
  local slug; slug="$(unique_slug policy_alias_union)"
  trap "cleanup_project ${slug}" EXIT
  _make_policy_baseline_project "${slug}"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
; The fixture enters through the first alias.
Reset:
  JSR AliasEntry
  RTS

AliasEntry:
BodyEntry:
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv" <<'CSV'
symbol,inventory,disposition,localization,rationale
AliasEntry,callable,retained_headerless,retain_global,"Public alias, with no separate body contract."
BodyEntry,global,retained_headerless,retain_global,"Shared entry retained for the fixture;
the return needs no extra header."
CSV
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=1/1; global_code_labels=1/1; retained_headerless=2; action=reviewed independent candidate sets."
  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" --require)"
  assert_match 'distinct_candidates=2' "${output}"
}

test_policy_manifest_pending_rows_do_not_claim_review() {
  local slug; slug="$(unique_slug policy_pending)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/,retained_headerless,(retain_global|deferred),/,pending,pending,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _write_policy_baseline_scorecard "${slug}" \
    "policy-baseline-audit: semantic_claims=reviewed; procedures=0/2; global_code_labels=0/3; retained_headerless=0; action=review is still pending."
  local output
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}")"
  assert_match 'in-progress' "${output}"
  _assert_policy_manifest_failure "${slug}" 'requires complete audit fractions'
}

test_policy_manifest_invalid_in_advisory_mode_still_fails() {
  local slug; slug="$(unique_slug policy_advisory_invalid)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/^UndocumentedEntry,/InventedEntry,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  local output rc
  set +e
  output="$(bash "${POLICY_BASELINE_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" 1
  assert_match 'InventedEntry is not in the live detail union' "${output}"
}

test_policy_manifest_invalid_enum_and_missing_cell_fail() {
  local slug; slug="$(unique_slug policy_invalid_fields)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  perl -pi -e 's/,retain_global,/,localized,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "invalid localization 'localized'"
  _write_policy_baseline_partial_asm "${slug}"
  perl -pi -e 's/,callable\+global,/,both,/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" "invalid inventory 'both'"
  _write_policy_baseline_partial_asm "${slug}"
  perl -pi -e 's/(^UndocumentedEntry,[^,]+,[^,]+,[^,]+),.*/$1/' \
    "projects/${slug}/docs/reverse_engineering/inventory/policy_baseline.csv"
  _assert_policy_manifest_failure "${slug}" 'manifest row column count mismatch'
}

test_policy_manifest_explicit_path_and_latest_marker_are_used() {
  local slug; slug="$(unique_slug policy_explicit_path)"
  trap "cleanup_project ${slug}" EXIT
  _make_complete_policy_manifest_fixture "${slug}"
  local root="projects/${slug}/docs/reverse_engineering"
  perl -pi -e 's/\| 1 \|/| 0 |/; s/retained_headerless=3/retained_headerless=999/' \
    "${root}/PROGRESS_SCORECARD.md"
  cat >> "${root}/PROGRESS_SCORECARD.md" <<'MD'
| 2 | Current review | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pass | 0 | policy-baseline-audit: semantic_claims=reviewed; procedures=2/2; global_code_labels=3/3; retained_headerless=3; action=current manifest reviewed. |
MD
  mv "${root}/inventory/policy_baseline.csv" "${root}/inventory/selected.csv"
  python3 "${REPO_ROOT}/scripts/policy_baseline_audit_check.py" \
    --asm "projects/${slug}/asm/${slug}.asm" \
    --scorecard "${root}/PROGRESS_SCORECARD.md" \
    --semantic-claims "${root}/SEMANTIC_CLAIMS.md" \
    --scripts-dir "${REPO_ROOT}/scripts" --manifest "${root}/inventory/selected.csv" --require >/dev/null
  _assert_policy_manifest_failure "${slug}" 'cannot read active policy manifest'
}
