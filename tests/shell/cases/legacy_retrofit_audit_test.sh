#!/usr/bin/env bash
# Tests legacy retrofit scorecard marker validation.

LEGACY_RETROFIT_CHECK="${REPO_ROOT}/scripts/project_legacy_retrofit_check.sh"
PROJECT_MATURITY_CHECK="${REPO_ROOT}/scripts/project_maturity_check.sh"

_make_legacy_retrofit_project() {
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
EOF
  : > "${root}/reference/${slug}.nes"
  : > "${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
}

_write_legacy_retrofit_partial_asm() {
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

_write_legacy_retrofit_documented_asm() {
  local slug="$1"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
; Reset is the only entry in this fully documented fixture.
Reset:
  RTS
ASM
}

_write_legacy_retrofit_scorecard() {
  local slug="$1" notes="$2"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<EOF
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---:|---:|---:|---:|---:|---|---|---|---:|---|
| 1 | Legacy retrofit audit | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pass | 0 | ${notes} |
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

_enable_legacy_retrofit_required() {
  local slug="$1"
  cat >> "projects/${slug}/project.conf" <<'EOF'
LEGACY_RETROFIT_REQUIRED="1"
EOF
}

test_legacy_retrofit_marker_cross_checks_live_detail_denominators() {
  local slug; slug="$(unique_slug legacy_marker_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=advisory; procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows."

  local output
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require)"
  assert_match "procedures=2/2" "${output}"
  assert_match "global_code_labels=3/3" "${output}"
}

test_legacy_retrofit_marker_accepts_reordered_scorecard_header() {
  local slug; slug="$(unique_slug legacy_marker_reordered)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| notes | focus | pass_id | verify | docs_check | rework_items |
|---|---|---|---|---|---:|
| legacy-retrofit-audit: semantic_claims=advisory; procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows. | Legacy retrofit audit | 1 | pass | pass | 0 |
EOF

  local output
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require)"
  assert_match "procedures=2/2" "${output}"
  assert_match "global_code_labels=3/3" "${output}"
}

test_legacy_retrofit_marker_bad_denominator_fails() {
  local slug; slug="$(unique_slug legacy_marker_bad_den)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=advisory; procedures=2/99; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows."

  local output rc
  set +e
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "bad live denominator must fail"
  assert_match "procedures denominator 99 does not match live procedure detail line count 2" "${output}"
}

test_legacy_retrofit_marker_in_progress_is_advisory_until_required() {
  local slug; slug="$(unique_slug legacy_marker_in_progress)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=advisory; procedures=1/2; global_code_labels=3/3; retained_headerless=1; action=partial review remains."

  local output
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}")"
  assert_match "in-progress" "${output}"

  local rc
  set +e
  bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "1" "current-gold mode must reject incomplete fractions"
}

test_legacy_retrofit_marker_missing_is_advisory_until_required() {
  local slug; slug="$(unique_slug legacy_marker_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" "No retrofit marker yet."

  bash "${LEGACY_RETROFIT_CHECK}" "${slug}" >/dev/null

  local rc
  set +e
  bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "1" "current-gold mode must require a marker"
}

test_legacy_retrofit_marker_malformed_fails_when_present() {
  local slug; slug="$(unique_slug legacy_marker_malformed)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=advisory procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=missing delimiter."

  local output rc
  set +e
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "malformed marker must fail even in advisory mode"
  assert_match "malformed legacy-retrofit-audit marker" "${output}"
}

test_legacy_retrofit_marker_must_live_in_notes_column() {
  local slug; slug="$(unique_slug legacy_marker_wrong_col)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_partial_asm "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | verify | docs_check | rework_items | notes |
|---|---|---|---|---:|---|
| 1 | legacy-retrofit-audit: semantic_claims=advisory; procedures=2/2; global_code_labels=3/3; retained_headerless=0; action=reviewed all detail rows. | pass | pass | 0 | Marker text is in the wrong column. |
EOF

  local output rc
  set +e
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "marker in a non-notes column must fail clearly"
  assert_match "legacy-retrofit-audit marker must live in the notes column" "${output}"
}

test_legacy_retrofit_marker_zero_zero_is_complete() {
  local slug; slug="$(unique_slug legacy_marker_zero)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_documented_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=advisory; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=no undocumented detail rows remained."

  local output
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require)"
  assert_match "complete" "${output}"
}

test_legacy_retrofit_required_maturity_fails_without_marker() {
  local slug; slug="$(unique_slug legacy_maturity_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_documented_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" "No retrofit marker yet."
  _enable_legacy_retrofit_required "${slug}"

  local output rc
  set +e
  output="$(bash "${PROJECT_MATURITY_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "opted-in legacy maturity must require a retrofit marker"
  assert_match "legacy current-gold assertion requires a valid legacy-retrofit-audit marker" "${output}"
  assert_match "maturity gate failed: legacy retrofit audit check failed" "${output}"
}

test_legacy_retrofit_required_maturity_accepts_valid_marker() {
  local slug; slug="$(unique_slug legacy_maturity_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_documented_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=advisory; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=no undocumented detail rows remained."
  _enable_legacy_retrofit_required "${slug}"

  local output
  output="$(bash "${PROJECT_MATURITY_CHECK}" "${slug}" 2>&1)"
  assert_match "legacy retrofit audit marker complete" "${output}"
  assert_match "OK: maturity hard gates passed" "${output}"
}

test_legacy_retrofit_marker_created_claims_requires_maturity_ledger() {
  local slug; slug="$(unique_slug legacy_marker_claims)"
  trap "cleanup_project ${slug}" EXIT
  _make_legacy_retrofit_project "${slug}"
  _write_legacy_retrofit_documented_asm "${slug}"
  _write_legacy_retrofit_scorecard "${slug}" \
    "legacy-retrofit-audit: semantic_claims=created; procedures=0/0; global_code_labels=0/0; retained_headerless=0; action=claims ledger promoted."

  local output rc
  set +e
  output="$(bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "created claims marker must require a maturity-valid ledger"
  assert_match "semantic_claims=created requires" "${output}"

  _write_valid_retrofit_claim "${slug}"
  bash "${LEGACY_RETROFIT_CHECK}" "${slug}" --require >/dev/null
}
