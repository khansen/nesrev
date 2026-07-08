#!/usr/bin/env bash
# Tests the semantic-claims ledger checker, scaffold, and maturity wiring.

SC_CHECK_PY="${REPO_ROOT}/scripts/project_semantic_claims_check.py"
SC_CHECK_SH="${REPO_ROOT}/scripts/project_semantic_claims_check.sh"
NEW_PROJECT_SH="${REPO_ROOT}/scripts/new_project.sh"
MATURITY_CHECK_SH="${REPO_ROOT}/scripts/project_maturity_check.sh"

_make_sc_project() {
  local slug="$1" required="$2"
  local root="projects/${slug}"
  cleanup_project "${slug}"
  mkdir -p \
    "${root}/asm" \
    "${root}/reference" \
    "${root}/docs/crosswalk" \
    "${root}/docs/reverse_engineering/inventory"
  cat > "${root}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="${root}/asm/${slug}.asm"
REF_NES="${root}/reference/${slug}.nes"
DOC_ROOT="${root}/docs/reverse_engineering"
SYSTEMS_DOC="${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
SEMANTIC_CLAIMS_REQUIRED="${required}"
EOF
  cat > "${root}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_FrameOamCursor .EQU $3F
Reset:
  RTS
ASM
  printf '# Memory map\n' > "${root}/docs/reverse_engineering/MEMORY_MAP.md"
}

_sc_file() { echo "projects/$1/docs/reverse_engineering/SEMANTIC_CLAIMS.md"; }
_asm_file() { echo "projects/$1/asm/$1.asm"; }

_write_valid_claim() {
  cat > "$(_sc_file "$1")" <<'MD'
# Semantic Claims

## Claim: frame-oam-cursor

Subject: ZP_FrameOamCursor
Kind: RAM/ZP field
Subsystem: rendering
Claim: per-frame OAM shadow write cursor.
Confidence: high
Evidence:
- Writers: Reset
Caveats:
- None.
Canonical docs:
- MEMORY_MAP.md
MD
}

_write_sparse_claim() {
  cat > "$(_sc_file "$1")" <<'MD'
# Semantic Claims

No claims recorded yet.
MD
}

_write_contract_test_asm() {
  local slug="$1" documented="$2"
  if [[ "${documented}" == "1" ]]; then
    cat > "$(_asm_file "${slug}")" <<'ASM'
.ORG $C000
; Boot entry that jumps through the shared helper in this fixture.
Reset:
  JSR Helper
  RTS

; Shared helper called by Reset; tiny but intentionally documented for the gate.
Helper:
  RTS
ASM
  else
    cat > "$(_asm_file "${slug}")" <<'ASM'
.ORG $C000
Reset:
  JSR Helper
  RTS

Helper:
  RTS
ASM
  fi
}

_check_rc() {
  local slug="$1" mode="$2" rc
  set +e
  python3 "${SC_CHECK_PY}" "$(_asm_file "${slug}")" "$(_sc_file "${slug}")" --mode "${mode}" >/dev/null 2>&1
  rc=$?
  set -e
  echo "${rc}"
}

_check_strict_rc() { _check_rc "$1" strict; }

test_semantic_claims_valid_claim_passes() {
  local slug; slug="$(unique_slug sc_valid)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  assert_eq "$(_check_strict_rc "${slug}")" "0" "a valid claim must pass strict"
}

test_semantic_claims_mode_parser_preserves_path_named_like_mode() {
  local dir="${NESREV_TEST_TMPDIR}/semantic_mode_path"
  mkdir -p "${dir}"
  cat > "${dir}/strict" <<'ASM'
.ORG $C000
Reset:
  RTS
ASM
  cat > "${dir}/SEMANTIC_CLAIMS.md" <<'MD'
# Semantic Claims

## Claim: reset-entry

Subject: Reset
Kind: subsystem
Subsystem: boot
Claim: reset is the boot entry point.
Confidence: high
Evidence:
- Vector target names Reset.
Caveats:
- None.
Canonical docs:
- MEMORY_MAP.md
MD
  printf '# Memory map\n' > "${dir}/MEMORY_MAP.md"

  (
    cd "${dir}"
    python3 "${SC_CHECK_PY}" strict SEMANTIC_CLAIMS.md --mode strict >/dev/null
  )
}

test_semantic_claims_global_label_subject_passes() {
  local slug; slug="$(unique_slug sc_global)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  sed -i.bak 's/Subject: ZP_FrameOamCursor/Subject: Reset/' "$(_sc_file "${slug}")"
  assert_eq "$(_check_strict_rc "${slug}")" "0" "a global label subject must pass strict"
}

test_semantic_claims_duplicate_heading_fails() {
  local slug; slug="$(unique_slug sc_dup)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  # Append a second claim with the same heading slug.
  cat >> "$(_sc_file "${slug}")" <<'MD'

## Claim: frame-oam-cursor

Subject: ZP_FrameOamCursor
Kind: RAM/ZP field
Subsystem: rendering
Claim: duplicate.
Confidence: high
Evidence:
- Writers: Reset
Caveats:
- None.
Canonical docs:
- MEMORY_MAP.md
MD
  assert_eq "$(_check_strict_rc "${slug}")" "2" "duplicate claim heading must fail"
}

test_semantic_claims_missing_field_fails() {
  local slug; slug="$(unique_slug sc_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  cat > "$(_sc_file "${slug}")" <<'MD'
# Semantic Claims

## Claim: frame-oam-cursor

Subject: ZP_FrameOamCursor
Kind: RAM/ZP field
Subsystem: rendering
Claim: missing Caveats and Canonical docs.
Confidence: high
Evidence:
- Writers: Reset
MD
  assert_eq "$(_check_strict_rc "${slug}")" "2" "missing required field must fail"
}

test_semantic_claims_empty_required_field_fails() {
  local slug; slug="$(unique_slug sc_empty_field)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  cat > "$(_sc_file "${slug}")" <<'MD'
# Semantic Claims

## Claim: frame-oam-cursor

Subject: ZP_FrameOamCursor
Kind: RAM/ZP field
Subsystem: rendering
Claim: per-frame OAM shadow write cursor.
Confidence: high
Evidence:
Caveats:
- None.
Canonical docs:
- MEMORY_MAP.md
MD
  assert_eq "$(_check_strict_rc "${slug}")" "2" \
    "empty required field must fail like a missing field"
}

test_semantic_claims_invalid_confidence_fails() {
  local slug; slug="$(unique_slug sc_conf)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  sed -i.bak 's/Confidence: high/Confidence: certain/' "$(_sc_file "${slug}")"
  assert_eq "$(_check_strict_rc "${slug}")" "2" "invalid Confidence must fail"
}

test_semantic_claims_unknown_asm_subject_fails() {
  local slug; slug="$(unique_slug sc_subj)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  sed -i.bak 's/Subject: ZP_FrameOamCursor/Subject: ZP_DoesNotExist/' "$(_sc_file "${slug}")"
  assert_eq "$(_check_strict_rc "${slug}")" "2" "subject absent from ASM must fail"
}

test_semantic_claims_lxxxx_subject_fails() {
  local slug; slug="$(unique_slug sc_lxxxx)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  sed -i.bak 's/Subject: ZP_FrameOamCursor/Subject: L1234/' "$(_sc_file "${slug}")"
  assert_eq "$(_check_strict_rc "${slug}")" "2" "raw LXXXX subject must fail"
}

test_semantic_claims_external_subject_allowed() {
  local slug; slug="$(unique_slug sc_ext)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  sed -i.bak 's@Subject: ZP_FrameOamCursor@Subject: External/reference-only@' "$(_sc_file "${slug}")"
  assert_eq "$(_check_strict_rc "${slug}")" "0" "External/reference-only subject must be allowed"
}

test_semantic_claims_bad_canonical_link_fails() {
  local slug; slug="$(unique_slug sc_link)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  sed -i.bak 's/- MEMORY_MAP.md/- NOPE_MAP.md/' "$(_sc_file "${slug}")"
  assert_eq "$(_check_strict_rc "${slug}")" "2" "unresolved local canonical-doc link must fail"
}

test_semantic_claims_legacy_missing_file_is_advisory() {
  local slug; slug="$(unique_slug sc_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"   # not opted in; no SEMANTIC_CLAIMS.md written

  local out rc
  set +e
  out="$(bash "${SC_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "0" "legacy project without the file must be advisory, not fail"
  assert_match "advisory" "${out}"
}

test_semantic_claims_optin_missing_file_fails() {
  local slug; slug="$(unique_slug sc_optin)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"   # opted in but no SEMANTIC_CLAIMS.md written

  local rc
  set +e
  bash "${SC_CHECK_SH}" "${slug}" >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "2" "opted-in project without the file must fail strict"
}

test_semantic_claims_maturity_mode_requires_at_least_one_claim() {
  local slug; slug="$(unique_slug sc_maturity_mode)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"

  _write_sparse_claim "${slug}"
  assert_eq "$(_check_rc "${slug}" strict)" "0" "sparse ledger passes pass-time strict"
  assert_eq "$(_check_rc "${slug}" maturity)" "2" "sparse ledger fails maturity mode"

  _write_valid_claim "${slug}"
  assert_eq "$(_check_rc "${slug}" maturity)" "0" "one valid claim passes maturity mode"
}

test_maturity_check_fails_optin_project_with_empty_ledger() {
  local slug; slug="$(unique_slug sc_mat_empty)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_sparse_claim "${slug}"   # file present but zero claims

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail an opted-in project whose ledger has no claims"
  fi
  assert_match "semantic-claims check failed" "${out}"
}

test_maturity_check_fails_optin_project_missing_claims_file() {
  local slug; slug="$(unique_slug sc_mat_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"   # opted in, no SEMANTIC_CLAIMS.md

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail an opted-in project with no claims file"
  fi
  assert_match "semantic-claims check failed" "${out}"
}

test_maturity_check_reports_data_extent_and_semantic_claim_failures() {
  local slug; slug="$(unique_slug sc_mat_multi_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_sparse_claim "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/inventory/data_extent_assertions.csv" <<'CSV'
label,expected_size,reason
MissingTable,1,fixture missing label should fail
CSV

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail when data extents and semantic claims both fail"
  fi
  assert_match "maturity gate failed: data extent assertions failed" "${out}"
  assert_match "maturity gate failed: semantic-claims check failed" "${out}"
}

test_maturity_check_passes_optin_project_with_valid_claim() {
  local slug; slug="$(unique_slug sc_mat_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"

  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_maturity_check_legacy_project_not_failed_by_semantic_claims() {
  local slug; slug="$(unique_slug sc_mat_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"   # legacy, no SEMANTIC_CLAIMS.md

  # Legacy project has clean raw/data here, so maturity-check should still pass:
  # the advisory semantic-claims step must not turn a legacy project red.
  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_maturity_check_fails_optin_project_with_zero_procedure_contracts() {
  local slug; slug="$(unique_slug sc_contract_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
PROCEDURE_CONTRACTS_REQUIRED="1"
EOF
  _write_contract_test_asm "${slug}" "0"

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail an opted-in project with zero procedure contracts"
  fi
  assert_match "procedure-contract audit skipped" "${out}"
}

test_maturity_check_passes_optin_project_with_procedure_contracts() {
  local slug; slug="$(unique_slug sc_contract_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
PROCEDURE_CONTRACTS_REQUIRED="1"
EOF
  _write_contract_test_asm "${slug}" "1"

  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_maturity_check_legacy_project_not_failed_by_zero_procedure_contracts() {
  local slug; slug="$(unique_slug sc_contract_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  _write_contract_test_asm "${slug}" "0"

  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_maturity_check_fails_optin_project_with_oversized_working_notes() {
  local slug; slug="$(unique_slug sc_notes_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
WORKING_NOTES_MATURITY_REQUIRED="1"
MAX_MATURITY_WORKING_NOTES_LINES="5"
EOF
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes

- One
- Two
- Three
- Four
MD

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail an opted-in project with oversized working notes"
  fi
  assert_match "working-notes pruning check failed" "${out}"
  assert_match "WORKING_NOTES.md has" "${out}"
}

test_maturity_check_passes_optin_project_with_compact_working_notes() {
  local slug; slug="$(unique_slug sc_notes_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
WORKING_NOTES_MATURITY_REQUIRED="1"
MAX_MATURITY_WORKING_NOTES_LINES="5"
EOF
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes
- Evidence gap.
MD

  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_maturity_check_accepts_leading_zero_working_notes_budget() {
  local slug; slug="$(unique_slug sc_notes_octal)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
WORKING_NOTES_MATURITY_REQUIRED="1"
MAX_MATURITY_WORKING_NOTES_LINES="08"
EOF
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes
- Evidence gap.
MD

  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_maturity_check_counts_final_line_without_trailing_newline() {
  local slug; slug="$(unique_slug sc_notes_noeol)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
WORKING_NOTES_MATURITY_REQUIRED="1"
MAX_MATURITY_WORKING_NOTES_LINES="2"
EOF
  printf '# Working Notes\n- One\n- Two' > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md"

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must count the final line even without a trailing newline"
  fi
  assert_match "has 3 lines" "${out}"
}

test_maturity_check_reports_custom_working_notes_path() {
  local slug; slug="$(unique_slug sc_notes_custom)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<EOF
WORKING_NOTES_MATURITY_REQUIRED="1"
WORKING_NOTES_FILE="projects/${slug}/docs/reverse_engineering/CUSTOM_NOTES.md"
MAX_MATURITY_WORKING_NOTES_LINES="2"
EOF
  cat > "projects/${slug}/docs/reverse_engineering/CUSTOM_NOTES.md" <<'MD'
# Custom Notes

- One
MD

  local out rc
  set +e
  out="$(bash "${MATURITY_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail an oversized custom working-notes file"
  fi
  assert_match "CUSTOM_NOTES.md has" "${out}"
}

test_maturity_check_legacy_project_not_failed_by_oversized_working_notes() {
  local slug; slug="$(unique_slug sc_notes_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes

- One
- Two
- Three
- Four
- Five
- Six
MD

  bash "${MATURITY_CHECK_SH}" "${slug}" >/dev/null
}

test_new_project_scaffolds_semantic_claims_and_passes_checker() {
  local slug; slug="$(unique_slug sc_scaffold)"
  trap "cleanup_project ${slug}" EXIT
  bash "${NEW_PROJECT_SH}" "${slug}" >/dev/null

  local sc; sc="$(_sc_file "${slug}")"
  [[ -f "${sc}" ]] || fail "new project must scaffold SEMANTIC_CLAIMS.md"
  grep -q 'SEMANTIC_CLAIMS_REQUIRED="1"' "projects/${slug}/project.conf" \
    || fail "new project must opt into strict semantic-claims maturity"
  grep -q 'PROCEDURE_CONTRACTS_REQUIRED="1"' "projects/${slug}/project.conf" \
    || fail "new project must opt into procedure-contract maturity"
  grep -q 'WORKING_NOTES_MATURITY_REQUIRED="1"' "projects/${slug}/project.conf" \
    || fail "new project must opt into working-notes maturity"
  # Scaffold references MEMORY_MAP.md, which must exist in the scaffold.
  [[ -f "projects/${slug}/docs/reverse_engineering/MEMORY_MAP.md" ]] \
    || fail "scaffold links MEMORY_MAP.md, which must be generated"
  # The scaffold (sparse, template fenced) must pass the strict checker.
  assert_eq "$(_check_strict_rc "${slug}")" "0" \
    "scaffolded SEMANTIC_CLAIMS.md must pass the strict checker while sparse"
}
