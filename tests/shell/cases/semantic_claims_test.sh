#!/usr/bin/env bash
# Tests the semantic-claims ledger checker, scaffold, and maturity wiring.

SC_CHECK_PY="${REPO_ROOT}/scripts/project_semantic_claims_check.py"
SC_CHECK_SH="${REPO_ROOT}/scripts/project_semantic_claims_check.sh"
NEW_PROJECT_SH="${REPO_ROOT}/scripts/new_project.sh"
MATURITY_CHECK_SH="${REPO_ROOT}/scripts/project_maturity_check.sh"

_make_sc_project() {
  local slug="$1" _legacy_required_argument="$2"
  local root="projects/${slug}"
  cleanup_project "${slug}"
  mkdir -p \
    "${root}/asm" \
    "${root}/reference" \
    "${root}/docs/crosswalk" \
    "${root}/docs/reverse_engineering/inventory/pass"
  cat > "${root}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="${root}/asm/${slug}.asm"
REF_NES="${root}/reference/${slug}.nes"
DOC_ROOT="${root}/docs/reverse_engineering"
SYSTEMS_DOC="${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
NESREV_RECOVERY_STATUS="none"
EOF
  cat > "${root}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_FrameOamCursor .EQU $3F
; Reset entry for the semantic-claims maturity fixture.
Reset:
  RTS
ASM
  printf '# Memory map\n' > "${root}/docs/reverse_engineering/MEMORY_MAP.md"
  printf 'source,entry,target_label,target_type,confidence,notes\n' \
    > "${root}/docs/reverse_engineering/inventory/embedded_pointer_targets.csv"
  printf 'lo_source,hi_source,entry,target_label,target_type,confidence,notes\n' \
    > "${root}/docs/reverse_engineering/inventory/split_pointer_targets.csv"
  printf 'label,expected_size,reason\n' \
    > "${root}/docs/reverse_engineering/inventory/data_extent_assertions.csv"
  cat > "${root}/docs/reverse_engineering/inventory/data_format_targets.csv" <<'CSV'
family,disposition,artifact,evidence
levels_rooms_maps,absent_not_applicable,,fixture review found no level or room data
objects_actors_enemies_hazards,absent_not_applicable,,fixture review found no actor data
items_pickups_powerups,absent_not_applicable,,fixture review found no item data
projectiles_collision,absent_not_applicable,,fixture review found no projectile data
behavior_state_movement_animation,absent_not_applicable,,fixture review found no behavior stream
metasprites_sprite_animation,absent_not_applicable,,fixture review found no sprite data
graphics_tiles_chr_nametables,absent_not_applicable,,fixture review found no graphics data
ppu_packet_update_streams,absent_not_applicable,,fixture review found no PPU stream
audio_music_jingles,absent_not_applicable,,fixture review found no music data
audio_sfx_cues,absent_not_applicable,,fixture review found no SFX data
password_save_progression,absent_not_applicable,,fixture review found no save data
CSV
  printf 'label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes\n' \
    > "${root}/docs/reverse_engineering/inventory/data_blob_dispositions.csv"
  printf '[]\n' > "${root}/docs/reverse_engineering/inventory/pass/data_coverage.json"
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
ZP_FrameOamCursor .EQU $3F
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
ZP_FrameOamCursor .EQU $3F
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

_run_maturity() {
  local slug="$1" root="projects/$1" proc_detail global_detail
  proc_detail="${NESREV_TEST_TMPDIR}/${slug}.proc"
  global_detail="${NESREV_TEST_TMPDIR}/${slug}.global"
  KPI_DETAIL_FILE="${proc_detail}" \
    bash "${REPO_ROOT}/scripts/procedure_doc_kpi.sh" "${root}/asm/${slug}.asm" >/dev/null
  KPI_DETAIL_FILE="${global_detail}" \
    bash "${REPO_ROOT}/scripts/global_code_label_doc_kpi.sh" "${root}/asm/${slug}.asm" >/dev/null
  local proc_count global_count retained_count
  proc_count="$(awk 'NF {count++} END {print count+0}' "${proc_detail}")"
  global_count="$(awk 'NF {count++} END {print count+0}' "${global_detail}")"
  retained_count="$(awk -F: 'NF {seen[$2]=1} END {for (symbol in seen) count++; print count+0}' "${proc_detail}" "${global_detail}")"
  {
    printf '%s\n' 'symbol,inventory,disposition,localization,rationale'
    awk -F: '
      FILENAME == ARGV[1] && NF {procedures[$2]=1; members[$2]=1}
      FILENAME == ARGV[2] && NF {globals[$2]=1; members[$2]=1}
      END {
        for (symbol in members) {
          inventory = (symbol in procedures) ? ((symbol in globals) ? "callable+global" : "callable") : "global"
          print symbol "," inventory ",retained_headerless,retain_global,Synthetic fixture entry retained without a header."
        }
      }
    ' "${proc_detail}" "${global_detail}" | LC_ALL=C sort
  } > "${root}/docs/reverse_engineering/inventory/policy_baseline.csv"
  cat > "${root}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<EOF
| pass_id | focus | verify | docs_check | rework_items | notes |
|---|---|---|---|---:|---|
| 1 | Fixture policy audit | pass | pass | 0 | policy-baseline-audit: semantic_claims=reviewed; procedures=${proc_count}/${proc_count}; global_code_labels=${global_count}/${global_count}; retained_headerless=${retained_count}; action=reviewed fixture detail rows. |
EOF
  bash "${MATURITY_CHECK_SH}" "${slug}"
}

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

test_semantic_claims_missing_file_fails_for_every_project() {
  local slug; slug="$(unique_slug sc_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"

  local out rc
  set +e
  out="$(bash "${SC_CHECK_SH}" "${slug}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "every project without the file must fail strict validation"
  assert_match "Every project must scaffold it" "${out}"
}

test_semantic_claims_wrapper_has_no_project_opt_in() {
  local slug; slug="$(unique_slug sc_optin)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"

  local rc
  set +e
  bash "${SC_CHECK_SH}" "${slug}" >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "2" "project without the file must fail strict"
  assert_not_match 'SEMANTIC_CLAIMS_REQUIRED' "$(<"${SC_CHECK_SH}")"
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

test_maturity_check_fails_project_with_empty_ledger() {
  local slug; slug="$(unique_slug sc_mat_empty)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_sparse_claim "${slug}"   # file present but zero claims

  local out rc
  set +e
  out="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail a project whose ledger has no claims"
  fi
  assert_match "semantic-claims check failed" "${out}"
}

test_maturity_check_fails_project_missing_claims_file() {
  local slug; slug="$(unique_slug sc_mat_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"

  local out rc
  set +e
  out="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail a project with no claims file"
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
  out="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail when data extents and semantic claims both fail"
  fi
  assert_match "maturity gate failed: data extent assertions failed" "${out}"
  assert_match "maturity gate failed: semantic-claims check failed" "${out}"
}

test_maturity_check_passes_project_with_valid_claim() {
  local slug; slug="$(unique_slug sc_mat_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"

  _run_maturity "${slug}" >/dev/null
}

test_maturity_check_every_project_requires_semantic_claims() {
  local slug; slug="$(unique_slug sc_mat_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  assert_exit 1 _run_maturity "${slug}"
}

test_maturity_check_generates_or_reuses_one_pointer_xref() {
  local slug; slug="$(unique_slug sc_mat_pointer_xref)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "1"
  _write_valid_claim "${slug}"
  printf 'source,entry,target_label,target_type,confidence,notes\n' \
    > "projects/${slug}/docs/reverse_engineering/inventory/embedded_pointer_targets.csv"
  printf 'lo_source,hi_source,entry,target_label,target_type,confidence,notes\n' \
    > "projects/${slug}/docs/reverse_engineering/inventory/split_pointer_targets.csv"

  local stub_dir="${NESREV_TEST_TMPDIR}/maturity-xasm"
  local xasm_log="${NESREV_TEST_TMPDIR}/maturity-xasm.log"
  mkdir -p "${stub_dir}"
  cat > "${stub_dir}/xasm" <<'STUB'
#!/usr/bin/env bash
set -euo pipefail
printf 'call\n' >> "${XASM_LOG}"
while (( $# > 0 )); do
  case "$1" in
    -o)
      : > "$2"
      shift 2
      ;;
    --xref=*)
      printf '{"version":"2","symbols":[],"data_directive_references":[]}\n' \
        > "${1#*=}"
      shift
      ;;
    *)
      shift
      ;;
  esac
done
STUB
  chmod +x "${stub_dir}/xasm"

  XASM_BIN="${stub_dir}/xasm" XASM_LOG="${xasm_log}" \
    _run_maturity "${slug}" >/dev/null
  assert_eq "$(wc -l < "${xasm_log}" | tr -d ' ')" "1" \
    "standalone maturity must generate one shared xref for both .DB ledgers"

  local shared_xref="${NESREV_TEST_TMPDIR}/shared-maturity-xref.json"
  printf '{"version":"2","symbols":[],"data_directive_references":[]}\n' \
    > "${shared_xref}"
  NESREV_XREF_FILE="${shared_xref}" XASM_BIN=/usr/bin/false \
    _run_maturity "${slug}" >/dev/null
}

test_maturity_check_fails_project_with_zero_procedure_contracts() {
  local slug; slug="$(unique_slug sc_contract_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  _write_contract_test_asm "${slug}" "0"
  _write_valid_claim "${slug}"

  local out rc
  set +e
  out="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail a project with zero procedure contracts"
  fi
  assert_match "procedure-contract audit skipped" "${out}"
}

test_maturity_check_passes_project_with_procedure_contracts() {
  local slug; slug="$(unique_slug sc_contract_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  _write_contract_test_asm "${slug}" "1"
  _write_valid_claim "${slug}"

  _run_maturity "${slug}" >/dev/null
}

test_maturity_check_every_project_enforces_procedure_contracts() {
  local slug; slug="$(unique_slug sc_contract_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  _write_contract_test_asm "${slug}" "0"
  _write_valid_claim "${slug}"

  local output rc
  set +e
  output="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "procedure contracts must be universal"
  assert_match "procedure-contract audit skipped" "${output}"
}

test_maturity_check_fails_project_with_oversized_working_notes() {
  local slug; slug="$(unique_slug sc_notes_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
MAX_MATURITY_WORKING_NOTES_LINES="5"
EOF
  _write_valid_claim "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes

- One
- Two
- Three
- Four
MD

  local out rc
  set +e
  out="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail a project with oversized working notes"
  fi
  assert_match "working-notes pruning check failed" "${out}"
  assert_match "WORKING_NOTES.md has" "${out}"
}

test_maturity_check_passes_project_with_compact_working_notes() {
  local slug; slug="$(unique_slug sc_notes_ok)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
MAX_MATURITY_WORKING_NOTES_LINES="5"
EOF
  _write_valid_claim "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes
- Evidence gap.
MD

  _run_maturity "${slug}" >/dev/null
}

test_maturity_check_accepts_leading_zero_working_notes_budget() {
  local slug; slug="$(unique_slug sc_notes_octal)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
MAX_MATURITY_WORKING_NOTES_LINES="08"
EOF
  _write_valid_claim "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes
- Evidence gap.
MD

  _run_maturity "${slug}" >/dev/null
}

test_maturity_check_counts_final_line_without_trailing_newline() {
  local slug; slug="$(unique_slug sc_notes_noeol)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
MAX_MATURITY_WORKING_NOTES_LINES="2"
EOF
  _write_valid_claim "${slug}"
  printf '# Working Notes\n- One\n- Two' > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md"

  local out rc
  set +e
  out="$(_run_maturity "${slug}" 2>&1)"
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
WORKING_NOTES_FILE="projects/${slug}/docs/reverse_engineering/CUSTOM_NOTES.md"
MAX_MATURITY_WORKING_NOTES_LINES="2"
EOF
  _write_valid_claim "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/CUSTOM_NOTES.md" <<'MD'
# Custom Notes

- One
MD

  local out rc
  set +e
  out="$(_run_maturity "${slug}" 2>&1)"
  rc=$?
  set -e
  if [[ "${rc}" == "0" ]]; then
    fail "maturity-check must fail an oversized custom working-notes file"
  fi
  assert_match "CUSTOM_NOTES.md has" "${out}"
}

test_maturity_check_every_project_enforces_working_notes_budget() {
  local slug; slug="$(unique_slug sc_notes_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_sc_project "${slug}" "0"
  cat >> "projects/${slug}/project.conf" <<'EOF'
MAX_MATURITY_WORKING_NOTES_LINES="5"
EOF
  _write_valid_claim "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/WORKING_NOTES.md" <<'MD'
# Working Notes

- One
- Two
- Three
- Four
- Five
- Six
MD

  assert_exit 1 _run_maturity "${slug}"
}

test_new_project_scaffolds_semantic_claims_and_passes_checker() {
  local slug; slug="$(unique_slug sc_scaffold)"
  trap "cleanup_project ${slug}" EXIT
  bash "${NEW_PROJECT_SH}" "${slug}" >/dev/null

  local sc; sc="$(_sc_file "${slug}")"
  [[ -f "${sc}" ]] || fail "new project must scaffold SEMANTIC_CLAIMS.md"
  if rg -q '_REQUIRED=' "projects/${slug}/project.conf"; then
    fail "new project must not carry per-project quality opt-ins"
  fi
  # Scaffold references MEMORY_MAP.md, which must exist in the scaffold.
  [[ -f "projects/${slug}/docs/reverse_engineering/MEMORY_MAP.md" ]] \
    || fail "scaffold links MEMORY_MAP.md, which must be generated"
  # The scaffold (sparse, template fenced) must pass the strict checker.
  assert_eq "$(_check_strict_rc "${slug}")" "0" \
    "scaffolded SEMANTIC_CLAIMS.md must pass the strict checker while sparse"
}
