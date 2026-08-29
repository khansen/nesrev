#!/usr/bin/env bash
# Tests pass lifecycle contracts exposed by the clean-room workflow.

PASS_START="${REPO_ROOT}/scripts/project_pass_start.sh"
PASS_CLOSEOUT="${REPO_ROOT}/scripts/project_pass_closeout.sh"
PASS_RESIDUE="${REPO_ROOT}/scripts/project_pass_residue_check.sh"
NEXT_PASS="${REPO_ROOT}/scripts/project_next_pass.sh"
PROCESS_CHECK="${REPO_ROOT}/scripts/project_process_check.sh"
MATURITY_SUMMARY="${REPO_ROOT}/scripts/project_maturity_summary.sh"
DRIFT_CHECK="${REPO_ROOT}/scripts/check_hardware_constant_drift.py"
RAW_ADDRESS_KPI="${REPO_ROOT}/scripts/raw_address_kpi.sh"
ASM_STYLE_DOC="${REPO_ROOT}/agent_playbook/ASM_STYLE.md"

_make_workflow_project() {
  local slug="$1" recovery_status="$2"
  local root="projects/${slug}"

  cleanup_project "${slug}"
  mkdir -p \
    "${root}/asm" \
    "${root}/build" \
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
NESREV_RECOVERY_STATUS="${recovery_status}"
OUT_BIN="${root}/build/${slug}.o"
EOF

  cat > "${root}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  RTS
ASM
  : > "${root}/reference/${slug}.nes"
  : > "${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
  cat > "${root}/docs/crosswalk/TERMINOLOGY_CROSSWALK.md" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
EOF
  : > "${root}/docs/reverse_engineering/ONBOARDING.md"
  : > "${root}/docs/reverse_engineering/QUICK_REFERENCE.md"
  printf 'old_name,new_name,reason,confidence,pass_id\n' \
    > "${root}/docs/reverse_engineering/inventory/renames.csv"
  cat > "${root}/docs/reverse_engineering/inventory/kpis.conf" <<'EOF'
MAX_ACTIVE_MAGIC_IMMEDIATES=1000
EOF
  cat > "${root}/docs/reverse_engineering/SEMANTIC_CLAIMS.md" <<'EOF'
# Semantic Claims

No claims recorded yet.
EOF
  printf 'label,expected_size,reason\n' \
    > "${root}/docs/reverse_engineering/inventory/data_extent_assertions.csv"
  cat > "${root}/docs/reverse_engineering/inventory/data_format_targets.csv" <<'EOF'
family,disposition,artifact,evidence
levels_rooms_maps,not_yet_reviewed,,fixture pending review
objects_actors_enemies_hazards,not_yet_reviewed,,fixture pending review
items_pickups_powerups,not_yet_reviewed,,fixture pending review
projectiles_collision,not_yet_reviewed,,fixture pending review
behavior_state_movement_animation,not_yet_reviewed,,fixture pending review
metasprites_sprite_animation,not_yet_reviewed,,fixture pending review
graphics_tiles_chr_nametables,not_yet_reviewed,,fixture pending review
ppu_packet_update_streams,not_yet_reviewed,,fixture pending review
audio_music_jingles,not_yet_reviewed,,fixture pending review
audio_sfx_cues,not_yet_reviewed,,fixture pending review
password_save_progression,not_yet_reviewed,,fixture pending review
EOF
  printf 'label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes\n' \
    > "${root}/docs/reverse_engineering/inventory/data_blob_dispositions.csv"
  printf 'pass_id,corridor,subject,kind,deferral,revisit_condition,status\n' \
    > "${root}/docs/reverse_engineering/inventory/deferrals.csv"
  printf 'signal,reason,pass_id\n' \
    > "${root}/docs/reverse_engineering/inventory/proof_debt_acknowledged.csv"
}

_write_pass_zero_scorecard() {
  local slug="$1"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
EOF
}

_write_pass_one_scorecard() {
  local slug="$1" notes="$2"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<EOF
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
| 1 | First corridor | 8 / 16 | 0 | not measured | 0 | 0 | 0 | pass (LXXXX gate suppressed) | pass | 0 | ${notes} |
EOF
}

_write_pass_prep_xasm_stub() {
  local stubdir="$1"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/xasm" <<'STUB'
#!/usr/bin/env bash
set -euo pipefail

printf 'CALL' >> "${XASM_LOG}"
for arg in "$@"; do
  printf '\t%s' "${arg}" >> "${XASM_LOG}"
done
printf '\n' >> "${XASM_LOG}"

write_json() {
  local path="$1" kind="$2"
  mkdir -p "$(dirname "${path}")"
  case "${kind}" in
    summary)
      printf '{"top_callables":[],"top_jump_targets":[],"top_data_labels":[]}\n' > "${path}"
      ;;
    xref)
      printf '{"version":"2","symbols":[],"references":[],"data_directive_references":[],"data_reads":[],"data_writes":[],"indirect_data_flows":[]}\n' > "${path}"
      ;;
    array)
      printf '[]\n' > "${path}"
      ;;
  esac
}

out=""
is_primary=0
while (( $# > 0 )); do
  case "$1" in
    -o)
      out="$2"
      shift 2
      ;;
    --xref-summary-output=*)
      write_json "${1#*=}" summary
      shift
      ;;
    --xref=*)
      is_primary=1
      write_json "${1#*=}" xref
      shift
      ;;
    --index-patterns-output=*|--data-consumers-output=*|--data-coverage-output=*)
      write_json "${1#*=}" array
      shift
      ;;
    *)
      shift
      ;;
  esac
done

if [[ -n "${out}" ]]; then
  mkdir -p "$(dirname "${out}")"
  : > "${out}"
fi

if [[ "${is_primary}" == "1" && "${XASM_STUB_PRIMARY_EXIT:-0}" != "0" ]]; then
  echo "stub primary failure ${XASM_STUB_PRIMARY_EXIT}" >&2
  exit "${XASM_STUB_PRIMARY_EXIT}"
fi
STUB
  chmod +x "${stubdir}/xasm"
}

_write_compare_size_xasm_stub() {
  local stubdir="$1"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/xasm" <<'STUB'
#!/usr/bin/env bash
set -euo pipefail

stub_log="${XASM_STUB_LOG:-${XASM_LOG}}"
printf 'CALL' >> "${stub_log}"
for arg in "$@"; do
  printf '\t%s' "${arg}" >> "${stub_log}"
done
printf '\n' >> "${stub_log}"

out=""
compare=""
xref=""
while (( $# > 0 )); do
  case "$1" in
    -o)
      out="$2"
      shift 2
      ;;
    --compare=*)
      compare="${1#*=}"
      shift
      ;;
    --xref=*)
      xref="${1#*=}"
      shift
      ;;
    *)
      shift
      ;;
  esac
done

if [[ -n "${compare}" ]]; then
  printf 'COMPARE_SIZE\t%s\n' "$(wc -c < "${compare}" | tr -d ' ')" >> "${stub_log}"
fi

if [[ -n "${out}" ]]; then
  mkdir -p "$(dirname "${out}")"
  python3 - "${out}" "${XASM_STUB_OUT_SIZE:-0}" <<'PY'
import sys
from pathlib import Path

Path(sys.argv[1]).write_bytes(b"\x00" * int(sys.argv[2]))
PY
fi
if [[ -n "${xref}" ]]; then
  mkdir -p "$(dirname "${xref}")"
  printf '{"version":"2","data_directive_references":[]}\n' > "${xref}"
fi
STUB
  chmod +x "${stubdir}/xasm"
}

_write_nes2_prg_high_reference() {
  local path="$1"
  python3 - "${path}" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = bytearray(b"NES\x1a" + bytes(12))
header[4] = 0
header[7] = 0x08  # NES 2.0 identifier bits.
header[9] = 0x01  # PRG-ROM size high nibble: 256 * 16 KB.
with path.open("wb") as f:
    f.write(header)
    f.truncate(16 + 256 * 16384)
PY
}

test_new_project_process_check_accepts_recorded_pass_one_analogue() {
  local slug analogue_slug
  slug="$(unique_slug analogue_recorded)"
  analogue_slug="$(unique_slug analogue_source)"
  trap "cleanup_project ${slug}; cleanup_project ${analogue_slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _make_workflow_project "${analogue_slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: ${analogue_slug} (reused the reset and NMI vocabulary; packet layout differed)."
  cat > "projects/${analogue_slug}/asm/${analogue_slug}.asm" <<'ASM'
.ORG $C000
PAD_STROBE_ON .EQU %00000001
PAD_BTN_START .EQU %00010000
Reset:
  RTS
ASM
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
PAD_STROBE_ON .EQU %00000001
ZP_JoypadHeld .EQU $16
Reset:
  LDA ZP_JoypadHeld
  AND #$10
  RTS
ASM

  local output
  output="$(bash "${PROCESS_CHECK}" "${slug}")"
  assert_match "PAD_BTN_START" "${output}" \
    "process-check should run the scorecard-selected analogue comparison"
}

test_new_project_process_check_rejects_unknown_recorded_analogue() {
  local slug; slug="$(unique_slug analogue_unknown)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: project_that_does_not_exist (claimed reuse without a resolvable project)."

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "a recorded analogue must resolve through project.conf"
  assert_match "project config not found" "${output}"
}

test_new_project_process_check_rejects_missing_pass_one_analogue() {
  local slug; slug="$(unique_slug analogue_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset and NMI corridor."

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "missing pass-1 analogue record must fail process-check"
  assert_match "pass 1 notes must record 'Analogue:" "${output}"
}

test_project_process_check_rejects_stale_generated_inventory() {
  local slug; slug="$(unique_slug process_stale_inventory)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  bash "${REPO_ROOT}/scripts/refresh_inventory.sh" "${slug}" >/dev/null
  printf '\nmanual stale edit\n' \
    >> "projects/${slug}/docs/reverse_engineering/inventory/unknowns.md"

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "stale generated inventory must fail process-check"
  assert_match "generated inventory is out of sync" "${output}"
  assert_match "unknowns.md" "${output}"
}

test_project_process_check_rejects_missing_generated_inventory() {
  local slug; slug="$(unique_slug process_missing_inventory)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  bash "${REPO_ROOT}/scripts/refresh_inventory.sh" "${slug}" >/dev/null
  rm "projects/${slug}/docs/reverse_engineering/inventory/split_pointer_targets.csv"

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "missing generated inventory must fail process-check"
  assert_match "generated inventory snapshot is missing" "${output}"
  assert_match "split_pointer_targets.csv" "${output}"
  assert_match "commit the complete generated inventory set" "${output}"
}

test_project_process_check_requires_canonical_data_format_inventory_under_set_u() {
  local slug; slug="$(unique_slug process_optional_data_format)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  local output
  output="$(bash "${PROCESS_CHECK}" "${slug}")"

  assert_match "\[data-format\] Checking data-format target inventory" "${output}"
  assert_match "OK: project process checks passed" "${output}"
}

test_project_process_check_rejects_stale_raw_ram_review_owner() {
  local slug; slug="$(unique_slug process_stale_raw_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
  LDA $10
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,OldOwner:1,
EOF

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "stale raw-RAM owner names must fail process-check"
  assert_match "raw_ram_review.csv" "${output}"
  assert_match "unknown owner symbol 'OldOwner'" "${output}"
}

test_project_process_check_accepts_scoped_local_raw_ram_review_owner() {
  local slug; slug="$(unique_slug process_scoped_raw_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
  LDA $10
@@poll:
  STA $10
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,2,1,1,1,NewOwner:1,NewOwner@@poll:1
EOF

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
}

test_project_process_check_rejects_unscoped_local_raw_ram_review_owner() {
  local slug; slug="$(unique_slug process_unscoped_raw_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
  LDA $10
@@poll:
  STA $10
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,2,1,1,1,NewOwner:1,@@poll:1
EOF

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "unscoped local owner names must fail process-check"
  assert_match "unscoped local owner symbol '@@poll'" "${output}"
  assert_match "Global@@local" "${output}"
}

test_project_process_check_allows_anonymous_local_raw_ram_review_owner() {
  local slug; slug="$(unique_slug process_anon_raw_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
@:
  LDA $10
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,@:1,
EOF

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
}

test_project_process_check_skips_inactive_raw_ram_review_owner_residue() {
  local slug; slug="$(unique_slug process_inactive_raw_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,symbolized,ZP_Done,inactive imported owner evidence,1,no,1,1,1,1,@@oldLocal:1,@:1
EOF

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
}

test_project_process_check_enforces_scorecard_lifecycle_for_imported_projects() {
  local slug; slug="$(unique_slug process_lifecycle_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | Imported latest pass | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pass | 0 | Imported history. |
| 1 | Imported stale pass | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pending | 0 | Imported history. |
EOF

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "imported scorecard lifecycle drift must fail universally"
  assert_match "non-latest pass 1 has docs_check='pending'" "${output}"
}

test_project_policy_rejects_scorecard_lifecycle_switch() {
  local slug; slug="$(unique_slug process_lifecycle_required)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  cat >> "projects/${slug}/project.conf" <<'EOF'
SCORECARD_LIFECYCLE_REQUIRED="1"
EOF
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
| 1 | First corridor | 8 / 16 | 0 | not measured | 0 | 0 | 0 | pass (LXXXX gate suppressed) | pending | 0 | Analogue: none (synthetic test fixture; no prior-project pattern applies). |
| 2 | Current pass | 7 / 14 | 0 | not measured | 0 | 0 | 0 | pending | pending | 0 | Closeout in progress. |
EOF

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "removed scorecard lifecycle switch must fail config validation"
  assert_match "SCORECARD_LIFECYCLE_REQUIRED is a removed quality-policy switch" "${output}"
}

test_project_process_check_enforces_current_pass_formatted_data_disposition() {
  local slug; slug="$(unique_slug process_formatted_data)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
; Format: two 4-byte OAM records [y, tile, attributes, x].
SmallOamTemplate:
  .DB $10,$20,$00,$30
  .DB $18,$21,$00,$38
Reset:
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'CSV'
old_name,new_name,reason,confidence,pass_id
L8123,SmallOamTemplate,two OAM records,high,1
CSV
  cat > "projects/${slug}/docs/reverse_engineering/inventory/data_blob_dispositions.csv" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
CSV

  local output rc
  set +e
  output="$(DATA_BLOB_RENAMED_PASS=1 bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" \
    "closeout-scoped process check must reject an undispositioned formatted data rename"
  assert_match "SmallOamTemplate" "${output}"
  assert_match "renamed in pass 1" "${output}"

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
}

test_raw_address_kpi_excludes_mapper_register_stores_from_absrom_count() {
  local asm="${NESREV_TEST_TMPDIR}/mapper_stores.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reset:
  STA $E000
  STX $A000
  STY $8000
  LDA $E000
  JSR $C000
  RTS
ASM

  local output
  output="$(bash "${RAW_ADDRESS_KPI}" "${asm}")"
  assert_match "strict_active_raw_absrom=2" "${output}" \
    "mapper register stores should not count as raw absolute-ROM references"
}

test_project_inventory_counts_lxxxx_definitions_and_references() {
  local slug; slug="$(unique_slug inventory_lxxxx)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
L0001:
  JSR L0002
  JSR L0002
L0002:
  JMP L0001
  RTS
ASM

  bash "${REPO_ROOT}/scripts/refresh_inventory.sh" "${slug}" >/dev/null

  grep -qF "Remaining generic hex labels (LXXXX): 2 / 5" \
    "projects/${slug}/docs/reverse_engineering/inventory/unknowns.md" \
    || fail "unknowns.md must report LXXXX definitions and total references, not matching lines"
  grep -qF "Auto-generated inventory. Prioritize these unresolved buckets:" \
    "projects/${slug}/docs/reverse_engineering/inventory/unknowns.md" \
    || fail "unknowns.md must not include a date that dirties no-op refreshes"
}

test_project_inventory_handles_unused_constant() {
  local slug; slug="$(unique_slug inventory_unused_const)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
UNUSED_TEST_CONSTANT .EQU $2A
Reset:
  RTS
ASM

  bash "${REPO_ROOT}/scripts/refresh_inventory.sh" "${slug}" >/dev/null

  grep -qF 'UNUSED_TEST_CONSTANT,$2A,misc,0' \
    "projects/${slug}/docs/reverse_engineering/inventory/constants_catalog.csv" \
    || fail "unused constants must be retained with zero usage sites"
}

test_project_inventory_reuses_one_xref_for_all_pointer_ledgers() {
  local slug; slug="$(unique_slug inventory_shared_xref)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  local xref="${NESREV_TEST_TMPDIR}/shared-xref.json"
  local out_dir="${NESREV_TEST_TMPDIR}/inventory"
  cat > "${xref}" <<'JSON'
{"version":"2","symbols":[
  {"name":"DispatchRecord","kind":"label","scope":"global","definition":{"file":"game.asm","line":10,"output_offset":0}},
  {"name":"FramePtrLoTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":20,"output_offset":2}},
  {"name":"FramePtrHiTable","kind":"label","scope":"global","definition":{"file":"game.asm","line":30,"output_offset":3}},
  {"name":"AfterTables","kind":"label","scope":"global","definition":{"file":"game.asm","line":40,"output_offset":4}}
],"data_directive_references":[
  {"file":"game.asm","line":11,"directive":".DB","width_bytes":1,"operand_index":0,"owner_symbol":"DispatchRecord","owner_item_index":0,"expression":"<DataTarget","target_projection":"low","target_kind":"data"},
  {"file":"game.asm","line":11,"directive":".DB","width_bytes":1,"operand_index":1,"owner_symbol":"DispatchRecord","owner_item_index":1,"expression":">DataTarget","target_projection":"high","target_kind":"data"},
  {"file":"game.asm","line":21,"directive":".DB","width_bytes":1,"operand_index":0,"owner_symbol":"FramePtrLoTable","owner_item_index":0,"expression":"<CodeTarget","target_projection":"low","target_kind":"code"},
  {"file":"game.asm","line":31,"directive":".DB","width_bytes":1,"operand_index":0,"owner_symbol":"FramePtrHiTable","owner_item_index":0,"expression":">CodeTarget","target_projection":"high","target_kind":"code"}
]}
JSON

  NESREV_XREF_FILE="${xref}" \
  NESREV_INVENTORY_OUT_DIR="${out_dir}" \
  XASM_BIN=/usr/bin/false \
    bash "${REPO_ROOT}/scripts/refresh_inventory.sh" "${slug}" >/dev/null

  grep -qF 'DispatchRecord,0,DataTarget,data_pointer' \
    "${out_dir}/embedded_pointer_targets.csv" \
    || fail "embedded pointer inventory must consume the wrapper-provided xref"
  grep -qF 'FramePtrLoTable,FramePtrHiTable,0,CodeTarget,code_pointer' \
    "${out_dir}/split_pointer_targets.csv" \
    || fail "split pointer inventory must consume the same wrapper-provided xref"
}

test_project_pass_prep_bundles_compatible_xasm_outputs() {
  local slug; slug="$(unique_slug pass_prep_bundle)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"
  make_ines "projects/${slug}/reference/${slug}.nes" --prg 2
  : > "projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"

  local stubdir="${NESREV_TEST_TMPDIR}/xasm_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_calls.tsv"
  _write_pass_prep_xasm_stub "${stubdir}"

  PATH="${stubdir}:${PATH}" XASM_BIN="${stubdir}/xasm" XASM_LOG="${log}" \
    bash "${REPO_ROOT}/scripts/project_pass_prep.sh" "${slug}" >/dev/null

  python3 - "${log}" "projects/${slug}/docs/reverse_engineering/inventory/pass" <<'PY'
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
pass_dir = sys.argv[2]
calls = [
    line.rstrip("\n").split("\t")[1:]
    for line in log_path.read_text(encoding="utf-8").splitlines()
]
if len(calls) != 2:
    raise SystemExit(f"expected two total xasm calls from project-pass-prep, got {len(calls)}: {calls!r}")
analysis_calls = [
    args for args in calls
    if any(arg.startswith("--xref-summary-output=") for arg in args)
]
if len(analysis_calls) != 2:
    raise SystemExit(f"expected two pass-prep analysis xasm calls, got {len(analysis_calls)}: {calls!r}")

bundle = [
    args for args in analysis_calls
    if f"--xref={pass_dir}/xref_with_data.json" in args
]
if len(bundle) != 1:
    raise SystemExit(f"expected exactly one bundled xref/data-analysis call, got {bundle!r}")
bundle = bundle[0]
for required in (
    "--compare-format=json",
    "--compare-cpu-base=$8000",
    f"--xref-summary-output={pass_dir}/xref_summary_all.json",
    f"--xref={pass_dir}/xref_with_data.json",
    f"--index-patterns-output={pass_dir}/index_patterns.json",
    f"--data-consumers-output={pass_dir}/data_consumers.json",
    f"--data-coverage-output={pass_dir}/data_coverage.json",
):
    if required not in bundle:
        raise SystemExit(f"bundled xasm call missing {required}: {bundle!r}")
if not any(arg.startswith("--compare=") for arg in bundle):
    raise SystemExit(f"bundled xasm call must include parity compare: {bundle!r}")
if any(arg.startswith("--xref-summary-include=") for arg in bundle):
    raise SystemExit(f"all-symbol bundle must not include the generic-label filter: {bundle!r}")

generic = [
    args for args in analysis_calls
    if f"--xref-summary-output={pass_dir}/xref_summary_generic.json" in args
]
if len(generic) != 1:
    raise SystemExit(f"expected exactly one generic-summary xasm call, got {generic!r}")
generic = generic[0]
if not any(arg == "--xref-summary-include=^L[0-9A-F]{4,5}$" for arg in generic):
    raise SystemExit(f"generic summary call missing LXXXX/LXXXXX include filter: {generic!r}")
if any(arg.startswith("--xref=") for arg in generic):
    raise SystemExit(f"generic summary must stay separate from owner/data xref outputs: {generic!r}")
PY
}

test_project_pass_prep_fails_non_compare_xasm_error_even_when_artifacts_exist() {
  local slug; slug="$(unique_slug pass_prep_xasm_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"
  make_ines "projects/${slug}/reference/${slug}.nes"
  : > "projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"

  local stubdir="${NESREV_TEST_TMPDIR}/xasm_fail_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_fail_calls.tsv"
  _write_pass_prep_xasm_stub "${stubdir}"

  local out="${NESREV_TEST_TMPDIR}/pass_prep_fail.stdout"
  local err="${NESREV_TEST_TMPDIR}/pass_prep_fail.stderr"
  local rc
  set +e
  PATH="${stubdir}:${PATH}" XASM_BIN="${stubdir}/xasm" XASM_LOG="${log}" \
    XASM_STUB_PRIMARY_EXIT=7 \
    bash "${REPO_ROOT}/scripts/project_pass_prep.sh" "${slug}" >"${out}" 2>"${err}"
  rc=$?
  set -e

  assert_eq "${rc}" "7" \
    "project-pass-prep must not hide non-compare xasm failures even when JSON artifacts exist"
  assert_match "stub primary failure 7" "$(cat "${err}")" \
    "fatal xasm stderr should be surfaced to the caller"

  local call_count
  call_count="$(wc -l < "${log}" | tr -d ' ')"
  assert_eq "${call_count}" "1" \
    "project-pass-prep must stop before the generic summary after fatal primary xasm failure"
}

test_project_pass_prep_rejects_truncated_reference_before_compare() {
  local slug; slug="$(unique_slug pass_prep_truncated_ref)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"
  : > "projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
  python3 - "projects/${slug}/reference/${slug}.nes" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = b"NES\x1a" + bytes([1, 1, 0, 0]) + b"\x00" * 8
path.write_bytes(header + b"\x00" * 1024)
PY

  local stubdir="${NESREV_TEST_TMPDIR}/xasm_truncated_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_truncated_calls.tsv"
  _write_pass_prep_xasm_stub "${stubdir}"

  PATH="${stubdir}:${PATH}" XASM_BIN="${stubdir}/xasm" XASM_LOG="${log}" \
    bash "${REPO_ROOT}/scripts/project_pass_prep.sh" "${slug}" >/dev/null

  python3 - \
    "${log}" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/baseline_status.json" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/compare.stderr" <<'PY'
import json
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
baseline_path = Path(sys.argv[2])
stderr_path = Path(sys.argv[3])

calls = [
    line.rstrip("\n").split("\t")[1:]
    for line in log_path.read_text(encoding="utf-8").splitlines()
]
if not calls:
    raise SystemExit("xasm should still run to generate analysis artifacts")
if any(any(arg.startswith("--compare=") for arg in args) for args in calls):
    raise SystemExit(f"truncated reference must not be passed to xasm --compare: {calls!r}")

baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
parity = baseline["checks"]["parity"]
if parity["status"] != "fail" or parity["exit_code"] != 2:
    raise SystemExit(f"truncated reference should be recorded as parity failure: {parity!r}")
if "truncated" not in stderr_path.read_text(encoding="utf-8"):
    raise SystemExit("compare.stderr should explain the truncated reference")
PY
}

test_project_pass_prep_rejects_zero_prg_reference_before_compare() {
  local slug; slug="$(unique_slug pass_prep_zero_prg_ref)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"
  : > "projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
  python3 - "projects/${slug}/reference/${slug}.nes" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = b"NES\x1a" + bytes([0, 1, 0, 0]) + b"\x00" * 8
path.write_bytes(header + b"\x00" * 8192)
PY

  local stubdir="${NESREV_TEST_TMPDIR}/xasm_zero_prg_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_zero_prg_calls.tsv"
  _write_pass_prep_xasm_stub "${stubdir}"

  PATH="${stubdir}:${PATH}" XASM_BIN="${stubdir}/xasm" XASM_LOG="${log}" \
    bash "${REPO_ROOT}/scripts/project_pass_prep.sh" "${slug}" >/dev/null

  python3 - \
    "${log}" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/baseline_status.json" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/compare.stderr" <<'PY'
import json
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
baseline_path = Path(sys.argv[2])
stderr_path = Path(sys.argv[3])

calls = [
    line.rstrip("\n").split("\t")[1:]
    for line in log_path.read_text(encoding="utf-8").splitlines()
]
if not calls:
    raise SystemExit("xasm should still run to generate analysis artifacts")
if any(any(arg.startswith("--compare=") for arg in args) for args in calls):
    raise SystemExit(f"zero-PRG reference must not be passed to xasm --compare: {calls!r}")

baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
parity = baseline["checks"]["parity"]
if parity["status"] != "fail" or parity["exit_code"] != 2:
    raise SystemExit(f"zero-PRG reference should be recorded as parity failure: {parity!r}")
if "zero PRG banks" not in stderr_path.read_text(encoding="utf-8"):
    raise SystemExit("compare.stderr should explain the zero-PRG reference")
PY
}

test_project_pass_prep_accepts_nes2_prg_high_units_before_compare() {
  local slug; slug="$(unique_slug pass_prep_nes2_prg_high)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"
  : > "projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
  _write_nes2_prg_high_reference "projects/${slug}/reference/${slug}.nes"

  local stubdir="${NESREV_TEST_TMPDIR}/xasm_nes2_prg_high_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_nes2_prg_high_calls.tsv"
  _write_pass_prep_xasm_stub "${stubdir}"

  PATH="${stubdir}:${PATH}" XASM_BIN="${stubdir}/xasm" XASM_LOG="${log}" \
    bash "${REPO_ROOT}/scripts/project_pass_prep.sh" "${slug}" >/dev/null

  python3 - \
    "${log}" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/baseline_status.json" <<'PY'
import json
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
baseline_path = Path(sys.argv[2])

calls = [
    line.rstrip("\n").split("\t")[1:]
    for line in log_path.read_text(encoding="utf-8").splitlines()
]
if not any(any(arg.startswith("--compare=") for arg in args) for args in calls):
    raise SystemExit(f"NES 2.0 PRG high-unit reference should be passed to xasm --compare: {calls!r}")

baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
parity = baseline["checks"]["parity"]
if parity["status"] != "pass" or parity["exit_code"] != 0:
    raise SystemExit(f"NES 2.0 PRG high-unit reference should be accepted for parity compare: {parity!r}")
PY
}

test_project_compare_uses_shared_nes2_prg_high_extract() {
  local slug; slug="$(unique_slug compare_nes2_prg_high)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_nes2_prg_high_reference "projects/${slug}/reference/${slug}.nes"

  local stubdir="${NESREV_TEST_TMPDIR}/xasm_compare_nes2_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_compare_nes2_calls.tsv"
  _write_compare_size_xasm_stub "${stubdir}"

  PATH="${stubdir}:${PATH}" XASM_LOG="${log}" \
    bash "${REPO_ROOT}/scripts/project_compare.sh" "${slug}" json >/dev/null

  grep -qF $'COMPARE_SIZE\t4194304' "${log}" \
    || fail "project_compare must extract the NES 2.0 high-unit PRG payload"
}

test_verify_uses_shared_nes2_prg_high_extract() {
  local asm="${NESREV_TEST_TMPDIR}/verify_nes2_prg_high.asm"
  local ref="${NESREV_TEST_TMPDIR}/verify_nes2_prg_high.nes"
  local out="${NESREV_TEST_TMPDIR}/verify_nes2_prg_high.o"
  local warnings="${NESREV_TEST_TMPDIR}/verify_nes2_warnings.txt"
  local stubdir="${NESREV_TEST_TMPDIR}/xasm_verify_nes2_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_verify_nes2_calls.tsv"

  cat > "${asm}" <<'ASM'
.ORG $C000
Reset:
  RTS
ASM
  : > "${warnings}"
  _write_nes2_prg_high_reference "${ref}"
  _write_compare_size_xasm_stub "${stubdir}"

  XASM_BIN="${stubdir}/xasm" PATH="${stubdir}:${PATH}" \
  XASM_LOG="${log}" XASM_STUB_OUT_SIZE=4194304 \
    bash "${REPO_ROOT}/scripts/verify.sh" "${asm}" "${ref}" "${out}" "${warnings}" '$C000' >/dev/null
}

test_verify_publishes_xref_v2_from_the_parity_assembly() {
  local asm="${NESREV_TEST_TMPDIR}/verify_xref.asm"
  local ref="${NESREV_TEST_TMPDIR}/verify_xref.nes"
  local out="${NESREV_TEST_TMPDIR}/verify_xref.o"
  local xref="${NESREV_TEST_TMPDIR}/published_xref.json"
  local warnings="${NESREV_TEST_TMPDIR}/verify_xref_warnings.txt"
  local stubdir="${NESREV_TEST_TMPDIR}/xasm_verify_xref_stub"
  local log="${NESREV_TEST_TMPDIR}/xasm_verify_xref_calls.tsv"

  printf '.ORG $C000\nReset: RTS\n' > "${asm}"
  : > "${warnings}"
  make_ines "${ref}"
  python3 - "${ref}" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
payload = path.read_bytes()
path.write_bytes(payload[:16] + bytes(len(payload) - 16))
PY
  _write_compare_size_xasm_stub "${stubdir}"

  XASM_BIN="${stubdir}/xasm" XASM_STUB_LOG="${log}" XASM_STUB_OUT_SIZE=16384 \
    bash "${REPO_ROOT}/scripts/verify.sh" \
      "${asm}" "${ref}" "${out}" "${warnings}" '$C000' "${xref}" >/dev/null

  assert_eq "$(wc -l < "${log}" | tr -d ' ')" "1" \
    "verification must generate pointer xref data in its parity assembly"
  assert_eq "$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["version"])' "${xref}")" "2" \
    "verification must publish the xasm v2 xref for downstream checks"
}

test_every_project_process_check_requires_analogue_record() {
  local slug; slug="$(unique_slug analogue_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Pre-contract project history."

  local output rc
  set +e
  output="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "every project must record a pass-1 analogue decision"
  assert_match "pass 1 notes must record 'Analogue:" "${output}"
}

test_pass_start_emits_selection_briefing_not_unmaintained_gate_ledger() {
  local slug; slug="$(unique_slug pass_briefing)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  printf 'FirstRetained|fixture\nSecondRetained|fixture\n' \
    > "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": {
    "type": "semantic_corridor",
    "summary": "Close the reset corridor."
  },
  "cluster_candidates": [
    {
      "cluster": "Reset corridor",
      "anchor": "Reset",
      "kind": "code",
      "members": [],
      "scope_barriers": [],
      "localize_candidates": []
    }
  ]
}
EOF

  bash "${PASS_START}" "${slug}" 1 Reset >/dev/null

  local json_path="projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json"
  local md_path="projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.md"
  python3 - "${json_path}" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
for obsolete in (
    "planned_code_changes",
    "planned_doc_changes",
    "symbols_to_add_or_rename",
    "ram_symbols_to_add",
    "known_risks",
    "gate_progress",
):
    if obsolete in payload:
        raise SystemExit(f"obsolete unmaintained plan field remains: {obsolete}")
if payload.get("selected_cluster") != "Reset corridor":
    raise SystemExit("selected corridor missing from generated briefing")
if payload.get("warning_baseline_count_at_start") != 2:
    raise SystemExit("pass start did not persist the warning-baseline count")
PY

  if rg -n '^## (Planned|Gate Progress)' "${md_path}" >/dev/null; then
    fail "generated pass briefing must not contain unmaintained plan or gate sections"
  fi
  rg -q 'Generated corridor-selection briefing' "${md_path}" \
    || fail "generated pass briefing must describe its cache role"
}

test_project_pass_closeout_computes_warning_baseline_delta() {
  local slug; slug="$(unique_slug closeout_warning_delta)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'EOF'
{
  "intended_pass_id": 1,
  "warning_baseline_count_at_start": 2,
  "corridor_objective": {}
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt" <<'EOF'
# symbol|rationale
RetainedLabel|still intentionally retained
EOF

  local stubdir="projects/${slug}/closeout_warning_stubs"
  mkdir -p "${stubdir}"
  local helper
  for helper in refresh_inventory project_pass_residue_check project_docs_check \
      project_process_check project_verify project_next_pass; do
    cat > "${stubdir}/${helper}.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
    chmod +x "${stubdir}/${helper}.sh"
  done

  PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    REWORK_ITEMS=0 FOCUS="Warning baseline fixture" \
    bash "${PASS_CLOSEOUT}" "${slug}" 1 relaxed >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

header = None
for raw in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
    cells = [cell.strip() for cell in raw.strip().strip("|").split("|")]
    if "warnings_baseline_delta" in cells:
        header = cells
        continue
    if header is None or len(cells) != len(header):
        continue
    columns = {name: idx for idx, name in enumerate(header)}
    if cells[columns["pass_id"]] == "1":
        if cells[columns["warnings_baseline_delta"]] != "-1":
            raise SystemExit(f"expected warning delta -1, got {cells!r}")
        break
else:
    raise SystemExit("pass 1 scorecard row missing")
PY

  python3 - \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" \
    "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import json
import sys
from pathlib import Path

plan_path = Path(sys.argv[1])
plan = json.loads(plan_path.read_text(encoding="utf-8"))
plan.pop("warning_baseline_count_at_start")
plan_path.write_text(json.dumps(plan) + "\n", encoding="utf-8")

scorecard_path = Path(sys.argv[2])
scorecard_path.write_text(
    scorecard_path.read_text(encoding="utf-8").replace(
        "| -1 | pass (LXXXX allowed) |",
        "| -7 | pass (LXXXX allowed) |",
    ),
    encoding="utf-8",
)
PY

  PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    REWORK_ITEMS=0 FOCUS="Warning baseline fixture" \
    bash "${PASS_CLOSEOUT}" "${slug}" 1 relaxed >/dev/null 2>&1

  assert_match "\| -7 \| pass \(LXXXX allowed\) \|" \
    "$(cat "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md")" \
    "legacy closeout without a start snapshot must preserve the existing delta"
}

_write_reset_next_pass() {
  local slug="$1"
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "semantic_corridor", "summary": "Close the reset corridor." },
  "cluster_candidates": [
    { "cluster": "Reset corridor", "anchor": "Reset", "kind": "code", "members": [], "scope_barriers": [], "localize_candidates": [] }
  ]
}
EOF
}

test_pass_start_persists_explicit_corridor_objective_fields() {
  local slug; slug="$(unique_slug pass_objective_fields)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_reset_next_pass "${slug}"

  local err
  err="$(CORRIDOR="Reset/boot corridor" WHY_NOW="boot path unnamed" \
    BOUNDARIES="Reset..NMI" EVIDENCE="next_pass cluster Reset" \
    OUT_OF_SCOPE="audio driver" \
    bash "${PASS_START}" "${slug}" 1 Reset 2>&1 >/dev/null)"

  if [[ "${err}" == *"corridor objective incomplete"* ]]; then
    fail "complete corridor objective must not warn: ${err}"
  fi

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
objective = plan.get("corridor_objective")
expected = {
    "selected_corridor": "Reset/boot corridor",
    "why_now": "boot path unnamed",
    "expected_boundaries": "Reset..NMI",
    "generated_evidence": "next_pass cluster Reset",
    "explicitly_out_of_scope": "audio driver",
}
if objective != expected:
    raise SystemExit(f"corridor_objective not persisted as expected: {objective!r}")
PY

  local md_path="projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.md"
  rg -q "^## Corridor Objective$" "${md_path}" \
    || fail "markdown plan must include a Corridor Objective section"
  rg -q "Selected corridor: Reset/boot corridor" "${md_path}" \
    || fail "markdown plan must render the selected corridor"
  rg -q "Explicitly out of scope: audio driver" "${md_path}" \
    || fail "markdown plan must render the out-of-scope field"
}

test_pass_start_snapshots_generated_localization_owners() {
  local slug; slug="$(unique_slug pass_localization_snapshot)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "semantic_corridor", "summary": "Close the owner corridor." },
  "cluster_candidates": [
    {
      "cluster": "Owner corridor",
      "anchor": "OldOwner",
      "kind": "code",
      "members": [],
      "scope_barriers": [],
      "localize_candidates": [
        { "symbol": "OldDone", "definition_owner": "OldOwner", "safe_localize": true },
        { "symbol": "UniqueLoop", "definition_owner": "OldOwner", "safe_localize": true }
      ]
    },
    {
      "cluster": "Conflicting owner corridor",
      "anchor": "OtherOwner",
      "kind": "code",
      "members": [],
      "scope_barriers": [],
      "localize_candidates": [
        { "symbol": "OldDone", "definition_owner": "OtherOwner", "safe_localize": true }
      ]
    }
  ]
}
EOF

  bash "${PASS_START}" "${slug}" 1 OldOwner >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
expected = [{"symbol": "UniqueLoop", "owner": "OldOwner"}]
if plan.get("localization_owner_snapshot") != expected:
    raise SystemExit(
        "generated localization owner snapshot was not persisted: "
        f"{plan.get('localization_owner_snapshot')!r}"
    )
PY
}

test_pass_start_refuses_unsafe_xref_localization_owners() {
  local slug; slug="$(unique_slug pass_xref_localization_refusals)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared conservative localization-owner evidence."

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "symbols": [
    {"name":"EarlierDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":2}},
    {"name":"OldOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":5}},
    {"name":"OtherOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":15}},
    {"name":"LateOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":30}},
    {"name":"SafeDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":40}},
    {"name":"CalledRoutine","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":41}},
    {"name":"CrossFileDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":42}},
    {"name":"ConflictedDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":43}},
    {"name":"MissingOwnerDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":44}},
    {"name":"LocalScopeDone","kind":"label","scope":"local","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":45}},
    {"name":"DataKindDone","kind":"data","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":46}},
    {"name":"MalformedLineDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":"unknown"}},
    {"name":"ExternalOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/other.asm","line":1}}
  ],
  "references": [
    {"symbol":"SafeDone","file":"projects/${slug}/asm/${slug}.asm","line":6,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"CalledRoutine","file":"projects/${slug}/asm/${slug}.asm","line":7,"opcode":"JSR","access":"call","owner_routine":"OldOwner"},
    {"symbol":"CrossFileDone","file":"projects/${slug}/asm/${slug}.asm","line":8,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"CrossFileDone","file":"projects/${slug}/asm/other.asm","line":2,"opcode":"BNE","access":"jump","owner_routine":"ExternalOwner"},
    {"symbol":"EarlierDone","file":"projects/${slug}/asm/${slug}.asm","line":31,"opcode":"BNE","access":"jump","owner_routine":"LateOwner"},
    {"symbol":"ConflictedDone","file":"projects/${slug}/asm/${slug}.asm","line":9,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"ConflictedDone","file":"projects/${slug}/asm/${slug}.asm","line":16,"opcode":"BNE","access":"jump","owner_routine":"OtherOwner"},
    {"symbol":"MissingOwnerDone","file":"projects/${slug}/asm/${slug}.asm","line":10,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"MissingOwnerDone","file":"projects/${slug}/asm/${slug}.asm","line":11,"opcode":"BEQ","access":"jump"},
    {"symbol":"LocalScopeDone","file":"projects/${slug}/asm/${slug}.asm","line":12,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"DataKindDone","file":"projects/${slug}/asm/${slug}.asm","line":13,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"MalformedLineDone","file":"projects/${slug}/asm/${slug}.asm","line":14,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"}
  ]
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": {"type":"semantic_corridor","summary":"Close the owner corridor."},
  "cluster_candidates": [
    {
      "cluster":"Owner corridor",
      "anchor":"OldOwner",
      "kind":"code",
      "members":[],
      "scope_barriers":[],
      "localize_candidates":[]
    }
  ]
}
EOF

  bash "${PASS_START}" "${slug}" 1 OldOwner >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
expected = [{"symbol": "SafeDone", "owner": "OldOwner"}]
if plan.get("localization_owner_snapshot") != expected:
    raise SystemExit(
        "unsafe full-xref localization owner was not refused: "
        f"{plan.get('localization_owner_snapshot')!r}"
    )
PY
}

test_pass_start_snapshots_xref_owners_for_opportunistic_localization() {
  local slug; slug="$(unique_slug pass_xref_localization_snapshot)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Localized branch targets across the selected corridor."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
EarlierDone:
  RTS

OldOwner:
  BNE OldMid
  BNE ConflictedDone
  BNE CrossFileDone
OldMid:
  BEQ OldDone
OldDone:
  LDA $10
  JSR CalledRoutine
  RTS

OtherOldOwner:
  BNE OtherOldDone
  BNE ConflictedDone
OtherOldDone:
  LDA $11
  RTS

ConflictedDone:
  RTS

CrossFileDone:
  RTS

LateOwner:
  BNE EarlierDone
  RTS

CalledRoutine:
  RTS
ASM
  cat > "projects/${slug}/asm/other.asm" <<'ASM'
ExternalOwner:
  BNE CrossFileDone
  RTS
ASM

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "symbols": [
    {"name":"EarlierDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":2}},
    {"name":"OldOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":5}},
    {"name":"OldMid","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":9}},
    {"name":"OldDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":11}},
    {"name":"OtherOldOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":16}},
    {"name":"OtherOldDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":19}},
    {"name":"ConflictedDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":23}},
    {"name":"CrossFileDone","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":26}},
    {"name":"LateOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":29}},
    {"name":"CalledRoutine","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":33}},
    {"name":"ExternalOwner","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/other.asm","line":1}}
  ],
  "references": [
    {"symbol":"OldMid","file":"projects/${slug}/asm/${slug}.asm","line":6,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"OldDone","file":"projects/${slug}/asm/${slug}.asm","line":10,"opcode":"BEQ","access":"jump","owner_routine":"OldMid"},
    {"symbol":"OtherOldDone","file":"projects/${slug}/asm/${slug}.asm","line":17,"opcode":"BNE","access":"jump","owner_routine":"OtherOldOwner"},
    {"symbol":"ConflictedDone","file":"projects/${slug}/asm/${slug}.asm","line":7,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"ConflictedDone","file":"projects/${slug}/asm/${slug}.asm","line":18,"opcode":"BNE","access":"jump","owner_routine":"OtherOldOwner"},
    {"symbol":"CrossFileDone","file":"projects/${slug}/asm/${slug}.asm","line":8,"opcode":"BNE","access":"jump","owner_routine":"OldOwner"},
    {"symbol":"CrossFileDone","file":"projects/${slug}/asm/other.asm","line":2,"opcode":"BNE","access":"jump","owner_routine":"ExternalOwner"},
    {"symbol":"EarlierDone","file":"projects/${slug}/asm/${slug}.asm","line":30,"opcode":"BNE","access":"jump","owner_routine":"LateOwner"},
    {"symbol":"CalledRoutine","file":"projects/${slug}/asm/${slug}.asm","line":13,"opcode":"JSR","access":"call","owner_routine":"OldDone"}
  ]
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": {"type":"semantic_corridor","summary":"Close the owner corridor."},
  "cluster_candidates": [
    {
      "cluster":"Owner corridor",
      "anchor":"OldOwner",
      "kind":"code",
      "members":[],
      "scope_barriers":[],
      "localize_candidates":[]
    }
  ]
}
EOF

  bash "${PASS_START}" "${slug}" 1 OldOwner >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
expected = [
    {"symbol": "OldDone", "owner": "OldOwner"},
    {"symbol": "OldMid", "owner": "OldOwner"},
    {"symbol": "OtherOldDone", "owner": "OtherOldOwner"},
]
if plan.get("localization_owner_snapshot") != expected:
    raise SystemExit(
        "full-xref localization owner snapshot was not persisted: "
        f"{plan.get('localization_owner_snapshot')!r}"
    )
PY

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
EarlierDone:
  RTS

NewOwner:
  BNE @@mid
  BNE ConflictedDone
  BNE CrossFileDone
@@mid:
  BEQ @@done
@@done:
  LDA $10
  JSR CalledRoutine
  RTS

OtherNewOwner:
  BNE @@done
  BNE ConflictedDone
@@done:
  LDA $11
  RTS

ConflictedDone:
  RTS

CrossFileDone:
  RTS

LateOwner:
  BNE EarlierDone
  RTS

CalledRoutine:
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
OldOwner,NewOwner,owner routine renamed,high,1
OldMid,@@mid,localized intermediate branch,mechanical,1
OldDone,@@done,localized nested branch,mechanical,1
OtherOldOwner,OtherNewOwner,second owner routine renamed,high,1
OtherOldDone,@@done,localized repeated branch name,mechanical,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,OldDone:1,
0x0011,unreviewed,,,,yes,1,1,1,0,OtherOldDone:1,
EOF

  bash "${PASS_RESIDUE}" "${slug}" 1 >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

if rows["0x0010"]["top_readers"] != "NewOwner:1":
    raise SystemExit(f"nested localized owner was not reconciled: {rows['0x0010']!r}")
if rows["0x0011"]["top_readers"] != "OtherNewOwner:1":
    raise SystemExit(f"repeated localized owner was not reconciled: {rows['0x0011']!r}")
PY
}

test_pass_start_snapshots_scoped_raw_ram_owners_for_repeated_local_names() {
  local slug; slug="$(unique_slug pass_raw_owner_scope_snapshot)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Localized self-loop owners under repeated concise names."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Start:
  JSR L8000
  JSR L8010
  RTS

L8000:
L8001:
L8002:
  LDA $10
  BNE L8002
  RTS

L8010:
L8011:
L8012:
  LDA $11
  BNE L8012
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "symbols": [
    {"name":"Start","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":2}},
    {"name":"L8000","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":7}},
    {"name":"L8001","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":8}},
    {"name":"L8002","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":9}},
    {"name":"L8010","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":14}},
    {"name":"L8011","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":15}},
    {"name":"L8012","kind":"label","scope":"global","definition":{"file":"projects/${slug}/asm/${slug}.asm","line":16}}
  ],
  "references": [
    {"symbol":"L8000","file":"projects/${slug}/asm/${slug}.asm","line":3,"opcode":"JSR","access":"call","owner_routine":"Start"},
    {"symbol":"L8010","file":"projects/${slug}/asm/${slug}.asm","line":4,"opcode":"JSR","access":"call","owner_routine":"Start"},
    {"symbol":"L8001","file":"projects/${slug}/asm/${slug}.asm","line":7,"opcode":"BNE","access":"branch","owner_routine":"L8000"},
    {"symbol":"L8002","file":"projects/${slug}/asm/${slug}.asm","line":11,"opcode":"BNE","access":"branch","owner_routine":"L8002"},
    {"symbol":"L8011","file":"projects/${slug}/asm/${slug}.asm","line":14,"opcode":"BNE","access":"branch","owner_routine":"L8010"},
    {"symbol":"L8012","file":"projects/${slug}/asm/${slug}.asm","line":18,"opcode":"BNE","access":"branch","owner_routine":"L8012"}
  ]
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,L8002:1,
0x0011,unreviewed,,,,yes,1,1,1,0,L8012:1,
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": {"type":"semantic_corridor","summary":"Close both self-loop owner corridors."},
  "cluster_candidates": [
    {
      "cluster":"Self-loop owner corridors",
      "anchor":"L8000",
      "kind":"code",
      "members":[],
      "scope_barriers":[],
      "localize_candidates":[]
    }
  ]
}
EOF

  bash "${PASS_START}" "${slug}" 1 L8000 >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
expected = [
    {"symbol": "L8001", "owner": "L8000"},
    {"symbol": "L8002", "owner": "L8001"},
    {"symbol": "L8011", "owner": "L8010"},
    {"symbol": "L8012", "owner": "L8011"},
]
if plan.get("raw_ram_owner_scope_snapshot") != expected:
    raise SystemExit(
        "scoped raw-RAM owner snapshot was not persisted: "
        f"{plan.get('raw_ram_owner_scope_snapshot')!r}"
    )
unsafe = {item.get("symbol") for item in plan.get("localization_owner_snapshot", [])}
if unsafe.intersection({"L8002", "L8012"}):
    raise SystemExit("self-owned loops must not become localization permissions")
PY

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Start:
  JSR NewOwner
  JSR OtherNewOwner
  RTS

NewOwner:
@@mid:
@@done:
  LDA $10
  BNE @@done
  RTS

OtherNewOwner:
@@mid:
@@done:
  LDA $11
  BNE @@done
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
L8000,NewOwner,renamed first owner routine,high,1
L8001,@@mid,localized first intermediate branch,mechanical,1
L8002,@@done,localized first self-loop,mechanical,1
L8010,OtherNewOwner,renamed second owner routine,high,1
L8011,@@mid,localized second intermediate branch,mechanical,1
L8012,@@done,localized second self-loop,mechanical,1
EOF

  local plan_path="projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json"
  local saved_plan="${NESREV_TEST_TMPDIR}/raw-owner-scope-plan.json"
  cp "${plan_path}" "${saved_plan}"
  python3 - "${plan_path}" <<'PY'
import json
import sys

path = sys.argv[1]
plan = json.load(open(path, encoding="utf-8"))
plan.pop("raw_ram_owner_scope_snapshot", None)
with open(path, "w", encoding="utf-8") as handle:
    json.dump(plan, handle)
    handle.write("\n")
PY

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e
  assert_eq "${rc}" "4" \
    "removing the scoped raw-RAM owner snapshot must restore duplicate-local ambiguity"
  assert_match "ambiguous_local_replacements" "${out}"

  cp "${saved_plan}" "${plan_path}"
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e
  assert_eq "${rc}" "0" \
    "scoped raw-RAM owner evidence must reconcile both repeated local names"

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

if rows["0x0010"]["top_readers"] != "NewOwner:1":
    raise SystemExit(f"first scoped local owner was not reconciled: {rows['0x0010']!r}")
if rows["0x0011"]["top_readers"] != "OtherNewOwner:1":
    raise SystemExit(f"second scoped local owner was not reconciled: {rows['0x0011']!r}")
PY
}

test_pass_start_warns_on_incomplete_corridor_objective_but_succeeds() {
  local slug; slug="$(unique_slug pass_objective_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_reset_next_pass "${slug}"

  local err rc
  set +e
  err="$(bash "${PASS_START}" "${slug}" 1 Reset 2>&1 >/dev/null)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "incomplete corridor objective must warn, not fail"
  assert_match "corridor objective incomplete" "${err}" \
    "pass-start must warn when objective fields are omitted"

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
objective = plan.get("corridor_objective")
if objective is None:
    raise SystemExit("corridor_objective key must exist for backward-compatible shape")
if any(objective.values()):
    raise SystemExit(f"omitted objective must persist empty strings, got {objective!r}")
PY

  rg -q "\(not recorded\)" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.md" \
    || fail "markdown plan must mark unrecorded objective fields"
}

test_pass_start_target_notes_plan_still_works() {
  local slug; slug="$(unique_slug pass_notes_plan)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_reset_next_pass "${slug}"

  bash "${PASS_START}" "${slug}" 1 notes_plan >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
if plan.get("anchor_source") != "notes_plan":
    raise SystemExit(f"notes_plan anchor_source not preserved: {plan.get('anchor_source')!r}")
if plan.get("anchor_kind") != "notes_plan":
    raise SystemExit(f"notes_plan anchor_kind not preserved: {plan.get('anchor_kind')!r}")
if "corridor_objective" not in plan:
    raise SystemExit("corridor_objective key must exist even for notes_plan")
PY
}

test_project_next_pass_refreshes_missing_or_stale_pass_cache() {
  local slug; slug="$(unique_slug next_pass_autoprep)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"

  local prep_stub="projects/${slug}/prep_stub.sh"
  cat > "${prep_stub}" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
slug="$1"
root="projects/${slug}/docs/reverse_engineering"
pass_dir="${root}/inventory/pass"
mkdir -p "${pass_dir}"
printf 'prep %s raw_write=%s\n' \
  "${slug}" "${PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW:-unset}" \
  > "${pass_dir}/prep_stub.log"
cat > "${pass_dir}/baseline_status.json" <<'JSON'
{"checks":{"docs_check":{"status":"pass"},"process_check":{"status":"pass"},"parity":{"status":"pass"}},"metrics":{"lxxxx_definitions":0,"lxxxx_occurrences":0,"strict_active_raw_lowaddr":0}}
JSON
cat > "${pass_dir}/xref_summary_all.json" <<'JSON'
{"top_callables":[],"top_jump_targets":[],"top_data_labels":[]}
JSON
cat > "${pass_dir}/xref_summary_generic.json" <<'JSON'
{"top_callables":[],"top_jump_targets":[],"top_data_labels":[]}
JSON
cat > "${pass_dir}/xref_with_data.json" <<'JSON'
{"version":"2","symbols":[],"references":[],"data_directive_references":[],"data_reads":[],"data_writes":[]}
JSON
cat > "${pass_dir}/data_consumers.json" <<'JSON'
[]
JSON
cat > "${pass_dir}/data_coverage.json" <<'JSON'
[]
JSON
cat > "${pass_dir}/index_patterns.json" <<'JSON'
[]
JSON
SH

  local out err
  err="projects/${slug}/next_pass.err"
  out="$(PROJECT_NEXT_PASS_PREP_SCRIPT="${prep_stub}" bash "${NEXT_PASS}" "${slug}" json 2>"${err}")"

  rg -q "refreshing missing, partial, or stale pass cache" "${err}" \
    || fail "project-next-pass must report automatic pass-cache refresh on stderr"
  rg -q "prep ${slug} raw_write=0" "projects/${slug}/docs/reverse_engineering/inventory/pass/prep_stub.log" \
    || fail "project-next-pass must invoke the prep wrapper when cache files are missing"
  python3 - "${out}" "${slug}" <<'PY'
import json
import sys

payload = json.loads(sys.argv[1])
slug = sys.argv[2]
if payload.get("project") != slug:
    raise SystemExit(f"project-next-pass did not emit clean JSON for {slug}: {payload!r}")
if payload.get("baseline", {}).get("parity") != "pass":
    raise SystemExit(f"auto-refreshed baseline cache was not consumed: {payload!r}")
PY

  rm "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_summary_generic.json"
  rm "projects/${slug}/docs/reverse_engineering/inventory/pass/prep_stub.log"
  out="$(PROJECT_NEXT_PASS_PREP_SCRIPT="${prep_stub}" bash "${NEXT_PASS}" "${slug}" json 2>"${err}")"

  rg -q "refreshing missing, partial, or stale pass cache" "${err}" \
    || fail "project-next-pass must report automatic refresh for a partial pass cache"
  rg -q "prep ${slug} raw_write=0" "projects/${slug}/docs/reverse_engineering/inventory/pass/prep_stub.log" \
    || fail "project-next-pass must invoke prep when a required cache input is missing"
}

test_pass_start_rejects_missing_next_pass_with_next_pass_instruction() {
  local slug; slug="$(unique_slug pass_start_missing_next)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  local output rc
  set +e
  output="$(bash "${PASS_START}" "${slug}" 1 Reset 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "pass-start must fail when next_pass.json is missing"
  assert_match "missing" "${output}"
  assert_match "make project-next-pass PROJECT=${slug}" "${output}"
  if [[ "${output}" == *"project-pass-prep"* ]]; then
    fail "pass-start missing-briefing error should point to project-next-pass, not pass-prep"
  fi
}

test_pass_start_rejects_stale_next_pass_after_source_edit() {
  local slug; slug="$(unique_slug pass_start_stale_next)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_reset_next_pass "${slug}"

  python3 - \
    "projects/${slug}/asm/${slug}.asm" \
    "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'PY'
import os
import sys

asm_path, next_pass_path = sys.argv[1:]
newer = os.stat(next_pass_path).st_mtime + 60
os.utime(asm_path, (newer, newer))
PY

  local output rc
  set +e
  output="$(bash "${PASS_START}" "${slug}" 1 Reset 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "pass-start must fail when next_pass.json is stale"
  assert_match "stale relative" "${output}"
  assert_match "asm/${slug}.asm" "${output}"
  assert_match "make project-next-pass PROJECT=${slug}" "${output}"
  if [[ -e "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" ]]; then
    fail "pass-start must not write a current pass plan from stale next-pass evidence"
  fi
}

test_project_pass_closeout_creates_row_runs_gates_and_marks_scorecard() {
  local slug; slug="$(unique_slug pass_closeout_full)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"

  local stubdir="projects/${slug}/closeout_stubs"
  local log="projects/${slug}/closeout.log"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_residue_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'residue %s %s\n' "$1" "$2" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ -n "${NESREV_XREF_FILE:-}" && -f "${NESREV_XREF_FILE}" ]] \
  || { echo "inventory did not receive the verification xref" >&2; exit 98; }
printf 'inventory %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_next_pass.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'raw_refresh %s auto_prep=%s raw_write=%s refresh_only=%s format=%s\n' \
  "$1" \
  "${PROJECT_NEXT_PASS_AUTO_PREP:-unset}" \
  "${PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW:-unset}" \
  "${PROJECT_NEXT_PASS_RAW_RAM_REFRESH_ONLY:-unset}" \
  "${2:-unset}" \
  >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_pass_prep.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
echo "project-pass-closeout must not run full project-pass-prep for raw-RAM refresh" >&2
exit 99
SH
  cat > "${stubdir}/project_docs_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'docs %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_process_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ -n "${NESREV_XREF_FILE:-}" && -f "${NESREV_XREF_FILE}" ]] \
  || { echo "process check did not receive the verification xref" >&2; exit 98; }
printf 'process %s data_blob_pass=%s\n' "$1" "${DATA_BLOB_RENAMED_PASS:-unset}" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_verify.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${EXPECT_RELAXED:-0}" == "1" && "${ALLOW_UNRESOLVED_LXXXX:-}" != "1" ]]; then
  echo "expected relaxed verify environment" >&2
  exit 99
fi
[[ -n "${NESREV_XREF_FILE:-}" ]] \
  || { echo "closeout did not request a shared verification xref" >&2; exit 98; }
mkdir -p "$(dirname "${NESREV_XREF_FILE}")"
printf '{"version":"2","data_directive_references":[]}\n' > "${NESREV_XREF_FILE}"
printf 'verify %s %s\n' "$1" "${ALLOW_UNRESOLVED_LXXXX:-}" >> "${STUB_LOG}"
[[ "${PROJECT_VERIFY_REFRESH_INVENTORY:-0}" == "1" ]] \
  || { echo "closeout did not request inventory refresh inside verification" >&2; exit 98; }
bash "${PROJECT_VERIFY_REFRESH_SCRIPT}" "$1"
SH

  STUB_LOG="${log}" EXPECT_RELAXED=1 PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    FOCUS="Closeout wrapper corridor" \
    NOTES="Closed the closeout wrapper corridor." \
    bash "${PASS_CLOSEOUT}" "${slug}" 1 relaxed >/dev/null

  cat > "projects/${slug}/expected_closeout.log" <<EOF
verify ${slug} 1
inventory ${slug}
residue ${slug} 1
docs ${slug}
process ${slug} data_blob_pass=1
raw_refresh ${slug} auto_prep=0 raw_write=1 refresh_only=1 format=json
docs ${slug}
process ${slug} data_blob_pass=1
EOF
  cmp -s "projects/${slug}/expected_closeout.log" "${log}" \
    || fail "project-pass-closeout must verify once, then share analysis through inventory, process, and final refresh gates"

  python3 - "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
rows = []
for raw in path.read_text(encoding="utf-8").splitlines():
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if cells and cells[0].isdigit():
        rows.append(cells)
row = next((r for r in rows if r[0] == "1"), None)
if row is None:
    raise SystemExit("project-pass-closeout did not create pass 1 scorecard row")
if row[1] != "Closeout wrapper corridor":
    raise SystemExit(f"unexpected focus: {row[1]!r}")
if row[8] != "pass (LXXXX allowed)" or row[9] != "pass":
    raise SystemExit(f"gate cells not marked after successful closeout: {row!r}")
if row[11] != "Closed the closeout wrapper corridor.":
    raise SystemExit(f"notes were not preserved: {row[11]!r}")
PY
}

test_project_pass_closeout_marks_scorecard_by_header_name() {
  local slug; slug="$(unique_slug pass_closeout_header)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | review_state | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---:|---|
| 0 | Existing setup row | 0 / 0 | 0 | not measured | 0 | 0 | 0 | keep-zero | pass | pass | 0 | pass_id |
| 1 | Existing closeout row | 0 / 0 | 0 | not measured | 0 | 0 | 0 | keep-me | pending | pending | pending | Existing row should be marked in place. |
EOF

  local stubdir="projects/${slug}/closeout_stubs"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_residue_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_next_pass.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_docs_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_process_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_verify.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH

  PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    bash "${PASS_CLOSEOUT}" "${slug}" 1 strict >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = None
row = None
header_cols = None
required = {"pass_id", "notes", "verify", "docs_check", "rework_items"}
for raw in path.read_text(encoding="utf-8").splitlines():
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if required.issubset(set(cells)):
        header = cells
        header_cols = {name: i for i, name in enumerate(header)}
    elif header and len(cells) == len(header) and cells[header_cols["pass_id"]] == "1":
        row = cells
        break
if header is None or row is None:
    raise SystemExit("header-driven scorecard fixture was not preserved")
cols = {name: i for i, name in enumerate(header)}
if row[cols["review_state"]] != "keep-me":
    raise SystemExit(f"extra column was overwritten: {row!r}")
if row[cols["verify"]] != "pass":
    raise SystemExit(f"verify column was not marked by name: {row!r}")
if row[cols["docs_check"]] != "pass":
    raise SystemExit(f"docs_check column was not marked by name: {row!r}")
if row[cols["rework_items"]] != "pending":
    raise SystemExit(f"rework_items column was not preserved by name: {row!r}")
PY
}

test_make_pass_closeout_rerun_repairs_pending_rework_before_process_check() {
  local slug; slug="$(unique_slug pass_closeout_rework_rerun)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---:|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
| 1 | Existing closed row | 8 / 16 | 0 | not measured | 0 | 0 | 0 | pass | pass | pending | First closeout stopped after marking gates. |
EOF

  local stubdir="projects/${slug}/closeout_stubs"
  local log="projects/${slug}/closeout.log"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_residue_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'residue %s %s\n' "$1" "$2" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'inventory %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_next_pass.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'raw_refresh %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_docs_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'docs %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_process_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
python3 - "projects/$1/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = None
for raw in path.read_text(encoding="utf-8").splitlines():
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if {"pass_id", "verify", "docs_check", "rework_items"}.issubset(set(cells)):
        header = cells
        continue
    if header is None or len(cells) != len(header):
        continue
    cols = {name: i for i, name in enumerate(header)}
    if cells[cols["pass_id"]] == "1" and cells[cols["rework_items"]].lower() == "pending":
        raise SystemExit("pending rework reached process check")
PY
printf 'process %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_verify.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'verify %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/deferral_capture.py" <<'PY'
import os
import sys

explicit = ""
if "--explicit" in sys.argv:
    explicit = sys.argv[sys.argv.index("--explicit") + 1]
with open(os.environ["STUB_LOG"], "a", encoding="utf-8") as handle:
    handle.write(f"deferrals {explicit}\n")
PY

  local deferrals
  deferrals=$'object_$40 :: inspect $40-$5F consumers :: static\nsecond_$AA :: inspect $AA writer :: runtime'
  STUB_LOG="${log}" PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    make project-pass-closeout PROJECT="${slug}" PASS=1 \
      REWORK_ITEMS=2 "DEFERRALS=${deferrals}" >/dev/null

  assert_match 'deferrals object_[$]40 :: inspect [$]40-[$]5F consumers :: static' "$(cat "${log}")" \
    "Makefile must forward DEFERRALS to project-pass-closeout"
  assert_match 'second_[$]AA :: inspect [$]AA writer :: runtime' "$(cat "${log}")" \
    "Makefile must preserve multiline DEFERRALS values"

  python3 - "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = None
row = None
for raw in path.read_text(encoding="utf-8").splitlines():
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if {"pass_id", "verify", "docs_check", "rework_items"}.issubset(set(cells)):
        header = cells
        continue
    if header is None or len(cells) != len(header):
        continue
    cols = {name: i for i, name in enumerate(header)}
    if cells[cols["pass_id"]] == "1":
        row = cells
        break
if row is None:
    raise SystemExit("pass 1 row missing after closeout rerun")
cols = {name: i for i, name in enumerate(header)}
if row[cols["verify"]] != "pass" or row[cols["docs_check"]] != "pass":
    raise SystemExit(f"gate cells were not preserved as closed: {row!r}")
if row[cols["rework_items"]] != "2":
    raise SystemExit(f"REWORK_ITEMS was not repaired before process check: {row!r}")
PY
}

test_project_pass_closeout_external_script_uses_declared_repo_root() {
  local slug; slug="$(unique_slug pass_closeout_external_root)"
  local target_repo="${NESREV_TEST_TMPDIR}/target_repo"
  mkdir -p "${target_repo}"
  git -C "${target_repo}" init -q
  local target_repo_real
  target_repo_real="$(cd "${target_repo}" && pwd -P)"

  (
    cd "${target_repo}"
    _make_workflow_project "${slug}" "none"
    cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---:|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
| 1 | Existing closed row | 8 / 16 | 0 | not measured | 0 | 0 | 0 | pass | pass | pending | First closeout stopped after marking gates. |
EOF
  )

  local stubdir="${NESREV_TEST_TMPDIR}/external_stubs"
  local log="${target_repo}/projects/${slug}/external_closeout.log"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_residue_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'residue %s %s cwd=%s\n' "$1" "$2" "$(pwd)" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'inventory %s cwd=%s\n' "$1" "$(pwd)" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_next_pass.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'raw_refresh %s cwd=%s\n' "$1" "$(pwd)" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_docs_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'docs %s cwd=%s\n' "$1" "$(pwd)" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_process_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
python3 - "projects/$1/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = None
for raw in path.read_text(encoding="utf-8").splitlines():
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if {"pass_id", "verify", "docs_check", "rework_items"}.issubset(set(cells)):
        header = cells
        continue
    if header is None or len(cells) != len(header):
        continue
    cols = {name: i for i, name in enumerate(header)}
    if cells[cols["pass_id"]] == "1" and cells[cols["rework_items"]].lower() == "pending":
        raise SystemExit("pending rework reached process check")
PY
printf 'process %s cwd=%s\n' "$1" "$(pwd)" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_verify.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'verify %s cwd=%s\n' "$1" "$(pwd)" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/deferral_capture.py" <<'PY'
import os
import sys

explicit = ""
if "--explicit" in sys.argv:
    explicit = sys.argv[sys.argv.index("--explicit") + 1]
with open(os.environ["STUB_LOG"], "a", encoding="utf-8") as handle:
    handle.write(f"deferrals {explicit} cwd={os.getcwd()}\n")
PY
  chmod +x "${stubdir}"/*.sh

  STUB_LOG="${log}" PROJECT_PASS_CLOSEOUT_REPO_ROOT="${target_repo}" \
    PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    REWORK_ITEMS=2 DEFERRALS=external_gap:static:revisit \
    bash "${PASS_CLOSEOUT}" "${slug}" 1 relaxed >/dev/null

  local target_scorecard="${target_repo}/projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"
  assert_match "cwd=${target_repo_real}" "$(cat "${log}")" \
    "external closeout helpers must run from the declared target repo root"
  assert_match "deferrals external_gap:static:revisit" "$(cat "${log}")" \
    "external closeout must still forward DEFERRALS"
  assert_match "\\| 1 \\| Existing closed row .*\\| pass \\(LXXXX allowed\\) \\| pass \\| 2 \\|" \
    "$(cat "${target_scorecard}")" \
    "external closeout must repair the target repo scorecard"
  if [[ -e "projects/${slug}" ]]; then
    fail "external closeout wrote project files in the tool repo"
  fi
}

test_project_pass_closeout_materializes_missing_row_from_existing_header() {
  local slug; slug="$(unique_slug pass_closeout_materialize)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| focus | pass_id | review_state | notes | verify | docs_check | rework_items | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta |
|---|---|---|---|---|---|---:|---|---|---|---|---|---|
| Existing setup row | 0 | keep-zero | pass_id | pass | pass | 0 | 0 / 0 | 0 | not measured | 0 | 0 | 0 |
EOF

  local stubdir="projects/${slug}/closeout_stubs"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_residue_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_next_pass.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_docs_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_process_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/project_verify.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH

  local notes
  notes=$'Preserved runner\'s $AA note.\nSecond $BB line.'
  PROJECT_PASS_CLOSEOUT_SCRIPT_DIR="${stubdir}" \
    make project-pass-closeout PROJECT="${slug}" PASS=1 VERIFY_MODE=strict \
      'FOCUS=Object $40-$5F corridor' \
      "NOTES=${notes}" >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
header = None
row = None
header_cols = None
required = {"pass_id", "notes", "verify", "docs_check", "rework_items"}
for raw in path.read_text(encoding="utf-8").splitlines():
    stripped = raw.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        continue
    cells = [c.strip() for c in stripped.strip("|").split("|")]
    if required.issubset(set(cells)):
        header = cells
        header_cols = {name: i for i, name in enumerate(header)}
    elif (
        header
        and len(cells) == len(header)
        and not all(cell.startswith("---") for cell in cells)
        and cells[header_cols["pass_id"]] == "1"
    ):
        row = cells
        break
if header is None or row is None:
    raise SystemExit("missing pass row was not materialized")
if len(row) != len(header):
    raise SystemExit(f"materialized row/header mismatch: {row!r} vs {header!r}")
cols = {name: i for i, name in enumerate(header)}
expected = {
    "pass_id": "1",
    "focus": "Object $40-$5F corridor",
    "review_state": "",
    "notes": "Preserved runner's $AA note. Second $BB line.",
    "verify": "pass",
    "docs_check": "pass",
    "rework_items": "pending",
    "labels_remaining": "0 / 0",
}
for name, value in expected.items():
    if row[cols[name]] != value:
        raise SystemExit(f"{name} = {row[cols[name]]!r}, expected {value!r}; row={row!r}")
PY
}

test_make_pass_start_preserves_raw_objective_values() {
  local slug; slug="$(unique_slug pass_objective_raw_values)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_reset_next_pass "${slug}"

  # Exercise the Makefile forwarding path: apostrophes, single dollar signs,
  # and embedded newlines must reach the pass plan literally.
  local corridor
  corridor=$'runner\'s $40-$5F path-state corridor\nsecond $BB line'
  make project-pass-start PROJECT="${slug}" PASS=1 TARGET=Reset \
    "CORRIDOR=${corridor}" \
    'WHY_NOW=shared $AA sentinel is still ambiguous' \
    'BOUNDARIES=$40-$5F and its direct owners' \
    'EVIDENCE=raw_$0040 generated evidence' \
    'OUT_OF_SCOPE=$60-$7F scratch window' >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
got = plan.get("corridor_objective")
expected = {
    "selected_corridor": "runner's $40-$5F path-state corridor\nsecond $BB line",
    "why_now": "shared $AA sentinel is still ambiguous",
    "expected_boundaries": "$40-$5F and its direct owners",
    "generated_evidence": "raw_$0040 generated evidence",
    "explicitly_out_of_scope": "$60-$7F scratch window",
}
if got != expected:
    raise SystemExit(f"Makefile forwarding mangled raw objective values: {got!r}")
PY
}

test_make_pass_start_normalizes_raw_ram_target_shorthand() {
  local slug; slug="$(unique_slug pass_raw_target_norm)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "raw_ram_corridor", "summary": "Close raw RAM byte $00BF." },
  "cluster_candidates": [
    {
      "cluster": "raw_$00BF corridor",
      "anchor": "raw_$00BF",
      "kind": "raw_ram_corridor",
      "members": [
        {"addr_hex": "raw_$00BF", "symbol": "ZP_TestByte", "site_count": 4}
      ],
      "scope_barriers": [],
      "localize_candidates": []
    }
  ]
}
EOF

  local target
  for target in raw_bf raw_0bf raw_00bf 'raw_$00bf'; do
    make project-pass-start PROJECT="${slug}" PASS=1 TARGET="${target}" >/dev/null 2>&1
    python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" "${target}" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
source_target = sys.argv[2]
if plan.get("anchor_source") != "cluster_candidate":
    raise SystemExit(f"{source_target}: expected cluster_candidate, got {plan.get('anchor_source')!r}")
if plan.get("anchor_target") != "raw_$00BF":
    raise SystemExit(f"{source_target}: expected raw_$00BF, got {plan.get('anchor_target')!r}")
PY
  done
}

_write_pass_plan_objective() {
  # $1=slug $2=intended_pass_id $3..$7 = the five objective field values
  local slug="$1" pass_id="$2"
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<EOF
{
  "intended_pass_id": ${pass_id},
  "corridor_objective": {
    "selected_corridor": "$3",
    "why_now": "$4",
    "expected_boundaries": "$5",
    "generated_evidence": "$6",
    "explicitly_out_of_scope": "$7"
  }
}
EOF
}

test_project_pass_closeout_rejects_missing_plan_without_explicit_pass() {
  local slug; slug="$(unique_slug closeout_missing_plan_full)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"

  local output rc
  set +e
  output="$(bash "${PASS_CLOSEOUT}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "closeout must reject inferred pass without current_pass_plan.json"
  assert_match "current_pass_plan.json missing" "${output}"
  assert_match "project-next-pass" "${output}"
  assert_match "project-pass-start" "${output}"
  if [[ -e "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" ]]; then
    fail "closeout must not create a pass plan when the operator skipped pass-start"
  fi
}

test_project_pass_closeout_rejects_inferred_already_closed_pass() {
  local slug; slug="$(unique_slug closeout_closed_plan_full)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  _write_pass_plan_objective "${slug}" 1 \
    "Reset corridor" "boot path unnamed" "Reset..NMI" "cluster Reset" "audio driver"

  local output rc
  set +e
  output="$(bash "${PASS_CLOSEOUT}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "closeout must not infer and restamp an already-closed pass"
  assert_match "pass 1" "${output}"
  assert_match "already closed" "${output}"
  assert_match "project-next-pass" "${output}"
  assert_match "project-pass-start" "${output}"
  assert_match "PASS=1" "${output}"
}

test_pass_residue_check_reports_complete_corridor_objective_without_warning() {
  local slug; slug="$(unique_slug closeout_obj_complete)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  _write_pass_plan_objective "${slug}" 1 \
    "Reset corridor" "boot path unnamed" "Reset..NMI" "cluster Reset" "audio driver"
  printf 'local scratch\n' > "projects/${slug}/PROCESS_FRICTION.md"
  mkdir -p "projects/${slug}/mods/local_probe"
  printf 'local mod\n' > "projects/${slug}/mods/local_probe/README.md"
  printf '# Runtime Evidence\n' > "projects/${slug}/docs/reverse_engineering/RUNTIME_EVIDENCE.md"

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "clean closeout with a complete objective must succeed"
  assert_match '"corridor_objective_status": "complete"' "${out}" \
    "closeout summary must report the persisted objective status"
  assert_match "Reset corridor" "${out}" \
    "closeout summary must surface the persisted corridor objective"
  assert_match "docs/reverse_engineering/RUNTIME_EVIDENCE.md" "${out}" \
    "closeout authored_diff_paths must include untracked authored project docs"
  if [[ "${out}" == *"corridor objective was incomplete"* ]]; then
    fail "complete objective must not trigger the incomplete warning"
  fi
  if [[ "${out}" == *"no persisted corridor objective"* ]]; then
    fail "present objective must not trigger the missing warning"
  fi
  if [[ "${out}" == *"PROCESS_FRICTION.md"* || "${out}" == *"mods/local_probe"* ]]; then
    fail "closeout authored_diff_paths must ignore untracked scratch and local mods"
  fi
}

test_pass_residue_check_warns_on_incomplete_objective_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_incomplete)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  _write_pass_plan_objective "${slug}" 1 "Reset corridor" "" "" "" ""

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "incomplete objective must warn, not fail, on an otherwise clean pass"
  assert_match "corridor objective was incomplete" "${out}" \
    "closeout must warn when the persisted objective was incomplete at pass start"
  assert_match '"corridor_objective_status": "incomplete"' "${out}" \
    "closeout summary must report the incomplete objective status"
}

test_pass_residue_check_warns_when_objective_missing_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  # No current_pass_plan.json is written.

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "missing objective must warn, not fail, on an otherwise clean pass"
  assert_match "no persisted corridor objective found" "${out}" \
    "closeout must warn when no objective was persisted"
  assert_match '"corridor_objective_status": "missing"' "${out}" \
    "closeout summary must report the missing objective status"
}

test_pass_residue_check_warns_on_stale_plan_objective_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_stale)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  # Plan was written for a different pass id than the one being closed out.
  _write_pass_plan_objective "${slug}" 2 \
    "Other corridor" "later pass" "later" "later" "later"

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "stale plan objective must warn, not fail, on an otherwise clean pass"
  assert_match "persisted corridor objective is for pass 2" "${out}" \
    "closeout must warn when the plan objective belongs to another pass"
  assert_match '"corridor_objective_status": "stale_plan"' "${out}" \
    "closeout summary must report the stale_plan objective status"
}

test_pass_residue_check_warns_on_unparseable_plan_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_invalid)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  printf '{ this is not valid json' \
    > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json"

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "an unparseable plan must warn, not crash closeout"
  assert_match "current_pass_plan.json could not be parsed" "${out}" \
    "closeout must warn when the plan cache is malformed"
  assert_match '"corridor_objective_status": "invalid_plan"' "${out}" \
    "closeout summary must report the invalid_plan objective status"
}

test_pass_residue_check_ignores_archived_review_history() {
  local slug; slug="$(unique_slug closeout_review_archive)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named the reset helper."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
RunResetHelper:
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
L1234,RunResetHelper,named reset helper,medium,1
EOF
  mkdir -p "projects/${slug}/docs/reverse_engineering/reviews"
  cat > "projects/${slug}/docs/reverse_engineering/reviews/pass-0.md" <<'EOF'
Verdict: APPROVED

Historical review text named `L1234` before the next pass renamed it.
EOF

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "archived review provenance must not block later closeout residue checks"
  if [[ "${out}" == *"\"file\": \"projects/${slug}/docs/reverse_engineering/reviews/pass-0.md\""* ]]; then
    fail "residue check must skip archived pass review records"
  fi
}

test_pass_residue_check_rejects_stale_old_symbols_in_normal_docs() {
  local slug; slug="$(unique_slug closeout_doc_residue)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named the reset helper."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
RunResetHelper:
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
L1234,RunResetHelper,named reset helper,medium,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/ONBOARDING.md" <<'EOF'
This normal project doc still mentions `L1234`.
EOF

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "4" "normal docs must still reject stale old-symbol residue"
  assert_match "ONBOARDING.md" "${out}"
  assert_match "L1234" "${out}"
}

test_project_maturity_summary_reports_blockers_inventory_and_clusters() {
  local slug; slug="$(unique_slug maturity_summary)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the first gameplay corridor."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  LDA $30
  STA ($10),Y
  LDA ($11,X)
  LDA [$12,X]
  LDA [$13],Y
  LDA #5
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "cluster_candidates": [
    {"anchor":"FocusedActionable","kind":"raw_ram_corridor","why":"4 actionable sites","mixed_anchor":false},
    {"anchor":"BroadMixedSetup","kind":"raw_ram_corridor","why":"broad mixed reset block","mixed_anchor":true}
  ],
  "alternative_candidates": [{"label":"ViewProjectionTable","kind":"data_label","why":"data-label debt; 12 refs"}]
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x00a4,deferred,,mixed role,7,yes,2,1,1,1,X:1,X:1
EOF

  local out rc
  set +e
  out="$(bash "${MATURITY_SUMMARY}" "${slug}")"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "maturity summary must be advisory and exit 0"
  assert_match "Hard blockers" "${out}"
  assert_match "raw low-address operands: 5" "${out}" \
    "hard blockers must report the canonical raw low-address count"
  assert_match "noncompliant data labels: 0" "${out}"
  assert_match "Soft review inventory" "${out}"
  assert_match "raw indirect operands: 2" "${out}" \
    "raw-indirect inventory must include bracketed xasm operands and ignore parenthesized operands"
  assert_match "review inventory, not a zero target" "${out}" \
    "callable/global-label counts must be framed as review inventory"
  assert_match "Recent pass yield" "${out}"
  assert_match "Top actionable candidate corridors" "${out}"
  assert_match "FocusedActionable" "${out}"
  assert_match "ViewProjectionTable" "${out}"
  assert_match "Deferred / mixed clusters" "${out}"
  assert_match "BroadMixedSetup \[mixed-anchor evidence\]" "${out}" \
    "mixed anchors must remain visible as context in the dashboard"
  assert_match "0x00a4" "${out}" "deferred raw-RAM bytes must appear as context"
  assert_match "Reminder: callable/global-label counts are review inventories" "${out}"
}

test_project_maturity_summary_reports_newest_passes_from_newest_first_scorecard() {
  local slug; slug="$(unique_slug maturity_newest)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  # Newest-first scorecard: the
  # dashboard must report the highest pass ids, not the first physical rows.
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 7 | Corridor07 | 1 / 9 | 0 | not measured | 1 | 0 | 0 | pass | pass | 0 | newest. |
| 6 | Corridor06 | 2 / 9 | 0 | not measured | 2 | 0 | 0 | pass | pass | 0 | x. |
| 5 | Corridor05 | 3 / 9 | 0 | not measured | 3 | 0 | 0 | pass | pass | 0 | x. |
| 4 | Corridor04 | 4 / 9 | 0 | not measured | 4 | 0 | 0 | pass | pass | 0 | x. |
| 3 | Corridor03 | 5 / 9 | 0 | not measured | 5 | 0 | 0 | pass | pass | 0 | x. |
| 2 | Corridor02 | 6 / 9 | 0 | not measured | 6 | 0 | 0 | pass | pass | 0 | x. |
| 1 | Corridor01 | 7 / 9 | 0 | not measured | 7 | 0 | 0 | pass | pass | 0 | oldest. |
EOF

  local out
  out="$(bash "${MATURITY_SUMMARY}" "${slug}")"

  assert_match "Corridor07" "${out}" "newest pass must appear in recent yield"
  assert_match "Corridor03" "${out}" "fifth-newest pass must appear in recent yield"
  if [[ "${out}" == *"Corridor01"* ]]; then
    fail "oldest pass must not appear when newer passes exist"
  fi
  if [[ "${out}" == *"Corridor02"* ]]; then
    fail "second-oldest pass must not appear when newer passes exist"
  fi
}

test_make_project_maturity_summary_target_runs() {
  local slug; slug="$(unique_slug maturity_summary_make)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed a corridor."

  local out
  out="$(make project-maturity-summary PROJECT="${slug}" 2>&1)"
  assert_match "Maturity summary: ${slug}" "${out}" \
    "make target must run the dashboard"
}

test_hardware_drift_check_flags_noncanonical_hardware_prefixed_equ() {
  local asm="${NESREV_TEST_TMPDIR}/drift.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
PPUCTRL            .EQU $2000
PPUCTRL_NMI_ENABLE .EQU %10000000
PPUCTRL_INIT_VALUE .EQU %10010000
RAM_OamShadowBase  .EQU $0200
Reset:
  RTS
ASM

  local out
  out="$(python3 "${DRIFT_CHECK}" "${asm}" "${ASM_STYLE_DOC}" "${NESREV_TEST_TMPDIR}/no_allowlist.txt")"

  assert_match "warn: 1 project-local" "${out}" \
    "exactly one non-canonical hardware-prefixed constant must be flagged"
  assert_match "PPUCTRL_INIT_VALUE" "${out}"
  # canonical names and non-prefix symbols must not be flagged
  if [[ "${out}" == *"RAM_OamShadowBase"* ]]; then
    fail "a non-prefixed symbol must not be flagged"
  fi
  if [[ "${out}" == *"PPUCTRL_NMI_ENABLE"* ]]; then
    fail "a canonical constant must not be flagged"
  fi
  assert_match "rename to a canonical constant" "${out}"
  assert_match "allowlist" "${out}"
}

test_hardware_drift_check_allowlist_suppresses_local_composite() {
  local asm="${NESREV_TEST_TMPDIR}/drift2.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
PPUCTRL_INIT_VALUE .EQU %10010000
Reset:
  RTS
ASM
  local allow="${NESREV_TEST_TMPDIR}/allow.txt"
  printf '# project-local composites\nPPUCTRL_INIT_VALUE\n' > "${allow}"

  local out
  out="$(python3 "${DRIFT_CHECK}" "${asm}" "${ASM_STYLE_DOC}" "${allow}")"
  assert_match "OK: no canonical hardware-constant drift" "${out}" \
    "an allowlisted local composite must not be flagged"
}

test_hardware_drift_check_reports_allowlisted_cross_project_recurrence() {
  local root="${NESREV_TEST_TMPDIR}/hardware_projects"
  local current="${root}/current"
  local peer="${root}/peer"
  local unrelated="${root}/unrelated"
  mkdir -p \
    "${current}/asm" "${current}/docs/reverse_engineering/inventory" \
    "${peer}/asm" "${peer}/docs/reverse_engineering/inventory" \
    "${unrelated}/asm" "${unrelated}/docs/reverse_engineering/inventory"

  cat > "${current}/asm/current.asm" <<'ASM'
.ORG $C000
APU_LOCAL_EXACT .EQU $08
APU_LOCAL_VALUE .EQU $30
APU_LOCAL_EXPR .EQU APU_LOCAL_EXACT+1
OAM_PAGE_HI .EQU $02
OAM_CURRENT_LOCAL .EQU $03
Reset:
  RTS
ASM
  cat > "${current}/docs/reverse_engineering/inventory/hardware_local_allowlist.txt" <<'EOF'
APU_LOCAL_EXACT
APU_LOCAL_VALUE
APU_LOCAL_EXPR
OAM_PAGE_HI
OAM_CURRENT_LOCAL
EOF
  cat > "${peer}/asm/peer.asm" <<'ASM'
.ORG $C000
APU_LOCAL_EXACT .EQU $08
APU_PEER_VALUE .EQU $30
APU_PEER_EXPR .EQU APU_LOCAL_EXACT+1
OAM_PAGE_HI .EQU $03
OAM_PEER_LOCAL .EQU $02
Reset:
  RTS
ASM
  cat > "${peer}/docs/reverse_engineering/inventory/hardware_local_allowlist.txt" <<'EOF'
APU_LOCAL_EXACT
APU_PEER_VALUE
APU_PEER_EXPR
OAM_PAGE_HI
OAM_PEER_LOCAL
EOF
  cat > "${unrelated}/asm/unrelated.asm" <<'ASM'
.ORG $C000
PPUMASK_UNRELATED_VALUE .EQU $30
Reset:
  RTS
ASM
  printf 'PPUMASK_UNRELATED_VALUE\n' \
    > "${unrelated}/docs/reverse_engineering/inventory/hardware_local_allowlist.txt"

  local allow="${current}/docs/reverse_engineering/inventory/hardware_local_allowlist.txt"
  local out rc
  set +e
  out="$(python3 "${DRIFT_CHECK}" "${current}/asm/current.asm" \
    "${ASM_STYLE_DOC}" "${allow}" --projects-root "${root}" --strict)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" \
    "allowlisted recurrence must remain advisory even in strict drift mode"
  assert_match "OK: no canonical hardware-constant drift" "${out}"
  assert_match "advisory: 2 allowlisted project-local hardware constant" "${out}" \
    "exact-name and compatible value recurrence must both be reported"
  assert_match "APU_LOCAL_EXACT: exact-name in peer" "${out}"
  assert_match 'APU_LOCAL_VALUE: same APU_ literal [$]30 as peer:APU_PEER_VALUE' "${out}"
  if [[ "${out}" == *"OAM_PAGE_HI"* ]]; then
    fail "a canonical current name must not match a noncanonical peer candidate"
  fi
  if [[ "${out}" == *"OAM_CURRENT_LOCAL"* ]]; then
    fail "a noncanonical current name must not match a canonical peer candidate"
  fi
  if [[ "${out}" == *"APU_LOCAL_EXPR"* ]]; then
    fail "expression-valued constants must not enter literal recurrence evidence"
  fi
  if [[ "${out}" == *"PPUMASK_UNRELATED_VALUE"* ]]; then
    fail "same-valued constants from another hardware family must not be reported"
  fi
}

test_hardware_drift_check_flags_ppu_register_bit_near_misses_only() {
  local asm="${NESREV_TEST_TMPDIR}/ppu_near_miss.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
PPU_NAMETABLE_X_BIT .EQU %00000001
PPU_NAMETABLE_2400_BIT .EQU %00000001
PPU_NAMETABLE_2400_CLEAR_MASK .EQU %11111110
PPU_NAMETABLE_2400_HI .EQU $24
PPU_NAMETABLE_PAGE_COUNT .EQU 4
Reset:
  RTS
ASM

  local out
  out="$(python3 "${DRIFT_CHECK}" "${asm}" "${ASM_STYLE_DOC}" "${NESREV_TEST_TMPDIR}/none.txt")"
  assert_match "warn: 3 project-local" "${out}" \
    "register-bit near misses must be visible without flagging PPU data constants"
  assert_match "PPU_NAMETABLE_X_BIT" "${out}"
  assert_match "PPU_NAMETABLE_2400_BIT" "${out}"
  assert_match "PPU_NAMETABLE_2400_CLEAR_MASK" "${out}"
  if [[ "${out}" == *"PPU_NAMETABLE_2400_HI"* || "${out}" == *"PPU_NAMETABLE_PAGE_COUNT"* ]]; then
    fail "PPU address and quantity constants must remain outside hardware-bit drift"
  fi
}

test_hardware_drift_check_accepts_promoted_cross_project_constants() {
  local asm="${NESREV_TEST_TMPDIR}/promoted_hardware.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
RAM_OamShadowBase .EQU $0200
OAM_PAGE_HI .EQU >RAM_OamShadowBase
PPUCTRL_NAMETABLE_2400 .EQU %00000001
PPUCTRL_NAMETABLE_SELECT_MASK .EQU %00000011
PPUCTRL_NAMETABLE_CLEAR_MASK .EQU ~PPUCTRL_NAMETABLE_SELECT_MASK
ZAPPER_TRIGGER_BIT .EQU %00010000
ZAPPER_LIGHT_BIT .EQU %00001000
Reset:
  RTS
ASM

  local out
  out="$(python3 "${DRIFT_CHECK}" "${asm}" "${ASM_STYLE_DOC}" "${NESREV_TEST_TMPDIR}/none.txt")"
  assert_match "OK: no canonical hardware-constant drift" "${out}" \
    "promoted names must not require project-local allowlist entries"

  local style
  style="$(cat "${ASM_STYLE_DOC}")"
  assert_match 'ZAPPER_TRIGGER_BIT.*%00010000' "${style}" \
    "the shared trigger bit must be in the canonical table"
  assert_match 'ZAPPER_LIGHT_BIT.*%00001000' "${style}" \
    "the shared light-sensor bit must be in the canonical table"
  assert_match 'PPUMASK_HIDE_SPRITES_MASK.*~PPUMASK_SHOW_SPRITES' "${style}" \
    "single-bit clear masks must derive from their positive bit"
  assert_match 'PPUMASK_RENDER_DISABLE_MASK.*~PPUMASK_RENDER_ENABLE_MASK' "${style}" \
    "compound clear masks must derive from their positive mask"
}

test_hardware_drift_check_strict_mode_exits_nonzero_on_drift() {
  local asm="${NESREV_TEST_TMPDIR}/drift3.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
APU_CUSTOM_LOCAL .EQU $05
Reset:
  RTS
ASM
  local rc
  set +e
  python3 "${DRIFT_CHECK}" "${asm}" "${ASM_STYLE_DOC}" "${NESREV_TEST_TMPDIR}/none.txt" --strict >/dev/null 2>&1
  rc=$?
  set -e
  assert_eq "${rc}" "3" "strict mode must exit non-zero when drift remains"
}

test_process_check_reports_hardware_drift_advisory_without_failing() {
  local slug; slug="$(unique_slug hw_drift_process)"
  local peer; peer="$(unique_slug hw_drift_peer)"
  trap "cleanup_project ${slug}; cleanup_project ${peer}" EXIT
  _make_workflow_project "${slug}" "none"
  _make_workflow_project "${peer}" "none"
  _write_pass_one_scorecard "${slug}" \
    "Analogue: none (synthetic test fixture; no prior-project pattern applies)."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
APU_CUSTOM_LOCAL .EQU $05
APU_SHARED_LOCAL .EQU $08
Reset:
  RTS
ASM
  printf 'APU_SHARED_LOCAL\n' \
    > "projects/${slug}/docs/reverse_engineering/inventory/hardware_local_allowlist.txt"
  cat > "projects/${peer}/asm/${peer}.asm" <<'ASM'
.ORG $C000
APU_SHARED_LOCAL .EQU $08
Reset:
  RTS
ASM
  printf 'APU_SHARED_LOCAL\n' \
    > "projects/${peer}/docs/reverse_engineering/inventory/hardware_local_allowlist.txt"

  local out rc
  set +e
  out="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "hardware-drift check must be advisory and not fail process-check"
  assert_match "canonical hardware-constant drift \(advisory\)" "${out}"
  assert_match "APU_CUSTOM_LOCAL" "${out}"
  assert_match "APU_SHARED_LOCAL: exact-name in ${peer}" "${out}" \
    "process check must surface cross-project allowlist recurrence evidence"
  assert_match "OK: project process checks passed" "${out}"
}

test_next_pass_text_frames_output_as_candidate_evidence() {
  local slug; slug="$(unique_slug next_candidate_wording)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Deferred a wider owner corridor; use operator judgment before selecting generated evidence."

  local output
  output="$(bash "${NEXT_PASS}" "${slug}" text)"

  assert_match "Operator selection required" "${output}" \
    "next-pass text must make pass selection the operator's responsibility"
  assert_match "Generated evidence buckets" "${output}" \
    "next-pass text must frame generated results as evidence buckets"
  assert_match "Top generated evidence bucket:" "${output}" \
    "next-pass text must not present the top generated bucket as a default pass"
  assert_match "Work-based operator signals:" "${output}" \
    "next-pass text must surface authored pass-outcome signals before generated evidence"
  if [[ "${output}" == *"Recommended next pass:"* ]]; then
    fail "next-pass text must not present its default as an authoritative recommendation"
  fi
  if [[ "${output}" == *"Default candidate pass:"* ]]; then
    fail "next-pass text must not present generated evidence as a default candidate pass"
  fi

  # The recommended_pass JSON key must survive for backward compatibility.
  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
if "recommended_pass" not in payload:
    raise SystemExit("recommended_pass key must be preserved for compatibility")
if "type" not in payload["recommended_pass"]:
    raise SystemExit("recommended_pass.type must be preserved for compatibility")
if payload["recommended_pass"].get("role") != "generated_evidence_bucket":
    raise SystemExit("recommended_pass must be explicitly classified as a generated evidence bucket")
if not payload.get("operator_guidance", {}).get("selection_required"):
    raise SystemExit("operator_guidance.selection_required must be true")
if not payload.get("operator_signals"):
    raise SystemExit("operator_signals must include latest pass outcome evidence")
PY
}

test_next_pass_surfaces_static_plateau_after_consecutive_doc_closure() {
  local slug; slug="$(unique_slug next_plateau)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"

  local pass_dir="projects/${slug}/docs/reverse_engineering/inventory/pass"
  cat > "${pass_dir}/baseline_status.json" <<'JSON'
{"checks":{"docs_check":{"status":"pass"},"process_check":{"status":"pass"},"parity":{"status":"pass"}},"metrics":{"lxxxx_definitions":0,"lxxxx_occurrences":0,"strict_active_raw_lowaddr":0}}
JSON
  cat > "${pass_dir}/xref_summary_all.json" <<'JSON'
{"top_callables":[],"top_jump_targets":[],"top_data_labels":[]}
JSON
  cat > "${pass_dir}/xref_summary_generic.json" <<'JSON'
{"top_callables":[],"top_jump_targets":[],"top_data_labels":[]}
JSON
  cat > "${pass_dir}/xref_with_data.json" <<'JSON'
{"version":"2","symbols":[],"references":[],"data_directive_references":[],"data_reads":[],"data_writes":[]}
JSON
  cat > "${pass_dir}/data_consumers.json" <<'JSON'
[]
JSON
  cat > "${pass_dir}/next_pass.json" <<'JSON'
{"recommended_pass":{"type":"doc_closure"}}
JSON

  local output
  output="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" text)"

  assert_match "Static gate-visible work exhausted; run orthogonal audits or stop." "${output}" \
    "next-pass must warn when doc_closure repeats"
  python3 - "${pass_dir}/next_pass.json" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
signal = payload.get("plateau_signal") or {}
if signal.get("kind") != "doc_closure_plateau":
    raise SystemExit(f"missing doc_closure plateau signal: {signal!r}")
PY
}

test_pass_start_warns_without_target_but_does_not_fail() {
  local slug; slug="$(unique_slug pass_no_target)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "semantic_corridor", "summary": "Close the reset corridor." },
  "cluster_candidates": [
    { "cluster": "Reset corridor", "anchor": "Reset", "kind": "code", "members": [], "scope_barriers": [], "localize_candidates": [] }
  ]
}
EOF

  local err rc
  set +e
  err="$(bash "${PASS_START}" "${slug}" 1 2>&1 >/dev/null)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "pass-start without TARGET must warn, not fail"
  assert_match "warning: no TARGET" "${err}" \
    "pass-start must warn when it falls back to the first generated bucket"
  assert_match "mechanical fallback" "${err}" \
    "pass-start must describe no-TARGET behavior as a mechanical fallback"
  assert_match "corridor objective" "${err}" \
    "warning must point at selecting an explicit corridor objective"
  [[ -f "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" ]] \
    || fail "pass-start must still persist the plan when defaulting without TARGET"
}

test_pass_start_does_not_warn_when_target_given() {
  local slug; slug="$(unique_slug pass_with_target)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 10 / 20 | 0 | not measured | 0 | 0 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured. |
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "semantic_corridor", "summary": "Close the reset corridor." },
  "cluster_candidates": [
    { "cluster": "Reset corridor", "anchor": "Reset", "kind": "code", "members": [], "scope_barriers": [], "localize_candidates": [] }
  ]
}
EOF

  local err
  err="$(bash "${PASS_START}" "${slug}" 1 Reset 2>&1 >/dev/null)"

  if [[ "${err}" == *"warning: no TARGET"* ]]; then
    fail "pass-start must not warn when an explicit TARGET is provided"
  fi
}

test_pass_residue_check_reconciles_every_raw_ram_review_row_from_the_pass() {
  local slug; slug="$(unique_slug closeout_raw_rows)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed two related zero-page fields."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_FirstField  .EQU $10
ZP_SecondField .EQU $11

Reset:
  LDA ZP_FirstField
  ORA ZP_SecondField
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
raw_$0010,ZP_FirstField,semantic role proven,high,1
raw_$0011,ZP_SecondField,semantic role proven,high,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,ZP_FirstField,,,,1,1,1,0,Reset,
0x0011,unreviewed,ZP_SecondField,,,,1,1,1,0,Reset,
EOF

  bash "${PASS_RESIDUE}" "${slug}" 1 >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

for addr in ("0x0010", "0x0011"):
    row = rows[addr]
    if row["status"] != "symbolized":
        raise SystemExit(f"{addr}: expected symbolized, got {row['status']!r}")
    if row["active"] != "no":
        raise SystemExit(f"{addr}: expected active=no, got {row['active']!r}")
    if row["last_pass_reviewed"] != "1":
        raise SystemExit(
            f"{addr}: expected last_pass_reviewed=1, got {row['last_pass_reviewed']!r}"
        )
PY
}

test_pass_residue_check_rewrites_raw_ram_review_owner_columns_for_renamed_routines() {
  local slug; slug="$(unique_slug closeout_raw_owner_rewrite)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Renamed an owner routine and localized a branch."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner: ; declaration comment
@@renamedLoop: LDA $10
  STA $11
@@_renamedLoop: ; local declaration comment
  LDA $12
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
OldOwner,NewOwner,owner routine renamed,high,1
OldLocal,@@renamedLoop,localized branch target,mechanical,1
@@_oldLoop,@@_renamedLoop,localized underscore branch target,mechanical,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,"OldOwner:1, OldLocal:1",
0x0011,unreviewed,,,,yes,1,1,0,1,," OldLocal : 1 "
0x0012,unreviewed,,,,yes,1,1,1,0," @@_oldLoop: 1 ",
EOF

  bash "${PASS_RESIDUE}" "${slug}" 1 >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    text = handle.read()

if "OldOwner" in text or "OldLocal" in text or "@@_oldLoop" in text:
    raise SystemExit(f"raw_ram_review.csv still contains stale owner labels:\n{text}")

rows = {}
with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    for row in csv.DictReader(handle):
        rows[row["addr_hex"]] = row

if rows["0x0010"]["top_readers"] != "NewOwner:2":
    raise SystemExit(f"expected local owner to collapse to NewOwner, got {rows['0x0010']['top_readers']!r}")
if rows["0x0011"]["top_writers"] != "NewOwner:1":
    raise SystemExit(f"expected local writer owner NewOwner, got {rows['0x0011']['top_writers']!r}")
if rows["0x0012"]["top_readers"] != "NewOwner:1":
    raise SystemExit(f"expected underscore local reader owner NewOwner, got {rows['0x0012']['top_readers']!r}")
PY
}

test_pass_residue_check_rejects_duplicate_local_owner_names() {
  local slug; slug="$(unique_slug closeout_duplicate_local_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Renamed a routine with a duplicated local label name."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
@@done:
  LDA $10
  RTS

UnrelatedOwner:
@@done:
  LDA $11
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
OldOwner,NewOwner,owner routine renamed,high,1
OldDone,@@done,localized return branch,mechanical,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,OldDone:1,
EOF

  local out rc
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e

  assert_eq "${rc}" "4" \
    "duplicate local owner names must fail closeout instead of guessing an owner"
  assert_match "ambiguous_local_replacements" "${out}" \
    "closeout should explain that the local owner was ambiguous"
  assert_match "OldDone" "${out}" \
    "closeout should report the skipped old owner label"

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

reader = rows["0x0010"]["top_readers"]
if reader != "OldDone:1":
    raise SystemExit(f"ambiguous duplicate local owner should stay unreconciled, got {reader!r}")
if "NewOwner" in reader or "UnrelatedOwner" in reader:
    raise SystemExit(f"duplicate local owner was guessed incorrectly: {reader!r}")
PY

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'EOF'
{"intended_pass_id": 1, "localization_owner_snapshot": 7}
EOF
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e
  assert_eq "${rc}" "4" \
    "malformed localization owner snapshots must preserve ambiguity failure"
  assert_match "ambiguous_local_replacements" "${out}" \
    "malformed localization owner snapshots must not authorize a guess"

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'EOF'
{
  "intended_pass_id": 2,
  "localization_owner_snapshot": [{"symbol": "OldDone", "owner": "OldOwner"}]
}
EOF
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e
  assert_eq "${rc}" "4" \
    "localization owner snapshots from another pass must not authorize a rewrite"

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'EOF'
{
  "intended_pass_id": 1,
  "localization_owner_snapshot": [{"symbol": "OldDone", "owner": "GhostOwner"}]
}
EOF
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e
  assert_eq "${rc}" "4" \
    "snapshot owners absent from the post-pass asm must not be written to the review queue"
  assert_match "GhostOwner" "${out}" \
    "closeout should identify the rejected snapshot owner"

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'EOF'
{
  "intended_pass_id": 1,
  "raw_ram_owner_scope_snapshot": [
    {"symbol": "OldDone", "owner": "OldOwner"},
    {"symbol": "OldOwner", "owner": "UnrelatedOwner"}
  ]
}
EOF
  set +e
  out="$(bash "${PASS_RESIDUE}" "${slug}" 1)"
  rc=$?
  set -e
  assert_eq "${rc}" "4" \
    "multiple surviving scoped owners must preserve duplicate-local ambiguity"
  assert_match "OldOwner" "${out}" \
    "closeout should report every rejected scoped owner candidate"
  assert_match "UnrelatedOwner" "${out}" \
    "closeout should report every rejected scoped owner candidate"
}

test_pass_residue_check_uses_snapshot_for_duplicate_local_owner_names() {
  local slug; slug="$(unique_slug closeout_snapshotted_local_owner)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Localized repeated concise branch names."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
NewOwner:
@@done:
  LDA $10
  RTS

OtherNewOwner:
@@done:
  LDA $11
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
OldOwner,NewOwner,owner routine renamed,high,1
OldDone,@@done,localized return branch,mechanical,1
OtherOldOwner,OtherNewOwner,second owner routine renamed,high,1
OtherOldDone,@@done,localized second return branch,mechanical,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,unreviewed,,,,yes,1,1,1,0,OldDone:1,
0x0011,unreviewed,,,,yes,1,1,1,0,OtherOldDone:1,
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'EOF'
{
  "intended_pass_id": 1,
  "localization_owner_snapshot": [
    {"symbol": "OldDone", "owner": "OldOwner"},
    {"symbol": "OtherOldDone", "owner": "OtherOldOwner"}
  ]
}
EOF

  bash "${PASS_RESIDUE}" "${slug}" 1 >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

if rows["0x0010"]["top_readers"] != "NewOwner:1":
    raise SystemExit(f"first snapshotted local owner was not reconciled: {rows['0x0010']!r}")
if rows["0x0011"]["top_readers"] != "OtherNewOwner:1":
    raise SystemExit(f"second snapshotted local owner was not reconciled: {rows['0x0011']!r}")
PY
}

test_pass_residue_check_rejects_residual_raw_operand_for_new_ram_symbol() {
  local slug; slug="$(unique_slug closeout_raw_residue)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named the frame counter."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_FrameCounter .EQU $19

Reset:
  LDA ZP_FrameCounter
  CMP $19
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
raw_$0019,ZP_FrameCounter,frame cadence owner,high,1
EOF

  local output rc
  set +e
  output="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "5" "residual raw operand for a new RAM symbol must fail closeout"
  assert_match "Residual raw operands remain" "${output}"
  assert_match "ZP_FrameCounter" "${output}"
  assert_match "\"line\": 6" "${output}"
}

test_pass_residue_check_allows_scoped_overlay_with_residual_raw_operands() {
  local slug; slug="$(unique_slug closeout_scoped_overlay)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named a PPU-helper overlay alias."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_PpuHelperCursor .EQU $05

PpuHelper:
  LDA ZP_PpuHelperCursor
  RTS

OtherOwner:
  LDA $05
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
raw_$0005,ZP_PpuHelperCursor,PPU helper scoped overlay while other owners remain raw,scoped-overlay,1
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0005,unreviewed,,,,yes,2,2,2,0,"PpuHelper:1,OtherOwner:1",
EOF

  local output rc
  set +e
  output="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "scoped overlay aliases must not require global raw cleanup"
  assert_match '"scoped_overlay_raw_symbols"' "${output}" \
    "closeout must surface scoped overlay aliases for review"
  assert_match "ZP_PpuHelperCursor" "${output}"

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    row = next(csv.DictReader(handle))

if row["status"] != "unreviewed":
    raise SystemExit(f"scoped overlay must not globally mark row symbolized, got {row['status']!r}")
if row["active"] != "yes":
    raise SystemExit(f"scoped overlay must leave mixed raw row active, got {row['active']!r}")
PY
}

test_pass_residue_check_rejects_bare_raw_address_rename_old_name() {
  local slug; slug="$(unique_slug closeout_bare_raw_old)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named the frame counter."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_FrameCounter .EQU $19

Reset:
  LDA ZP_FrameCounter
  RTS
ASM
  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
$0019,ZP_FrameCounter,frame cadence owner,high,1
EOF

  local output rc
  set +e
  output="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "bare raw address old_name must fail closeout"
  assert_match 'must use raw_\$NNNN' "${output}"
  assert_match 'raw_\$0019' "${output}"
}

test_pass_residue_check_rejects_generic_lowercase_rename_old_name() {
  local slug; slug="$(unique_slug closeout_generic_old)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named an interrupt vector table owner."

  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
vectors,InterruptVectorTable,NES hardware interrupt vector table owner for pointer inventory,mechanical,1
EOF

  local output rc
  set +e
  output="$(bash "${PASS_RESIDUE}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "generic lowercase old_name must fail closeout"
  assert_match "old_name values must be symbol-shaped" "${output}"
  assert_match '"old_name": "vectors"' "${output}"
}

test_next_pass_raw_ram_review_uses_parent_owner_after_local_labels() {
  local slug; slug="$(unique_slug raw_owner_local)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared raw owner attribution fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  LDA $10
@@poll:
  STA $10
  RTS

NextRoutine:
  LDA $11
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [
    {
      "name": "Reset",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 2,
        "cpu_address": "\$C000"
      }
    },
    {
      "name": "LC004",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 4,
        "cpu_address": "\$C002"
      }
    },
    {
      "name": "NextRoutine",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 8,
        "cpu_address": "\$C006"
      }
    }
  ],
  "references": [],
  "data_reads": [],
  "data_writes": []
}
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
    bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

row = rows["0x0010"]
if row["top_readers"] != "Reset:1":
    raise SystemExit(f"expected 0x0010 reader owner Reset:1, got {row['top_readers']!r}")
if row["top_writers"] != "Reset:1":
    raise SystemExit(f"expected 0x0010 writer owner Reset:1, got {row['top_writers']!r}")
if "LC004" in row["top_readers"] or "LC004" in row["top_writers"]:
    raise SystemExit(f"local-label fallback leaked into owner columns: {row!r}")
PY
}

test_next_pass_raw_ram_review_does_not_use_data_label_as_owner() {
  local slug; slug="$(unique_slug raw_owner_data)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared data-label owner attribution fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  JSR NextRoutine
  RTS

DataBlob:
  ; Format: byte stream.
  .DB $00
  LDA $10
  STA $10

NextRoutine:
  LDA $11
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [
    {
      "name": "Reset",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 2,
        "cpu_address": "\$C000"
      }
    },
    {
      "name": "DataBlob",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 6,
        "cpu_address": "\$C003"
      }
    },
    {
      "name": "NextRoutine",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 12,
        "cpu_address": "\$C006"
      }
    }
  ],
  "references": [],
  "data_reads": [],
  "data_writes": []
}
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
    bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

row = rows["0x0010"]
if "DataBlob" in row["top_readers"] or "DataBlob" in row["top_writers"]:
    raise SystemExit(f"data label leaked into raw-RAM owner columns: {row!r}")
if row["top_readers"] != "Reset:1" or row["top_writers"] != "Reset:1":
    raise SystemExit(f"expected data-labeled raw sites to fall back to Reset owner, got {row!r}")
PY
}

test_next_pass_raw_ram_review_refreshes_symbolized_owner_columns() {
  local slug; slug="$(unique_slug raw_owner_symbolized)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared symbolized raw owner refresh fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_FrameCounterBase .EQU $0F
ZP_FrameCounter .EQU ZP_FrameCounterBase+1

NewOwner:
  LDA ZP_FrameCounter
  STA ZP_FrameCounter
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [
    {
      "name": "NewOwner",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 5,
        "cpu_address": "\$C000"
      }
    },
    {
      "name": "ZP_FrameCounter",
      "kind": "equ",
      "scope": "global",
      "defined": true,
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 3,
        "value": 16
      }
    }
  ],
  "references": [],
  "data_reads": [
    {
      "symbol": "ZP_FrameCounter",
      "owner_routine": "NewOwner",
      "file": "projects/${slug}/asm/${slug}.asm",
      "line": 6,
      "opcode": "LDA"
    }
  ],
  "data_writes": [
    {
      "symbol": "ZP_FrameCounter",
      "owner_routine": "NewOwner",
      "file": "projects/${slug}/asm/${slug}.asm",
      "line": 7,
      "opcode": "STA"
    }
  ]
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,symbolized,ZP_FrameCounter,,5,no,2,1,1,1,OldOwner:1,OldOwner:1
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
    bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

row = rows["0x0010"]
if row["status"] != "symbolized" or row["active"] != "no":
    raise SystemExit(f"review state should stay symbolized/inactive, got {row!r}")
if row["top_readers"] != "NewOwner:1" or row["top_writers"] != "NewOwner:1":
    raise SystemExit(f"symbolized owner columns were not refreshed: {row!r}")
if row["operand_count"] != "2" or row["read_count"] != "1" or row["write_count"] != "1":
    raise SystemExit(f"symbolized factual counts were not refreshed: {row!r}")
PY
}

test_next_pass_raw_ram_symbol_map_refuses_noncanonical_xref_symbols() {
  local slug; slug="$(unique_slug raw_symbol_refusals)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared structured RAM-symbol refusal fixture."

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [
    {"name":"ZP_LabelPretender","kind":"label","scope":"global","defined":true,"definition":{"value":16}},
    {"name":"ZP_LocalEqu","kind":"equ","scope":"local","defined":true,"definition":{"value":17}},
    {"name":"ZP_UndefinedEqu","kind":"equ","scope":"global","defined":false,"definition":{"value":18}},
    {"name":"RAM_OutsideLowRange","kind":"equ","scope":"global","defined":true,"definition":{"value":4096}},
    {"name":"OTHER_Equ","kind":"equ","scope":"global","defined":true,"definition":{"value":19}},
    {"name":"ZP_NegativeEqu","kind":"equ","scope":"global","defined":true,"definition":{"value":-1}}
  ],
  "references": [],
  "data_reads": [
    {"symbol":"ZP_LabelPretender","owner_routine":"NewOwner","opcode":"LDA"},
    {"symbol":"ZP_LocalEqu","owner_routine":"NewOwner","opcode":"LDA"},
    {"symbol":"ZP_UndefinedEqu","owner_routine":"NewOwner","opcode":"LDA"},
    {"symbol":"RAM_OutsideLowRange","owner_routine":"NewOwner","opcode":"LDA"},
    {"symbol":"OTHER_Equ","owner_routine":"NewOwner","opcode":"LDA"},
    {"symbol":"ZP_NegativeEqu","owner_routine":"NewOwner","opcode":"LDA"}
  ],
  "data_writes": []
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,symbolized,ZP_LabelPretender,,5,no,1,1,1,0,OldOwner:1,
0x0011,symbolized,ZP_LocalEqu,,5,no,1,1,1,0,OldOwner:1,
0x0012,symbolized,ZP_UndefinedEqu,,5,no,1,1,1,0,OldOwner:1,
0x1000,symbolized,RAM_OutsideLowRange,,5,no,1,1,1,0,OldOwner:1,
0x0013,symbolized,OTHER_Equ,,5,no,1,1,1,0,OldOwner:1,
0x-001,symbolized,ZP_NegativeEqu,,5,no,1,1,1,0,OldOwner:1,
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
    bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = list(csv.DictReader(handle))

wrong = [row for row in rows if row["top_readers"] != "OldOwner:1"]
if wrong:
    raise SystemExit(f"unsafe xref symbol entered the low-address equate map: {wrong!r}")
PY
}

test_next_pass_raw_ram_symbol_map_does_not_fall_back_to_source_equates() {
  local slug; slug="$(unique_slug raw_symbol_no_source_fallback)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared source-only RAM-symbol fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
ZP_SourceOnly .EQU $10

NewOwner:
  LDA ZP_SourceOnly
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<'JSON'
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [],
  "references": [],
  "data_reads": [
    {"symbol":"ZP_SourceOnly","owner_routine":"NewOwner","opcode":"LDA"}
  ],
  "data_writes": []
}
JSON
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,symbolized,ZP_SourceOnly,,5,no,1,1,1,0,OldOwner:1,
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 \
    bash "${NEXT_PASS}" "${slug}" json >/dev/null

  assert_match 'OldOwner:1' \
    "$(cat "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv")"
  if rg -q 'NewOwner:1' "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv"; then
    fail "source text must not supply a RAM-symbol mapping absent from xref"
  fi
}

test_next_pass_raw_ram_symbol_map_rejects_malformed_resolved_value() {
  local slug; slug="$(unique_slug raw_symbol_bad_value)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared malformed structured RAM-symbol fixture."

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<'JSON'
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [
    {"name":"ZP_BadValue","kind":"equ","scope":"global","defined":true,"definition":{"value":true}}
  ],
  "references": [],
  "data_reads": [],
  "data_writes": []
}
JSON

  local output rc
  set +e
  output="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "malformed resolved RAM-symbol values must fail conservatively"
  assert_match 'symbols\[0\]\.definition\.value must be int' "${output}"
}

test_next_pass_raw_ram_symbol_map_rejects_malformed_records() {
  local slug; slug="$(unique_slug raw_symbol_bad_record)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared malformed structured RAM-symbol records."
  local xref="projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json"
  local output rc

  cat > "${xref}" <<'JSON'
{"version":"2","data_directive_references":[],"symbols":[null],"references":[],"data_reads":[],"data_writes":[]}
JSON
  set +e
  output="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "65" "non-object xref symbols must fail conservatively"
  assert_match 'symbols\[0\] must be an object' "${output}"

  cat > "${xref}" <<'JSON'
{"version":"2","data_directive_references":[],"symbols":[{"name":"ZP_BadDefinition","kind":"equ","scope":"global","defined":true,"definition":[]}],"references":[],"data_reads":[],"data_writes":[]}
JSON
  set +e
  output="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "65" "non-object xref definitions must fail conservatively"
  assert_match 'symbols\[0\]\.definition must be an object' "${output}"
}

test_next_pass_requires_complete_xref_sections() {
  local slug; slug="$(unique_slug raw_symbol_sections)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared incomplete structured RAM-symbol sections."
  local xref="projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json"
  local section output rc

  for section in symbols references data_reads data_writes; do
    python3 - "${xref}" "${section}" <<'PY'
import json
import sys

path, missing = sys.argv[1:]
payload = {
    "version": "2",
    "data_directive_references": [],
    "symbols": [],
    "references": [],
    "data_reads": [],
    "data_writes": [],
}
payload.pop(missing)
with open(path, "w", encoding="utf-8") as handle:
    json.dump(payload, handle)
PY
    set +e
    output="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json 2>&1)"
    rc=$?
    set -e
    assert_eq "${rc}" "65" "missing ${section} must fail the xref symbol contract"
    assert_match "xref version 2 is missing ${section}" "${output}"
  done
}

test_next_pass_requires_xref_v2_symbol_contract() {
  local slug; slug="$(unique_slug raw_symbol_v1)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared incompatible structured RAM-symbol fixture."

  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<'JSON'
{"version":"1","symbols":[],"references":[],"data_directive_references":[],"data_reads":[],"data_writes":[]}
JSON

  local output rc
  set +e
  output="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "65" "pass selection must reject incompatible xref symbol data"
  assert_match 'xref schema version 2 required' "${output}"
}

test_next_pass_raw_ram_clusters_prioritize_actionable_over_deferred_density() {
  local slug; slug="$(unique_slug raw_cluster_actionable)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared raw-RAM cluster prioritization fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
DenseReviewed:
  LDA $10
  STA $10
  LDA $11
  STA $11
  LDA $12
  STA $12
  LDA $13
  STA $13
  RTS

FreshActionable:
  LDA $20
  STA $21
  LDA $22
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/baseline_status.json" <<'EOF'
{
  "checks": {
    "parity": {"status": "pass"},
    "docs_check": {"status": "pass"},
    "process_check": {"status": "pass"}
  },
  "metrics": {
    "lxxxx_definitions": 0,
    "lxxxx_occurrences": 0,
    "strict_active_raw_lowaddr": 11
  }
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "version": "2",
  "data_directive_references": [],
  "symbols": [
    {
      "name": "DenseReviewed",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 2,
        "cpu_address": "\$C000"
      }
    },
    {
      "name": "FreshActionable",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 13,
        "cpu_address": "\$C009"
      }
    }
  ],
  "references": [],
  "data_reads": [],
  "data_writes": []
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,deferred,,already reviewed; wait for wider owner proof,7,yes,2,1,1,1,DenseReviewed:1,DenseReviewed:1
0x0011,deferred,,already reviewed; wait for wider owner proof,7,yes,2,1,1,1,DenseReviewed:1,DenseReviewed:1
0x0012,deferred,,already reviewed; wait for wider owner proof,7,yes,2,1,1,1,DenseReviewed:1,DenseReviewed:1
0x0013,deferred,,already reviewed; wait for wider owner proof,7,yes,2,1,1,1,DenseReviewed:1,DenseReviewed:1
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
recommended = payload["recommended_pass"]
if recommended["type"] != "raw_ram_symbolization":
    raise SystemExit(f"expected raw-RAM recommendation, got {recommended!r}")
if "FreshActionable" not in recommended["summary"]:
    raise SystemExit(f"expected fresh actionable corridor to win, got {recommended!r}")
clusters = payload["cluster_candidates"]
if not clusters or clusters[0]["anchor"] != "FreshActionable":
    raise SystemExit(f"expected FreshActionable as top cluster, got {clusters[:2]!r}")
if clusters[0].get("actionable_operand_count") != 3:
    raise SystemExit(f"expected 3 actionable operands in top cluster, got {clusters[0]!r}")
if any(cluster["anchor"] == "DenseReviewed" for cluster in clusters):
    raise SystemExit(f"deferred-only dense owner should not be recommended: {clusters!r}")
PY
}

_write_raw_ram_mode_baseline() {
  # $1=slug $2=strict_active_raw_lowaddr
  cat > "projects/$1/docs/reverse_engineering/inventory/pass/baseline_status.json" <<EOF
{
  "checks": {
    "parity": {"status": "pass"},
    "docs_check": {"status": "pass"},
    "process_check": {"status": "pass"}
  },
  "metrics": {
    "lxxxx_definitions": 0,
    "lxxxx_occurrences": 0,
    "strict_active_raw_lowaddr": $2
  }
}
EOF
}

test_next_pass_ranks_actionable_subcorridor_above_broad_mixed_anchor() {
  local slug; slug="$(unique_slug raw_mixed_anchor)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared mixed-anchor demotion fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
BroadMixedAnchor:
  LDA $30
  STA $31
  LDA $32
  STA $33
  LDA $34
  STA $35
  LDA $40
  STA $41
  RTS

FocusedActionable:
  LDA $50
  STA $51
  LDA $52
  STA $53
  RTS
ASM
  _write_raw_ram_mode_baseline "${slug}" 10
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0040,deferred,,mixed role,7,yes,1,1,1,0,BroadMixedAnchor:1,
0x0041,deferred,,mixed role,7,yes,1,1,0,1,,BroadMixedAnchor:1
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
if payload["recommended_pass"]["type"] != "raw_ram_symbolization":
    raise SystemExit(f"expected raw-RAM mode, got {payload['recommended_pass']!r}")
clusters = payload["cluster_candidates"]
anchors = [c["anchor"] for c in clusters]
if anchors[0] != "FocusedActionable":
    raise SystemExit(f"focused sub-corridor must rank first, got {anchors!r}")
focused = clusters[0]
if focused.get("mixed_anchor") is not False:
    raise SystemExit(f"focused corridor must not be a mixed anchor: {focused!r}")
broad = next((c for c in clusters if c["anchor"] == "BroadMixedAnchor"), None)
if broad is None:
    raise SystemExit("broad mixed anchor must still appear as evidence")
if broad.get("mixed_anchor") is not True or broad.get("anchor_role") != "mixed_anchor_evidence":
    raise SystemExit(f"broad anchor must be flagged as evidence container: {broad!r}")
# Broad anchor has MORE actionable operands but must still rank below the focused corridor.
if broad["actionable_operand_count"] <= focused["actionable_operand_count"]:
    raise SystemExit("fixture invalid: broad anchor should have higher raw density")
if anchors.index("FocusedActionable") >= anchors.index("BroadMixedAnchor"):
    raise SystemExit(f"actionable corridor must outrank denser mixed anchor: {anchors!r}")
if (broad.get("hint") or {}).get("kind") != "narrow":
    raise SystemExit(f"mixed anchor must carry a narrow hint: {broad.get('hint')!r}")
PY
}

test_next_pass_surfaces_scoped_overlay_for_cross_owner_byte() {
  local slug; slug="$(unique_slug raw_scoped_overlay)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared scoped-overlay fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
OwnerOne:
  LDA $20
  STA $20
  LDA $0C
  STA $0C
  RTS

OwnerTwo:
  LDA $0C
  STA $21
  LDA $21
  RTS
ASM
  _write_raw_ram_mode_baseline "${slug}" 8

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
clusters = payload["cluster_candidates"]
overlay_owners = {
    c["anchor"]: c
    for c in clusters
    if "0x000c" in (c.get("scoped_overlay_candidates") or [])
}
# The cross-owner byte $0C must be offered as a scoped overlay in each owner.
for owner in ("OwnerOne", "OwnerTwo"):
    c = overlay_owners.get(owner)
    if c is None:
        raise SystemExit(f"{owner} must surface 0x000c as a scoped overlay candidate: {clusters!r}")
    if (c.get("hint") or {}).get("kind") != "scoped_overlay":
        raise SystemExit(f"{owner} must carry a scoped_overlay hint: {c.get('hint')!r}")
PY
}

test_next_pass_offers_data_label_alternatives_when_only_mixed_anchor_remains() {
  local slug; slug="$(unique_slug raw_data_alt)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared data-label alternative fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
BroadMixedAnchor:
  LDA $30
  STA $31
  LDA $32
  STA $33
  LDA $34
  STA $35
  LDA $40
  STA $41
  RTS
ASM
  _write_raw_ram_mode_baseline "${slug}" 8
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_summary_generic.json" <<'EOF'
{"top_callables":[],"top_jump_targets":[],"top_data_labels":[{"label":"L1234","total_ref_count":12}]}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0040,deferred,,mixed role,7,yes,1,1,1,0,BroadMixedAnchor:1,
0x0041,deferred,,mixed role,7,yes,1,1,0,1,,BroadMixedAnchor:1
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1], encoding="utf-8"))
if not payload["cluster_candidates"][0].get("mixed_anchor"):
    raise SystemExit("fixture invalid: top raw cluster should be a mixed anchor")
alts = payload.get("alternative_candidates") or []
labels = {a["label"] for a in alts}
if "L1234" not in labels:
    raise SystemExit(f"data-label alternative must be surfaced when only a mixed anchor remains: {alts!r}")
if any(a["kind"] != "data_label" for a in alts):
    raise SystemExit(f"alternatives must be data-label candidates: {alts!r}")
if "confidence_caveat" not in payload:
    raise SystemExit("candidate-evidence caveat must be present")
PY
}

test_next_pass_warns_when_top_candidate_is_broad_mixed_anchor() {
  local slug; slug="$(unique_slug raw_mixed_warn)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared mixed-anchor warning fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
BroadMixedAnchor:
  LDA $30
  STA $31
  LDA $32
  STA $33
  LDA $34
  STA $35
  LDA $40
  STA $41
  RTS
ASM
  _write_raw_ram_mode_baseline "${slug}" 8
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0040,deferred,,mixed role,7,yes,1,1,1,0,BroadMixedAnchor:1,
0x0041,deferred,,mixed role,7,yes,1,1,0,1,,BroadMixedAnchor:1
EOF

  local err
  err="$(PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json 2>&1 >/dev/null)"

  assert_match "broad mixed anchor" "${err}" \
    "next-pass must warn when the top generated bucket is a broad mixed anchor"
  assert_match "BroadMixedAnchor" "${err}"
}

_write_tiny_and_big_next_pass() {
  local slug="$1"
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "raw_ram_symbolization", "summary": "x" },
  "cluster_candidates": [
    {"cluster":"TinyOwner corridor","anchor":"TinyOwner","kind":"raw_ram_corridor","actionable_operand_count":2,"members":[],"scope_barriers":[],"localize_candidates":[]},
    {"cluster":"BigOwner corridor","anchor":"BigOwner","kind":"raw_ram_corridor","actionable_operand_count":6,"members":[],"scope_barriers":[],"localize_candidates":[]}
  ]
}
EOF
}

test_pass_start_warns_on_tiny_objective_while_larger_corridor_remains() {
  local slug; slug="$(unique_slug pass_tiny_objective)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_tiny_and_big_next_pass "${slug}"

  local err rc
  set +e
  err="$(bash "${PASS_START}" "${slug}" 1 TinyOwner 2>&1 >/dev/null)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "tiny-objective warning must be advisory, not a failure"
  assert_match "is a tiny 2-site objective" "${err}" \
    "pass-start must warn on a tiny objective while a larger corridor remains"
  assert_match "BigOwner" "${err}" "warning must name the larger available corridor"
}

test_pass_start_tiny_objective_warning_suppressed_by_final_tail_note() {
  local slug; slug="$(unique_slug pass_tiny_exempt)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_tiny_and_big_next_pass "${slug}"

  local err
  err="$(WHY_NOW="final-tail cleanup of the last residual byte" \
    bash "${PASS_START}" "${slug}" 1 TinyOwner 2>&1 >/dev/null)"

  if [[ "${err}" == *"is a tiny"* ]]; then
    fail "a final-tail/strategic objective note must suppress the tiny-objective warning"
  fi
}

test_pass_start_tiny_warning_ignores_mixed_anchor_as_larger_corridor() {
  local slug; slug="$(unique_slug pass_tiny_vs_mixed)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  # The only larger candidate is a mixed-anchor evidence container, which must
  # not be advertised as the "larger corridor to prefer".
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/next_pass.json" <<'EOF'
{
  "selection_strategy": "test",
  "recommended_pass": { "type": "raw_ram_symbolization", "summary": "x" },
  "cluster_candidates": [
    {"cluster":"TinyOwner corridor","anchor":"TinyOwner","kind":"raw_ram_corridor","actionable_operand_count":2,"mixed_anchor":false,"members":[],"scope_barriers":[],"localize_candidates":[]},
    {"cluster":"BroadMixedAnchor corridor","anchor":"BroadMixedAnchor","kind":"raw_ram_corridor","actionable_operand_count":9,"mixed_anchor":true,"anchor_role":"mixed_anchor_evidence","members":[],"scope_barriers":[],"localize_candidates":[]}
  ]
}
EOF

  local err
  err="$(bash "${PASS_START}" "${slug}" 1 TinyOwner 2>&1 >/dev/null)"

  if [[ "${err}" == *"is a tiny"* ]]; then
    fail "a mixed-anchor evidence container must not count as a larger actionable corridor"
  fi
}

test_pass_start_no_tiny_warning_when_selecting_the_larger_corridor() {
  local slug; slug="$(unique_slug pass_big_objective)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_tiny_and_big_next_pass "${slug}"

  local err
  err="$(bash "${PASS_START}" "${slug}" 1 BigOwner 2>&1 >/dev/null)"

  if [[ "${err}" == *"is a tiny"* ]]; then
    fail "selecting the larger corridor must not warn about a tiny objective"
  fi
}

test_next_pass_raw_ram_review_preserves_existing_row_order() {
  local slug; slug="$(unique_slug raw_order)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared raw-RAM ordering fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  LDA $20
  STA $10
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0018,deferred,ZP_OldDeferred,kept for ordering regression,1,no,0,0,0,0,,
0x0008,symbolized,ZP_OldSymbolized,kept for ordering regression,1,no,0,0,0,0,,
0x0010,deferred,ZP_ExistingReview,keep review fields stable,7,yes,99,88,77,66,OldReader:7,OldWriter:6
EOF

  PROJECT_NEXT_PASS_WRITE_RAW_RAM_REVIEW=1 bash "${NEXT_PASS}" "${slug}" json >/dev/null

  local order
  order="$(awk -F, 'NR>1 {print $1}' "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" | paste -sd ' ' -)"
  assert_eq "${order}" "0x0018 0x0008 0x0010 0x0020" \
    "raw_ram_review.csv must preserve existing row order and append new addresses"
  python3 - "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'PY'
import csv
import sys

with open(sys.argv[1], encoding="utf-8", newline="") as handle:
    rows = {row["addr_hex"]: row for row in csv.DictReader(handle)}

row = rows["0x0010"]
expected = {
    "status": "deferred",
    "proposed_symbol": "ZP_ExistingReview",
    "notes": "keep review fields stable",
    "last_pass_reviewed": "7",
    "active": "yes",
    "operand_count": "1",
    "distinct_owner_count": "1",
    "read_count": "0",
    "write_count": "1",
    "top_readers": "",
    "top_writers": "Reset:1",
}
for key, value in expected.items():
    if row.get(key) != value:
        raise SystemExit(f"existing raw-RAM review row field {key} mismatch: {row.get(key)!r}")
PY
}

test_next_pass_does_not_rewrite_raw_ram_review_without_write_mode() {
  local slug; slug="$(unique_slug raw_readonly)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Prepared raw-RAM read-only fixture."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  LDA $10
  STA $10
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,revisit,ZP_ExistingReview,explicit refresh should stabilize this row,7,yes,99,88,77,66,OldReader:7,OldWriter:6
EOF

  local before="${NESREV_TEST_TMPDIR}/${slug}_raw_before.csv"
  cp "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" "${before}"

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

  cmp -s "${before}" "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" \
    || fail "project-next-pass must not rewrite raw_ram_review.csv without explicit write mode"
}

test_project_raw_ram_review_preserves_existing_row_order() {
  local slug; slug="$(unique_slug raw_manual_order)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0018,deferred,ZP_OldDeferred,kept for ordering regression,1,no,0,0,0,0,,
0x0008,symbolized,ZP_OldSymbolized,kept for ordering regression,1,no,0,0,0,0,,
EOF

  bash "${REPO_ROOT}/scripts/project_raw_ram_review.sh" \
    "${slug}" '$0010' unreviewed ZP_NewManual "manual review" 2 >/dev/null

  local order
  order="$(awk -F, 'NR>1 {print $1}' "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" | paste -sd ' ' -)"
  assert_eq "${order}" "0x0018 0x0008 0x0010" \
    "manual raw-RAM review updates must preserve existing row order and append new addresses"
}
