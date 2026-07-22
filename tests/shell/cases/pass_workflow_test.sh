#!/usr/bin/env bash
# Tests pass lifecycle contracts exposed by the clean-room workflow.

PASS_START="${REPO_ROOT}/scripts/project_pass_start.sh"
PASS_CLOSEOUT="${REPO_ROOT}/scripts/project_pass_closeout.sh"
PASS_FINISH="${REPO_ROOT}/scripts/project_pass_finish.sh"
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
MAX_ACTIVE_MAGIC_IMMEDIATES=999999
EOF
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
      printf '{"symbols":[],"references":[],"data_reads":[],"data_writes":[],"indirect_data_flows":[]}\n' > "${path}"
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

printf 'CALL' >> "${XASM_LOG}"
for arg in "$@"; do
  printf '\t%s' "${arg}" >> "${XASM_LOG}"
done
printf '\n' >> "${XASM_LOG}"

out=""
compare=""
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
    *)
      shift
      ;;
  esac
done

if [[ -n "${compare}" ]]; then
  printf 'COMPARE_SIZE\t%s\n' "$(wc -c < "${compare}" | tr -d ' ')" >> "${XASM_LOG}"
fi

if [[ -n "${out}" ]]; then
  mkdir -p "$(dirname "${out}")"
  python3 - "${out}" "${XASM_STUB_OUT_SIZE:-0}" <<'PY'
import sys
from pathlib import Path

Path(sys.argv[1]).write_bytes(b"\x00" * int(sys.argv[2]))
PY
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
  local slug; slug="$(unique_slug analogue_recorded)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard \
    "${slug}" \
    "Analogue: prior_project (reused the reset and NMI vocabulary; packet layout differed)."

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
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

test_project_process_check_skips_scorecard_lifecycle_for_legacy_imports() {
  local slug; slug="$(unique_slug process_lifecycle_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "legacy"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | Imported latest pass | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pass | 0 | Imported history. |
| 1 | Imported stale pass | 0 / 0 | 0 | 0 | 0 | 0 | 0 | pass | pending | 0 | Imported history. |
EOF

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
}

test_project_process_check_enforces_scorecard_lifecycle_when_required() {
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

  assert_eq "${rc}" "1" "opted-in scorecard lifecycle drift must fail process-check"
  assert_match "non-latest pass 1 has docs_check='pending'" "${output}"
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

  PATH="${stubdir}:${PATH}" XASM_LOG="${log}" XASM_STUB_OUT_SIZE=4194304 \
    bash "${REPO_ROOT}/scripts/verify.sh" "${asm}" "${ref}" "${out}" "${warnings}" '$C000' >/dev/null
}

test_legacy_project_process_check_does_not_require_analogue_record() {
  local slug; slug="$(unique_slug analogue_legacy)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "legacy"
  _write_pass_one_scorecard "${slug}" "Pre-contract project history."

  bash "${PROCESS_CHECK}" "${slug}" >/dev/null
}

test_pass_start_emits_selection_briefing_not_unmaintained_gate_ledger() {
  local slug; slug="$(unique_slug pass_briefing)"
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
PY

  if rg -n '^## (Planned|Gate Progress)' "${md_path}" >/dev/null; then
    fail "generated pass briefing must not contain unmaintained plan or gate sections"
  fi
  rg -q 'Generated corridor-selection briefing' "${md_path}" \
    || fail "generated pass briefing must describe its cache role"
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
printf 'prep %s\n' "${slug}" > "${pass_dir}/prep_stub.log"
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
{"symbols":[],"references":[],"data_reads":[],"data_writes":[]}
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
  rg -q "prep ${slug}" "projects/${slug}/docs/reverse_engineering/inventory/pass/prep_stub.log" \
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
  rg -q "prep ${slug}" "projects/${slug}/docs/reverse_engineering/inventory/pass/prep_stub.log" \
    || fail "project-next-pass must invoke prep when a required cache input is missing"
}

test_project_pass_finish_creates_row_runs_gates_and_marks_scorecard() {
  local slug; slug="$(unique_slug pass_finish)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_zero_scorecard "${slug}"

  local stubdir="projects/${slug}/finish_stubs"
  local log="projects/${slug}/finish.log"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_closeout.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'closeout %s %s\n' "$1" "$2" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'inventory %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_docs_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'docs %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_process_check.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'process %s\n' "$1" >> "${STUB_LOG}"
SH
  cat > "${stubdir}/project_verify.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${EXPECT_RELAXED:-0}" == "1" && "${ALLOW_UNRESOLVED_LXXXX:-}" != "1" ]]; then
  echo "expected relaxed verify environment" >&2
  exit 99
fi
printf 'verify %s %s\n' "$1" "${ALLOW_UNRESOLVED_LXXXX:-}" >> "${STUB_LOG}"
SH

  STUB_LOG="${log}" EXPECT_RELAXED=1 PROJECT_PASS_FINISH_SCRIPT_DIR="${stubdir}" \
    FOCUS="Finish wrapper corridor" \
    NOTES="Closed the finish wrapper corridor." \
    bash "${PASS_FINISH}" "${slug}" 1 relaxed >/dev/null

  cat > "projects/${slug}/expected_finish.log" <<EOF
inventory ${slug}
closeout ${slug} 1
docs ${slug}
process ${slug}
verify ${slug} 1
docs ${slug}
EOF
  cmp -s "projects/${slug}/expected_finish.log" "${log}" \
    || fail "project-pass-finish must run inventory, closeout, docs, process, verify, final docs in order"

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
    raise SystemExit("project-pass-finish did not create pass 1 scorecard row")
if row[1] != "Finish wrapper corridor":
    raise SystemExit(f"unexpected focus: {row[1]!r}")
if row[8] != "pass (LXXXX allowed)" or row[9] != "pass":
    raise SystemExit(f"gate cells not marked after successful finish: {row!r}")
if row[11] != "Closed the finish wrapper corridor.":
    raise SystemExit(f"notes were not preserved: {row[11]!r}")
PY
}

test_project_pass_finish_marks_scorecard_by_header_name() {
  local slug; slug="$(unique_slug pass_finish_header)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | review_state | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---:|---|
| 0 | Existing setup row | 0 / 0 | 0 | not measured | 0 | 0 | 0 | keep-zero | pass | pass | 0 | pass_id |
| 1 | Existing finish row | 0 / 0 | 0 | not measured | 0 | 0 | 0 | keep-me | pending | pending | pending | Existing row should be marked in place. |
EOF

  local stubdir="projects/${slug}/finish_stubs"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_closeout.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
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

  PROJECT_PASS_FINISH_SCRIPT_DIR="${stubdir}" \
    bash "${PASS_FINISH}" "${slug}" 1 strict >/dev/null

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
if row[cols["rework_items"]] != "0":
    raise SystemExit(f"rework_items column was not normalized by name: {row!r}")
PY
}

test_project_pass_finish_materializes_missing_row_from_existing_header() {
  local slug; slug="$(unique_slug pass_finish_materialize)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"

  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| focus | pass_id | review_state | notes | verify | docs_check | rework_items | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta |
|---|---|---|---|---|---|---:|---|---|---|---|---|---|
| Existing setup row | 0 | keep-zero | pass_id | pass | pass | 0 | 0 / 0 | 0 | not measured | 0 | 0 | 0 |
EOF

  local stubdir="projects/${slug}/finish_stubs"
  mkdir -p "${stubdir}"
  cat > "${stubdir}/project_pass_closeout.sh" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
SH
  cat > "${stubdir}/refresh_inventory.sh" <<'SH'
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

  PROJECT_PASS_FINISH_SCRIPT_DIR="${stubdir}" \
    FOCUS="Materialized finish row" \
    NOTES="Created from a reordered scorecard header." \
    bash "${PASS_FINISH}" "${slug}" 1 strict >/dev/null

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
    "focus": "Materialized finish row",
    "review_state": "",
    "notes": "Created from a reordered scorecard header.",
    "verify": "pass",
    "docs_check": "pass",
    "rework_items": "0",
    "labels_remaining": "0 / 0",
}
for name, value in expected.items():
    if row[cols[name]] != value:
        raise SystemExit(f"{name} = {row[cols[name]]!r}, expected {value!r}; row={row!r}")
PY
}

test_make_pass_start_forwards_objective_value_with_apostrophe() {
  local slug; slug="$(unique_slug pass_objective_apostrophe)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_reset_next_pass "${slug}"

  # Exercise the Makefile forwarding path (not the script directly): a prose
  # objective with an apostrophe must survive without breaking shell parsing.
  make project-pass-start PROJECT="${slug}" PASS=1 TARGET=Reset \
    CORRIDOR="runner's path-state corridor" >/dev/null 2>&1

  python3 - "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json" <<'PY'
import json
import sys

plan = json.load(open(sys.argv[1], encoding="utf-8"))
got = plan.get("corridor_objective", {}).get("selected_corridor")
if got != "runner's path-state corridor":
    raise SystemExit(f"Makefile forwarding mangled the apostrophe value: {got!r}")
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
  for target in raw_bf raw_0bf raw_00bf 'raw_$$00bf'; do
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

test_pass_closeout_reports_complete_corridor_objective_without_warning() {
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
  out="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
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

test_pass_closeout_warns_on_incomplete_objective_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_incomplete)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  _write_pass_plan_objective "${slug}" 1 "Reset corridor" "" "" "" ""

  local out rc
  set +e
  out="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "incomplete objective must warn, not fail, on an otherwise clean pass"
  assert_match "corridor objective was incomplete" "${out}" \
    "closeout must warn when the persisted objective was incomplete at pass start"
  assert_match '"corridor_objective_status": "incomplete"' "${out}" \
    "closeout summary must report the incomplete objective status"
}

test_pass_closeout_warns_when_objective_missing_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_missing)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  # No current_pass_plan.json is written.

  local out rc
  set +e
  out="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "missing objective must warn, not fail, on an otherwise clean pass"
  assert_match "no persisted corridor objective found" "${out}" \
    "closeout must warn when no objective was persisted"
  assert_match '"corridor_objective_status": "missing"' "${out}" \
    "closeout summary must report the missing objective status"
}

test_pass_closeout_warns_on_stale_plan_objective_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_stale)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  # Plan was written for a different pass id than the one being closed out.
  _write_pass_plan_objective "${slug}" 2 \
    "Other corridor" "later pass" "later" "later" "later"

  local out rc
  set +e
  out="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "stale plan objective must warn, not fail, on an otherwise clean pass"
  assert_match "persisted corridor objective is for pass 2" "${out}" \
    "closeout must warn when the plan objective belongs to another pass"
  assert_match '"corridor_objective_status": "stale_plan"' "${out}" \
    "closeout summary must report the stale_plan objective status"
}

test_pass_closeout_warns_on_unparseable_plan_but_does_not_fail() {
  local slug; slug="$(unique_slug closeout_obj_invalid)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Closed the reset corridor."
  printf '{ this is not valid json' \
    > "projects/${slug}/docs/reverse_engineering/inventory/pass/current_pass_plan.json"

  local out rc
  set +e
  out="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "an unparseable plan must warn, not crash closeout"
  assert_match "current_pass_plan.json could not be parsed" "${out}" \
    "closeout must warn when the plan cache is malformed"
  assert_match '"corridor_objective_status": "invalid_plan"' "${out}" \
    "closeout summary must report the invalid_plan objective status"
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
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "legacy"
  _write_pass_one_scorecard "${slug}" "Pre-contract project history."

  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
APU_CUSTOM_LOCAL .EQU $05
Reset:
  RTS
ASM

  local out rc
  set +e
  out="$(bash "${PROCESS_CHECK}" "${slug}" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "hardware-drift check must be advisory and not fail process-check"
  assert_match "canonical hardware-constant drift \(advisory\)" "${out}"
  assert_match "APU_CUSTOM_LOCAL" "${out}"
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
{"symbols":[],"references":[],"data_reads":[],"data_writes":[]}
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

test_pass_closeout_reconciles_every_raw_ram_review_row_from_the_pass() {
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

  bash "${PASS_CLOSEOUT}" "${slug}" 1 >/dev/null

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

test_pass_closeout_rewrites_raw_ram_review_owner_columns_for_renamed_routines() {
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

  bash "${PASS_CLOSEOUT}" "${slug}" 1 >/dev/null

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

test_pass_closeout_rejects_duplicate_local_owner_names() {
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
  out="$(bash "${PASS_CLOSEOUT}" "${slug}" 1)"
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
}

test_pass_closeout_rejects_residual_raw_operand_for_new_ram_symbol() {
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
  output="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "5" "residual raw operand for a new RAM symbol must fail closeout"
  assert_match "Residual raw operands remain" "${output}"
  assert_match "ZP_FrameCounter" "${output}"
  assert_match "\"line\": 6" "${output}"
}

test_pass_closeout_allows_scoped_overlay_with_residual_raw_operands() {
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
  output="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
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

test_pass_closeout_rejects_bare_raw_address_rename_old_name() {
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
  output="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "bare raw address old_name must fail closeout"
  assert_match 'must use raw_\$NNNN' "${output}"
  assert_match 'raw_\$0019' "${output}"
}

test_pass_closeout_rejects_generic_lowercase_rename_old_name() {
  local slug; slug="$(unique_slug closeout_generic_old)"
  trap "cleanup_project ${slug}" EXIT
  _make_workflow_project "${slug}" "none"
  _write_pass_one_scorecard "${slug}" "Named an interrupt vector table owner."

  cat >> "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
vectors,InterruptVectorTable,NES hardware interrupt vector table owner for pointer inventory,mechanical,1
EOF

  local output rc
  set +e
  output="$(bash "${PASS_CLOSEOUT}" "${slug}" 1 2>&1)"
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

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

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

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

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
ZP_FrameCounter .EQU $10

NewOwner:
  LDA ZP_FrameCounter
  STA ZP_FrameCounter
  RTS
ASM
  cat > "projects/${slug}/docs/reverse_engineering/inventory/pass/xref_with_data.json" <<EOF
{
  "symbols": [
    {
      "name": "NewOwner",
      "scope": "global",
      "definition": {
        "file": "projects/${slug}/asm/${slug}.asm",
        "line": 4,
        "cpu_address": "\$C000"
      }
    }
  ],
  "references": [],
  "data_reads": [
    {
      "symbol": "ZP_FrameCounter",
      "owner_routine": "NewOwner",
      "file": "projects/${slug}/asm/${slug}.asm",
      "line": 5,
      "opcode": "LDA"
    }
  ],
  "data_writes": [
    {
      "symbol": "ZP_FrameCounter",
      "owner_routine": "NewOwner",
      "file": "projects/${slug}/asm/${slug}.asm",
      "line": 6,
      "opcode": "STA"
    }
  ]
}
EOF
  cat > "projects/${slug}/docs/reverse_engineering/inventory/raw_ram_review.csv" <<'EOF'
addr_hex,status,proposed_symbol,notes,last_pass_reviewed,active,operand_count,distinct_owner_count,read_count,write_count,top_readers,top_writers
0x0010,symbolized,ZP_FrameCounter,,5,no,2,1,1,1,OldOwner:1,OldOwner:1
EOF

  PROJECT_NEXT_PASS_AUTO_PREP=0 bash "${NEXT_PASS}" "${slug}" json >/dev/null

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

  bash "${NEXT_PASS}" "${slug}" json >/dev/null

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
