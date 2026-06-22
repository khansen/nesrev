#!/usr/bin/env bash
# Tests scripts/project_scorecard_sync.sh for pass-0 fill_when_empty behavior.
# Builds a synthetic project with a minimal scorecard, runs sync, and inspects
# the resulting row.

SYNC="${REPO_ROOT}/scripts/project_scorecard_sync.sh"

_make_minimal_asm() {
  # The sync script invokes constant_kpi.sh, so the asm needs to at least
  # parse. Provide a trivial one.
  local path="$1"
  mkdir -p "$(dirname "${path}")"
  cat > "${path}" <<'ASM'
.ORG $C000
L0001:
  LDA #$00
  RTS
ASM
}

_make_scaffold() {
  local slug="$1"
  scaffold_project "${slug}" /dev/null 2>/dev/null || true
  rm -f "projects/${slug}/reference/${slug}.nes"
  _make_minimal_asm "projects/${slug}/asm/${slug}.asm"
  mkdir -p "projects/${slug}/docs/reverse_engineering/inventory"
  # constant_kpi config the sync script reads; needs MAX_ACTIVE_MAGIC_IMMEDIATES
  cat > "projects/${slug}/docs/reverse_engineering/inventory/constant_kpi.txt" <<'EOF'
MAX_ACTIVE_MAGIC_IMMEDIATES=999999
EOF
  # Augment project.conf with CONST_KPI_FILE
  cat >> "projects/${slug}/project.conf" <<EOF
CONST_KPI_FILE="projects/${slug}/docs/reverse_engineering/inventory/constant_kpi.txt"
PROGRESS_SCORECARD_FILE="projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"
EOF
}

_write_scorecard() {
  local slug="$1"; shift
  local pass_id="$1"; shift
  # Remaining args are the cells after pass_id+focus; row is 12 columns total.
  local header="| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |"
  local sep="|---|---|---|---|---|---|---|---|---|---|---|---|"
  local row="| ${pass_id} | Intake baseline |"
  for cell in "$@"; do
    row+=" ${cell} |"
  done
  printf "%s\n%s\n%s\n" "${header}" "${sep}" "${row}" \
    > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"
}

_get_cell() {
  # Reads the column named $2 from the pass-0 row of slug $1's scorecard.
  local slug="$1" col_name="$2"
  python3 - "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" "${col_name}" <<'PY'
import sys
path, col = sys.argv[1:]
lines = open(path).read().splitlines()
header = next(l for l in lines if l.startswith("|") and "pass_id" in l)
cols = [c.strip() for c in header.strip("|").split("|")]
idx = cols.index(col)
for l in lines:
    if not l.startswith("|"): continue
    cells = [c.strip() for c in l.strip("|").split("|")]
    if cells and cells[0] == "0":
        print(cells[idx])
        break
PY
}

test_pass0_fills_empty_outcome_cells() {
  local slug; slug="$(unique_slug pass0_empty)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  # Empty outcome cells
  _write_scorecard "${slug}" 0 "" "" "" "" "" "" "" "" "" ""

  bash "${SYNC}" "${slug}" 0 >/dev/null

  assert_eq "$(_get_cell "${slug}" "verify")"                       "pass (intake-relaxed)"
  assert_eq "$(_get_cell "${slug}" "docs_check")"                   "pass"
  assert_eq "$(_get_cell "${slug}" "raw_ptr_immediates_remaining")" "not measured"
  assert_eq "$(_get_cell "${slug}" "rework_items")"                 "0"
  assert_eq "$(_get_cell "${slug}" "notes")" \
    "Intake baseline captured; semantic naming not started."
}

test_scorecard_sync_counts_only_xasm_bracketed_raw_indirect_operands() {
  local slug; slug="$(unique_slug raw_indirect_indexed)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  LDA ($10)
  LDA ($11),Y
  LDA ($12,X)
  LDA [$13]
  LDA [$13,X]
  LDA [$14],Y
  RTS
ASM
  _write_scorecard "${slug}" 0 "" "" "" "" "" "" "" "" "" ""

  bash "${SYNC}" "${slug}" 0 >/dev/null

  assert_eq "$(_get_cell "${slug}" "raw_indirect_operands_remaining")" "3" \
    "raw-indirect count must include bracketed xasm operands and ignore parenthesized operands"
}

test_pass0_preserves_human_values() {
  local slug; slug="$(unique_slug pass0_preserved)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  # Pre-populated outcome cells
  _write_scorecard "${slug}" 0 "" "" "42" "" "" "" "fail" "manual" "7" "Reviewed manually"

  bash "${SYNC}" "${slug}" 0 >/dev/null

  assert_eq "$(_get_cell "${slug}" "verify")"                       "fail" \
    "human-entered verify value must not be overwritten"
  assert_eq "$(_get_cell "${slug}" "docs_check")"                   "manual" \
    "human-entered docs_check value must not be overwritten"
  assert_eq "$(_get_cell "${slug}" "raw_ptr_immediates_remaining")" "42" \
    "human-entered pointer metric must not be overwritten"
  assert_eq "$(_get_cell "${slug}" "rework_items")" "7" \
    "human-entered rework count must not be overwritten"
  assert_eq "$(_get_cell "${slug}" "notes")" "Reviewed manually" \
    "human-entered notes must not be overwritten"
}

test_nonzero_pass_does_not_infer_outcomes() {
  local slug; slug="$(unique_slug pass5)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  # Empty outcome cells on pass 5
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 5 | Test pass |  |  |  |  |  |  |  |  |  |  |
EOF

  bash "${SYNC}" "${slug}" 5 >/dev/null

  # Read the three potentially-inferred cells on the pass-5 row.
  local row_path="projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"
  _get_cell_pass5() {
    python3 - "${row_path}" "$1" <<'PY'
import sys
path, col = sys.argv[1:]
lines = open(path).read().splitlines()
header = next(l for l in lines if l.startswith("|") and "pass_id" in l)
cols = [c.strip() for c in header.strip("|").split("|")]
idx = cols.index(col)
for l in lines:
    if not l.startswith("|"): continue
    cells = [c.strip() for c in l.strip("|").split("|")]
    if cells and cells[0] == "5":
        print(cells[idx])
        break
PY
  }

  assert_eq "$(_get_cell_pass5 verify)"                       "" \
    "non-zero pass must not auto-fill verify"
  assert_eq "$(_get_cell_pass5 docs_check)"                   "" \
    "non-zero pass must not auto-fill docs_check"
  assert_eq "$(_get_cell_pass5 raw_ptr_immediates_remaining)" "" \
    "non-zero pass must not auto-fill raw_ptr_immediates_remaining"
  assert_eq "$(_get_cell_pass5 rework_items)" "" \
    "non-zero pass must not auto-fill rework_items"
  assert_eq "$(_get_cell_pass5 notes)" "" \
    "non-zero pass must not auto-fill notes"
}

test_dry_run_without_pass_id_uses_latest_scorecard_pass() {
  local slug; slug="$(unique_slug dryrun_latest)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  cat > "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | Intake baseline | 0 / 0 | 0 | not measured | 0 | 1 | 0 | pass (intake-relaxed) | pass | 0 | Intake baseline captured; semantic naming not started. |
| 5 | Test pass |  |  |  |  |  |  |  |  |  |  |
EOF

  local scorecard="projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"
  local before; before="$(<"${scorecard}")"

  local out rc
  set +e
  out="$(bash "${SYNC}" "${slug}" --dry-run 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "dry-run without pass id should use latest scorecard pass"
  assert_match "scorecard would sync: pass 5" "${out}"
  assert_eq "$(<"${scorecard}")" "${before}" "dry-run must not modify scorecard"
}

test_missing_scorecard_reports_clear_error_without_traceback() {
  local slug; slug="$(unique_slug scorecard_missing)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  rm -f "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md"

  local out rc
  set +e
  out="$(bash "${SYNC}" "${slug}" --dry-run 2>&1)"
  rc=$?
  set -e

  if [[ "${rc}" == "0" ]]; then
    fail "missing scorecard must fail"
  fi
  assert_match "error: scorecard file not found" "${out}"
  if [[ "${out}" == *"Traceback"* ]]; then
    fail "missing scorecard must not emit a Python traceback"
  fi
}

test_constant_kpi_failure_reports_clear_error_without_traceback() {
  local slug; slug="$(unique_slug scorecard_const_fail)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _make_scaffold "${slug}"
  _write_scorecard "${slug}" 0 "" "" "" "" "" "" "" "" "" ""
  printf 'MAX_ACTIVE_MAGIC_IMMEDIATES=0\n' \
    > "projects/${slug}/docs/reverse_engineering/inventory/constant_kpi.txt"
  cat > "projects/${slug}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reset:
  LDA #$2A
  RTS
ASM

  local out rc
  set +e
  out="$(bash "${SYNC}" "${slug}" --dry-run 2>&1)"
  rc=$?
  set -e

  if [[ "${rc}" == "0" ]]; then
    fail "failing constant KPI gate must fail scorecard sync"
  fi
  assert_match "error: constant KPI calculation failed" "${out}"
  if [[ "${out}" == *"Traceback"* ]]; then
    fail "constant KPI failure must not emit a Python traceback"
  fi
}
