#!/usr/bin/env bash
# Tests for project-pass review packet generation.

PACKET_SCRIPT="${REPO_ROOT}/scripts/project_pass_review_packet.sh"

_init_packet_repo() {
  local repo="$1" slug="$2"
  mkdir -p \
    "${repo}/scripts" \
    "${repo}/projects/${slug}/asm" \
    "${repo}/projects/${slug}/build" \
    "${repo}/projects/${slug}/reference" \
    "${repo}/projects/${slug}/docs/crosswalk" \
    "${repo}/projects/${slug}/docs/reverse_engineering/inventory"

  cp "${REPO_ROOT}/scripts/project_pass_review_packet.sh" "${repo}/scripts/"
  cp "${REPO_ROOT}/scripts/project_common.sh" "${repo}/scripts/"
  cp "${REPO_ROOT}/scripts/project_policy_config_check.py" "${repo}/scripts/"
  cp "${REPO_ROOT}/scripts/proof_debt.py" "${repo}/scripts/"
  cp "${REPO_ROOT}/scripts/review_packet_evidence.py" "${repo}/scripts/"
  cp "${REPO_ROOT}/scripts/process_friction.py" "${repo}/scripts/"
  printf 'projects/*/reference/\nprojects/*/build/\n' > "${repo}/.gitignore"

  cat > "${repo}/projects/${slug}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="projects/${slug}/asm/${slug}.asm"
REF_NES="projects/${slug}/reference/${slug}.nes"
DOC_ROOT="projects/${slug}/docs/reverse_engineering"
SYSTEMS_DOC="projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
NESREV_RECOVERY_STATUS="none"
OUT_BIN="projects/${slug}/build/${slug}.o"
EOF
  cat > "${repo}/projects/${slug}/asm/${slug}.asm" <<'EOF'
L1234:
  JSR L1234
  JMP L1234
L1235:
  RTS
EOF
  python3 - "${repo}/projects/${slug}/reference/${slug}.nes" <<'PY'
import sys
from pathlib import Path
Path(sys.argv[1]).write_bytes(b'NES\x1a' + bytes([1, 0]) + bytes(10) + bytes(16384))
PY
  : > "${repo}/projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
  cat > "${repo}/projects/${slug}/docs/crosswalk/TERMINOLOGY_CROSSWALK.md" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
| widget | `RunWidget` | high | fixture |
EOF
  cat > "${repo}/projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| pass_id | focus | labels_remaining | verify | docs_check | rework_items | notes |
|---|---|---|---|---|---|---|
| 0 | Intake baseline | 1 / 1 | pass | pass | 0 | Intake baseline captured. |
EOF
  printf 'old_name,new_name,reason,confidence,pass_id\n' \
    > "${repo}/projects/${slug}/docs/reverse_engineering/inventory/renames.csv"
  cat > "${repo}/projects/${slug}/docs/reverse_engineering/SEMANTIC_CLAIMS.md" <<'EOF'
# Semantic Claims

## Claim: widget

Subject: RunWidget
Kind: routine contract
Subsystem: fixture
Claim: Fixture claim.
Confidence: high
Evidence:
- Writers/Producers: fixture
- Readers/Consumers: fixture
- Cross-check: fixture
Caveats:
- none
Canonical docs:
- MEMORY_MAP.md
EOF

  git -C "${repo}" init -q
  git -C "${repo}" config user.email "tests@example.invalid"
  git -C "${repo}" config user.name "Tests"
  git -C "${repo}" config commit.gpgsign false
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Fixture base"

  cat > "${repo}/projects/${slug}/asm/${slug}.asm" <<'EOF'
RunWidget:
  JSR RunWidget
  JMP RunWidget
@@done:
  RTS
EOF
  cat >> "${repo}/projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
L1234,RunWidget,fixture rename,high,1
EOF
  cat >> "${repo}/projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'
| 1 | Widget pass | 0 / 0 | pass | pass | 0 | Named widget. |
EOF
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Fixture real pass"

  cat >> "${repo}/projects/${slug}/docs/reverse_engineering/inventory/renames.csv" <<'EOF'
L1234,MissingWidgetHelper,fixture phantom rename,medium,1
EOF
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Fixture ledger follow-up"
}

_write_make_stub() {
  local path="$1"
  cat > "${path}" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
echo "stub make $*"
if [[ -n "${PACKET_TEST_CACHE_PATH:-}" && "$*" != project-pass-prep* && ! -f "${PACKET_TEST_CACHE_PATH}" ]]; then
  echo "cold cache was not prepared" >&2
  exit 27
fi
case "$*" in
  project-pass-prep*)
    [[ "${PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW:-}" == 0 ]] || { echo 'prep would rewrite authored queue'; exit 28; }
    if [[ -n "${PACKET_TEST_DIRTY_PATH:-}" ]]; then printf '\nchanged\n' >> "${PACKET_TEST_DIRTY_PATH}"; fi
    if [[ -n "${PACKET_TEST_CACHE_PATH:-}" ]]; then touch "${PACKET_TEST_CACHE_PATH}"; fi
    exit "${PACKET_TEST_PREP_EXIT:-0}" ;;
  project-next-pass*) echo "Top generated evidence bucket: identity_pass" ;;
  project-verify*) echo "Verification complete"; exit "${PACKET_TEST_VERIFY_EXIT:-0}" ;;
  project-process-check*) echo "Process evidence"; exit "${PACKET_TEST_PROCESS_EXIT:-0}" ;;
  project-docs-check*) echo "Doc consistency checks passed"; exit "${PACKET_TEST_DOCS_EXIT:-0}" ;;
esac
EOF
  chmod +x "${path}"
}

test_project_pass_review_packet_emits_complete_range_and_head_gates() {
  local repo="${NESREV_TEST_TMPDIR}/packet_repo"
  local slug; slug="$(unique_slug packet)"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"

  local base head out
  base="$(git -C "${repo}" rev-parse HEAD~2)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  out="$(cd "${repo}" && MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" \
    bash "scripts/project_pass_review_packet.sh" "${slug}" "${base}" "${head}")"

  assert_match "Fixture real pass" "${out}" \
    "packet must enumerate every commit in the reviewed range"
  assert_match "Fixture ledger follow-up" "${out}" \
    "packet must include the second commit, not only the real pass summary"
  assert_match "## Range Summary" "${out}" \
    "packet must include the mandated range-summary section"
  assert_match "Project commits in range: \`2\`" "${out}" \
    "packet must summarize the number of reviewed project commits"
  assert_match "Rename ledger rows: \`\\+2 this range \\(0 -> 2 total\\)\`" "${out}" \
    "packet must summarize range-level rename ledger growth"
  assert_match "Unresolved LXXXX labels: \`2 / 4 -> 0 / 0 \\(delta -2 / -4\\)\`" "${out}" \
    "packet must summarize unresolved-label movement across the range"
  assert_match "LXXXX-sourced rename rows: \`\\+2 this range\`" "${out}" \
    "packet must count added rename rows that started from LXXXX labels"
  assert_match "LXXXX definition removals: \`2 removed; 1 matched to LXXXX-sourced rename rows; 1 without rename row\`" "${out}" \
    "packet must reconcile LXXXX removals against LXXXX-sourced rename rows"
  assert_match "LXXXX removals without rename row: \`L1235\`" "${out}" \
    "packet must identify removed LXXXX definitions not explained by rename rows"
  assert_match "LXXXX rename rows without definition removal: \`1 \\(L1234->MissingWidgetHelper\\)\`" "${out}" \
    "packet must identify LXXXX-sourced rename rows not explained by removed definitions"
  assert_match "State: \`review_head ${head}\`" "${out}" \
    "gate evidence must be labelled with the reviewed SHA"
  assert_match "stub make project-verify PROJECT=${slug}" "${out}" \
    "packet must run the verify gate command"
  assert_match "MissingWidgetHelper" "${out}" \
    "packet must expose review-ledger deltas"
  assert_match "Top generated evidence bucket: identity_pass" "${out}" \
    "packet must include generated next-pass evidence"
  printf '%s\n' "${out}" > "${NESREV_TEST_TMPDIR}/complete-packet.md"
  python3 - "${NESREV_TEST_TMPDIR}/complete-packet.md" "${head}" "${slug}" <<'PY'
import sys
from pathlib import Path
sys.path.insert(0, 'scripts')
from review_packet_evidence import validate_packet
validate_packet(Path(sys.argv[1]).read_text(), sys.argv[2], sys.argv[3])
PY
}

test_packet_complete_inventory_includes_root_only_and_reverted_paths() {
  local repo="${NESREV_TEST_TMPDIR}/root_inventory" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  local base head out
  base="$(git -C "${repo}" rev-parse HEAD~2)"
  printf 'Root coordination\n' > "${repo}/COORDINATION.md"
  git -C "${repo}" add COORDINATION.md
  git -C "${repo}" commit -q -m 'Root-only coordination change'
  git -C "${repo}" rm -q COORDINATION.md
  git -C "${repo}" commit -q -m 'Revert coordination text'
  head="$(git -C "${repo}" rev-parse HEAD)"
  out="$(cd "${repo}" && MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo "${base}" "${head}")"
  assert_match 'Root-only coordination change' "${out}"
  assert_match 'COORDINATION.md' "${out}"
  assert_match 'Complete Changed Path Inventory' "${out}"
}

test_packet_cold_cache_is_prepared_before_dependent_commands() {
  local repo="${NESREV_TEST_TMPDIR}/cold_cache" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  local head out marker="${NESREV_TEST_TMPDIR}/prepared"
  head="$(git -C "${repo}" rev-parse HEAD)"
  out="$(cd "${repo}" && PACKET_TEST_CACHE_PATH="${marker}" MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo HEAD~2 "${head}")"
  [[ -f "${marker}" ]] || fail 'cache preparation was never run'
  assert_match '"status": "pass"' "${out}"
  if [[ "${out}" == *'cold cache was not prepared'* ]]; then fail 'dependent command ran before cache preparation'; fi
}

test_packet_terminal_summary_retains_every_gate_failure() {
  local repo="${NESREV_TEST_TMPDIR}/failed_gates" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  local head out
  head="$(git -C "${repo}" rev-parse HEAD)"
  out="$(cd "${repo}" && PACKET_TEST_VERIFY_EXIT=3 PACKET_TEST_PROCESS_EXIT=4 PACKET_TEST_DOCS_EXIT=5 MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo HEAD~2 "${head}")"
  assert_match '"project-verify exit 3"' "${out}"
  assert_match '"project-process-check exit 4"' "${out}"
  assert_match '"project-docs-check exit 5"' "${out}"
  assert_match 'Packet generation: complete' "${out}"
  assert_match '"status": "fail"' "${out}"
}

test_packet_missing_fixture_marks_all_gates_not_run() {
  local repo="${NESREV_TEST_TMPDIR}/missing_fixture" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  rm "${repo}/projects/demo/reference/demo.nes"
  local head out
  head="$(git -C "${repo}" rev-parse HEAD)"
  out="$(cd "${repo}" && MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo HEAD~2 "${head}")"
  assert_match 'missing or empty reference input' "${out}"
  assert_match '"project-verify not run"' "${out}"
  assert_match '"project-process-check not run"' "${out}"
  assert_match '"project-docs-check not run"' "${out}"
  if [[ "${out}" == *'stub make project-verify'* ]]; then fail 'verify ran with missing fixture'; fi
}

test_packet_failed_cache_preparation_cannot_be_hidden_by_gate_stubs() {
  local repo="${NESREV_TEST_TMPDIR}/bad_cache" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  local head out
  head="$(git -C "${repo}" rev-parse HEAD)"
  out="$(cd "${repo}" && PACKET_TEST_PREP_EXIT=6 MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo HEAD~2 "${head}")"
  assert_match '"cache-preparation exit 6"' "${out}"
  assert_match '"project-verify not run"' "${out}"
}

test_packet_mid_generation_tracked_change_blocks_later_gates() {
  local repo="${NESREV_TEST_TMPDIR}/changed_state" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  local out
  out="$(cd "${repo}" && PACKET_TEST_DIRTY_PATH="${repo}/projects/demo/asm/demo.asm" MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo HEAD~2 HEAD)"
  assert_match '"state_integrity": "fail"' "${out}"
  assert_match '"project-verify not run"' "${out}"
  if [[ "${out}" == *'stub make project-verify'* ]]; then fail 'verify ran after tracked state changed'; fi
}

test_packet_supplied_tool_and_fixture_hash_mismatches_block_gates() {
  local repo="${NESREV_TEST_TMPDIR}/mismatched_inputs" slug="demo"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"
  local out
  out="$(cd "${repo}" && REVIEW_EXPECTED_XASM_SHA256=invalid REVIEW_EXPECTED_REF_SHA256=invalid MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" bash scripts/project_pass_review_packet.sh demo HEAD~2 HEAD)"
  assert_match 'assembler SHA-256 mismatch' "${out}"
  assert_match 'reference SHA-256 mismatch' "${out}"
  assert_match '"project-verify not run"' "${out}"
}

test_project_pass_review_packet_rejects_non_checked_out_head() {
  local repo="${NESREV_TEST_TMPDIR}/packet_repo_mismatch"
  local slug; slug="$(unique_slug packet_mismatch)"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"

  local head output rc
  head="$(git -C "${repo}" rev-parse HEAD)"
  git -C "${repo}" checkout -q HEAD~1

  set +e
  output="$(cd "${repo}" && MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" \
    bash "scripts/project_pass_review_packet.sh" "${slug}" HEAD~1 "${head}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "packet generation must reject stale checkout state"
  assert_match "review head must be checked out" "${output}"
}

test_project_pass_review_packet_rejects_tracked_dirty_state() {
  local repo="${NESREV_TEST_TMPDIR}/packet_repo_dirty"
  local slug; slug="$(unique_slug packet_dirty)"
  _init_packet_repo "${repo}" "${slug}"
  _write_make_stub "${NESREV_TEST_TMPDIR}/make-stub"

  local base head output rc
  base="$(git -C "${repo}" rev-parse HEAD~2)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  printf '\n; dirty\n' >> "${repo}/projects/${slug}/asm/${slug}.asm"

  set +e
  output="$(cd "${repo}" && MAKE_BIN="${NESREV_TEST_TMPDIR}/make-stub" \
    bash "scripts/project_pass_review_packet.sh" "${slug}" "${base}" "${head}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "packet generation must reject tracked dirty state"
  assert_match "tracked working tree changes" "${output}"
}

test_project_pass_review_packet_make_target_requires_range() {
  local output rc
  set +e
  output="$(make project-pass-review-packet PROJECT=missing 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "make target must require BASE and HEAD"
  assert_match "usage: make project-pass-review-packet" "${output}"
}
