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
  cp "${REPO_ROOT}/scripts/proof_debt.py" "${repo}/scripts/"

  cat > "${repo}/projects/${slug}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="projects/${slug}/asm/${slug}.asm"
REF_NES="projects/${slug}/reference/${slug}.nes"
DOC_ROOT="projects/${slug}/docs/reverse_engineering"
SYSTEMS_DOC="projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
OUT_BIN="projects/${slug}/build/${slug}.o"
PROOF_DEBT_REQUIRED="1"
EOF
  cat > "${repo}/projects/${slug}/asm/${slug}.asm" <<'EOF'
L1234:
  JSR L1234
  JMP L1234
EOF
  : > "${repo}/projects/${slug}/reference/${slug}.nes"
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
case "$*" in
  project-next-pass*) echo "Top generated evidence bucket: identity_pass" ;;
  project-verify*) echo "Verification complete" ;;
  project-process-check*) echo "OK: project process checks passed" ;;
  project-docs-check*) echo "Doc consistency checks passed" ;;
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
  assert_match "Unresolved LXXXX labels: \`1 / 3 -> 0 / 0 \\(delta -1 / -3\\)\`" "${out}" \
    "packet must summarize unresolved-label movement across the range"
  assert_match "State: \`review_head ${head}\`" "${out}" \
    "gate evidence must be labelled with the reviewed SHA"
  assert_match "stub make project-verify PROJECT=${slug}" "${out}" \
    "packet must run the verify gate command"
  assert_match "MissingWidgetHelper" "${out}" \
    "packet must expose review-ledger deltas"
  assert_match "Top generated evidence bucket: identity_pass" "${out}" \
    "packet must include generated next-pass evidence"
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
