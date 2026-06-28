#!/usr/bin/env bash
# Tests advisory Markdown provenance linting.

DOCS_PROVENANCE_LINT="${REPO_ROOT}/scripts/docs_provenance_lint.py"

test_docs_provenance_lint_reports_planted_process_provenance() {
  local root="${NESREV_TEST_TMPDIR}/docs_positive"
  mkdir -p "${root}"
  cat > "${root}/sample_DX_Systems.md" <<'MD'
# Systems

This routine was proven in pass 12.
The table is now explicit.
The helper is currently unreferenced because no live caller is proven.
The warning-baselined entry stayed in the overview.
MD

  local output rc
  set +e
  output="$(python3 "${DOCS_PROVENANCE_LINT}" --root "${root}")"
  rc=$?
  set -e

  assert_eq "${rc}" "0" "provenance lint is advisory and must exit 0"
  assert_match "WARN: docs provenance lint found" "${output}"
  assert_match "proven_in_pass|pass_provenance" "${output}"
  assert_match "now_process" "${output}"
  assert_match "unreferenced_claim" "${output}"
  assert_match "warning_baseline" "${output}"
}

test_docs_provenance_lint_ignores_false_positive_decoys() {
  local root="${NESREV_TEST_TMPDIR}/docs_decoys"
  mkdir -p "${root}/inventory"
  cat > "${root}/sample_DX_Systems.md" <<'MD'
# Systems

The bypass path passes through a handler that will pass the value unchanged.
Player recovery uses the recovered timer state after a knockdown.
The renderer skips hidden row slots and hidden tiles without process meaning.
MD
  cat > "${root}/inventory/generated.md" <<'MD'
This generated inventory note was proven in pass 99 and should be skipped.
MD
  cat > "${root}/PROGRESS_SCORECARD.md" <<'MD'
| pass_id | notes |
|---|---|
| 1 | A scorecard may say recovered in pass 1 because it is process history. |
MD

  local output
  output="$(python3 "${DOCS_PROVENANCE_LINT}" --root "${root}")"

  assert_match "OK: no docs provenance lint findings" "${output}"
}

test_project_docs_provenance_lint_wrapper_scans_clean_project_docs() {
  local slug; slug="$(unique_slug docs_provenance_clean)"
  local root="projects/${slug}"
  trap "cleanup_project ${slug}" EXIT
  mkdir -p "${root}/asm" "${root}/reference" "${root}/docs/reverse_engineering"
  cat > "${root}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="${root}/asm/${slug}.asm"
REF_NES="${root}/reference/${slug}.nes"
DOC_ROOT="${root}/docs/reverse_engineering"
SYSTEMS_DOC="${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
EOF
  cat > "${root}/docs/reverse_engineering/${slug}_DX_Systems.md" <<'MD'
# Systems

The frame service owns rendering handoff and input sampling order.
MD

  local output
  output="$(bash "${REPO_ROOT}/scripts/project_docs_provenance_lint.sh" "${slug}")"

  assert_match "OK: no docs provenance lint findings" "${output}"
}
