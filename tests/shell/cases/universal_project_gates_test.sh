#!/usr/bin/env bash
# Tests the repository-wide project quality contract and its escape-hatch guards.

POLICY_CHECK="${REPO_ROOT}/scripts/project_policy_config_check.py"
ARTIFACT_CHECK="${REPO_ROOT}/scripts/project_artifact_manifest.py"

_write_policy_conf() {
  local path="$1"
  cat > "${path}" <<'EOF'
NESREV_RECOVERY_STATUS="none"
EOF
}

test_project_policy_rejects_every_removed_quality_switch() {
  local conf="${NESREV_TEST_TMPDIR}/project.conf"
  local field
  for field in \
    SEMANTIC_CLAIMS_REQUIRED \
    PROCEDURE_CONTRACTS_REQUIRED \
    LEGACY_RETROFIT_REQUIRED \
    WORKING_NOTES_MATURITY_REQUIRED \
    PROOF_DEBT_REQUIRED \
    DATA_FORMAT_TARGETS_REQUIRED \
    DATA_BLOB_DISPOSITIONS_REQUIRED \
    EMBEDDED_POINTER_AUDIT_REQUIRED \
    BASE_READABILITY_REQUIRED \
    BASE_READABILITY_EQU_REQUIRED \
    SCORECARD_LIFECYCLE_REQUIRED; do
    _write_policy_conf "${conf}"
    printf '%s="0"\n' "${field}" >> "${conf}"
    local output rc
    set +e
    output="$(python3 "${POLICY_CHECK}" config "${conf}" 2>&1)"
    rc=$?
    set -e
    assert_eq "${rc}" "1" "${field} must be rejected"
    assert_match "${field} is a removed quality-policy switch" "${output}"
  done
}

test_project_policy_requires_explicit_nonlegacy_recovery_fact() {
  local conf="${NESREV_TEST_TMPDIR}/project.conf"
  : > "${conf}"
  assert_exit 1 python3 "${POLICY_CHECK}" config "${conf}"
  printf 'NESREV_RECOVERY_STATUS="legacy"\n' > "${conf}"
  assert_exit 1 python3 "${POLICY_CHECK}" config "${conf}"
  printf 'NESREV_RECOVERY_STATUS="none"\n' > "${conf}"
  assert_exit 0 python3 "${POLICY_CHECK}" config "${conf}"
  printf 'NESREV_RECOVERY_STATUS="configured"\n' > "${conf}"
  assert_exit 0 python3 "${POLICY_CHECK}" config "${conf}"
}

test_project_policy_rejects_pending_for_tracked_corpus_validation() {
  local conf="${NESREV_TEST_TMPDIR}/project.conf"
  printf 'NESREV_RECOVERY_STATUS="pending"\n' > "${conf}"
  assert_exit 0 python3 "${POLICY_CHECK}" config "${conf}"
  assert_exit 1 python3 "${POLICY_CHECK}" config "${conf}" --tracked
}

test_project_policy_rejects_undeclared_config_controls() {
  local conf="${NESREV_TEST_TMPDIR}/project.conf"
  _write_policy_conf "${conf}"
  printf 'PROJECT_FAST_POLICY="0"\n' >> "${conf}"
  local output rc
  set +e
  output="$(python3 "${POLICY_CHECK}" config "${conf}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "undeclared project.conf controls must fail closed"
  assert_match "PROJECT_FAST_POLICY is not a declared project fact" "${output}"
}

test_project_policy_rejects_disabled_kpi_sentinel() {
  local kpis="${NESREV_TEST_TMPDIR}/kpis.conf"
  printf 'MAX_ACTIVE_MAGIC_IMMEDIATES=999999\n' > "${kpis}"
  local output rc
  set +e
  output="$(python3 "${POLICY_CHECK}" kpis "${kpis}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "sentinel KPI ceiling must fail"
  assert_match "disabled/sentinel ceiling" "${output}"
  printf 'MAX_ACTIVE_MAGIC_IMMEDIATES=17\n' > "${kpis}"
  assert_exit 0 python3 "${POLICY_CHECK}" kpis "${kpis}"
}

test_universal_wrapper_contract_is_complete() {
  python3 "${POLICY_CHECK}" wrappers "${REPO_ROOT}" >/dev/null
}

test_universal_wrapper_contract_rejects_presence_guard_mutation() {
  local repo="${NESREV_TEST_TMPDIR}/repo"
  mkdir -p "${repo}"
  cp -R "${REPO_ROOT}/scripts" "${repo}/scripts"
  python3 - "${repo}/scripts/project_verify.sh" <<'PY'
import sys
from pathlib import Path
path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
text = text.replace(
    'bash "${SCRIPT_DIR}/embedded_pointer_targets_check.sh" \\\n',
    'if [[ -f "${EMBEDDED_POINTER_TARGETS_FILE}" ]]; then\n'
    'bash "${SCRIPT_DIR}/embedded_pointer_targets_check.sh" \\\n',
    1,
)
path.write_text(text + "\nfi\n", encoding="utf-8")
PY
  local output rc
  set +e
  output="$(python3 "${POLICY_CHECK}" wrappers "${repo}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "restored presence guard must fail wrapper contract"
  assert_match "may supply a path but may not select whether its quality check runs" "${output}"
}

test_universal_wrapper_contract_rejects_unclassified_config_conditional() {
  local repo="${NESREV_TEST_TMPDIR}/repo-config-condition"
  mkdir -p "${repo}"
  cp -R "${REPO_ROOT}/scripts" "${repo}/scripts"
  printf '\nif [[ "${PROJECT_FAST_POLICY:-0}" == "1" ]]; then :; fi\n' \
    >> "${repo}/scripts/project_process_check.sh"
  local output rc
  set +e
  output="$(python3 "${POLICY_CHECK}" wrappers "${repo}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "unclassified config-derived policy branch must fail"
  assert_match "unclassified config-style variable PROJECT_FAST_POLICY" "${output}"
}

test_universal_wrapper_contract_rejects_recovery_policy_mutation() {
  local repo="${NESREV_TEST_TMPDIR}/repo-recovery-condition"
  mkdir -p "${repo}"
  cp -R "${REPO_ROOT}/scripts" "${repo}/scripts"
  printf '\nif [[ "${NESREV_RECOVERY_STATUS}" == "configured" ]]; then :; fi\n' \
    >> "${repo}/scripts/project_process_check.sh"
  assert_exit 1 python3 "${POLICY_CHECK}" wrappers "${repo}"
}

test_universal_wrapper_contract_rejects_advisory_crash_suppression() {
  local repo="${NESREV_TEST_TMPDIR}/repo-advisory-crash"
  mkdir -p "${repo}"
  cp -R "${REPO_ROOT}/scripts" "${repo}/scripts"
  python3 - "${repo}/scripts/project_process_check.sh" <<'PY'
import sys
from pathlib import Path
path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
text = text.replace(
    '  --projects-root projects\n',
    '  --projects-root projects || true\n',
    1,
)
path.write_text(text, encoding="utf-8")
PY
  local output rc
  set +e
  output="$(python3 "${POLICY_CHECK}" wrappers "${repo}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "advisory checker crash suppression must fail"
  assert_match "operational failure is suppressed" "${output}"
}

test_aggregate_contract_rejects_project_allowlist_mutation() {
  local repo="${NESREV_TEST_TMPDIR}/repo-aggregate-allowlist"
  mkdir -p "${repo}"
  cp -R "${REPO_ROOT}/scripts" "${repo}/scripts"
  sed -i.bak \
    "s/git ls-files 'projects\/\*\/project.conf'/printf '%s\\n' projects\/one\/project.conf # allowlist/" \
    "${repo}/scripts/projects_policy_check.sh"
  assert_exit 1 python3 "${POLICY_CHECK}" wrappers "${repo}"
}

test_canonical_artifact_manifest_reports_every_missing_input() {
  local docs="${NESREV_TEST_TMPDIR}/docs"
  mkdir -p "${docs}/inventory"
  local output rc
  set +e
  output="$(python3 "${ARTIFACT_CHECK}" fixture "${docs}" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "missing canonical artifacts must fail"
  assert_match "SEMANTIC_CLAIMS.md" "${output}"
  assert_match "data_format_targets.csv" "${output}"
  assert_match "proof_debt_acknowledged.csv" "${output}"
}

test_aggregate_commands_discover_tracked_projects() {
  local policy ci
  policy="$(<"${REPO_ROOT}/scripts/projects_policy_check.sh")"
  ci="$(<"${REPO_ROOT}/scripts/projects_ci.sh")"
  assert_match "git ls-files 'projects/\*/project.conf'" "${policy}"
  assert_match "git ls-files 'projects/\*/project.conf'" "${ci}"
  assert_not_match 'PROJECTS=|allowlist' "${policy}"
  assert_not_match 'PROJECTS=|allowlist' "${ci}"
}
