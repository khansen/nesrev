#!/usr/bin/env bash

test_agent_playbook_validator_rejects_empty_anchored_section() {
  local playbook="${REPO_ROOT}/agent_playbook/ASM_STYLE.md"
  local backup="${NESREV_TEST_TMPDIR}/ASM_STYLE.md.backup"
  cp "${playbook}" "${backup}"
  trap "cp '${backup}' '${playbook}'" EXIT

  {
    printf '\n<a id="empty-section-fixture"></a>\n'
    printf '## Empty Section Fixture\n'
  } >> "${playbook}"

  local out rc
  set +e
  out="$(python3 "${REPO_ROOT}/scripts/check_agent_playbooks.py" --strict 2>&1)"
  rc=$?
  set -e
  cp "${backup}" "${playbook}"
  trap - EXIT

  assert_eq "${rc}" "1" "empty anchored section should fail validation"
  assert_match "empty-section-fixture|Empty Section Fixture|has no body" "${out}"
}

test_trace_analyzer_refuses_configured_canonical_summary() {
  local analyzer="${REPO_ROOT}/agent_playbook/templates/trace/analyze_trace.sh"
  local log="${REPO_ROOT}/agent_playbook/templates/trace/synthetic_trace.log"
  local summary="${NESREV_TEST_TMPDIR}/ENTITY_BEHAVIOR_TRANSITIONS.md"

  local out rc
  set +e
  out="$(
    CANONICAL_TRACE_DOC="${summary}" \
      bash "${analyzer}" "${log}" "${summary}" 2>&1
  )"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "trace analyzer must reject configured canonical summary overwrite"
  assert_match "refusing to overwrite curated evidence doc" "${out}"
}
