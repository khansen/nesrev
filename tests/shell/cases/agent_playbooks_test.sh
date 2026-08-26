#!/usr/bin/env bash

test_nesrev_control_examples_keep_literal_schema_headers() {
  local tooling="${REPO_ROOT}/agent_playbook/TOOLING.md"

  assert_eq "$(grep -c '^start|count$' "${tooling}")" "2" \
    "code- and data-pointer examples must show literal start|count headers"
  assert_eq "$(grep -c '^callee|layout$' "${tooling}")" "1" \
    "inline-call examples must show the required literal header"
  assert_eq "$(grep -c '^start|length$' "${tooling}")" "1" \
    "data-range examples must show the required literal header"
  assert_match "first nonblank, non-comment line" "$(<"${tooling}")" \
    "recovery-control docs must explain where required schema headers belong"
}

test_agent_review_protocol_records_pass_aware_default_range() {
  local spec="${REPO_ROOT}/AGENT_REVIEW_PROTOCOL_SPEC.md"
  local tooling="${REPO_ROOT}/agent_playbook/TOOLING.md"

  assert_match 'HEAD~2\.\.HEAD.*pass 0' "$(<"${spec}")" \
    "review protocol must record the pass-0 two-commit range"
  assert_match 'HEAD~1\.\.HEAD.*later passes' "$(<"${spec}")" \
    "review protocol must retain the later-pass one-commit range"
  assert_match 'RUN_ID=<id>.*MAX_ROUNDS=<n>' "$(<"${tooling}")" \
    "Make-wrapper docs must advertise supported review-run overrides"
  if grep -q 'non-default range, run id' "${spec}"; then
    fail "review protocol must not route supported start-pass overrides through lower-level init"
  fi
}

test_removed_generator_label_notation_is_plain_and_scoped() {
  local docs="${REPO_ROOT}/agent_playbook/DOCUMENTATION.md"
  local intake="${REPO_ROOT}/agent_playbook/NEW_PROJECT.md"
  local notation_line

  notation_line="$(grep -F 'removed generator label L8123' "${docs}")"
  if [[ "${notation_line}" == *'`'* ]]; then
    fail "removed generator-label example must be plain text, not backticked"
  fi
  assert_match 'return-address dispatcher' "$(<"${intake}")" \
    "intake rules must identify disposable inline-payload anchors"
  assert_match 'orphan `\.DB` region head' "$(<"${intake}")" \
    "intake rules must distinguish orphan data boundaries that stay retained"
  assert_match 'pointer_targets\.csv.*preceding code label' "$(<"${intake}")" \
    "intake rules must disclose the generated-inventory re-anchoring effect"
}

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
