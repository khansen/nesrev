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

  assert_eq "$(grep -cF '`HEAD~2..HEAD` range for pass 0 or `HEAD~1..HEAD` for later passes' "${spec}")" "1" \
    "review protocol must keep both pass-aware defaults on one unambiguous line"
  assert_eq "$(grep -cF 'make project-pass-review-start PROJECT=<slug> PASS=<id> [BASE=<ref>] [HEAD=<ref>] [RUN_ID=<id>] [MAX_ROUNDS=<n>] [LEARNING=<text>]' "${tooling}")" "1" \
    "Make-wrapper synopsis must advertise every supported review-run override"
  if grep -q 'non-default range, run id' "${spec}"; then
    fail "review protocol must not route supported start-pass overrides through lower-level init"
  fi
}

test_removed_generator_label_notation_is_plain_and_scoped() {
  local docs="${REPO_ROOT}/agent_playbook/DOCUMENTATION.md"
  local intake="${REPO_ROOT}/agent_playbook/NEW_PROJECT.md"

  assert_eq "$(grep -cF 'removed generator label L8123' "${docs}")" "1" \
    "DOCUMENTATION.md must keep exactly one plain-text notation example"
  if grep -qF 'removed generator label `L8123`' "${docs}"; then
    fail "removed generator-label example must be plain text, not backticked"
  fi
  assert_match 'return-address dispatcher' "$(<"${intake}")" \
    "intake rules must identify disposable inline-payload anchors"
  assert_match 'orphan `\.DB` region head' "$(<"${intake}")" \
    "intake rules must distinguish orphan data boundaries that stay retained"
  assert_match 'pointer_targets\.csv.*preceding code label' "$(<"${intake}")" \
    "intake rules must disclose the generated-inventory re-anchoring effect"
}

test_intentional_kpi_regression_convention_is_durable() {
  local workflow="${REPO_ROOT}/agent_playbook/PASS_WORKFLOW.md"
  local review="${REPO_ROOT}/agent_playbook/QUALITY_REVIEW.md"

  assert_eq "$(grep -cF 'intentional-kpi-regression: <metric> <before> -> <after>; <semantic/readability reason>' "${workflow}")" "1" \
    "pass workflow must keep one canonical intentional-regression marker"
  assert_match 'exact emitted metric name and measured final values' "$(<"${workflow}")" \
    "intentional KPI regressions must remain comparable"
  assert_match 'kpi-measurement-change: <metric>; <old/new basis>' "$(<"${workflow}")" \
    "measurement-definition changes must not masquerade as code regressions"
  assert_match 'unexplained backward movement as incomplete review work' "$(<"${review}")" \
    "quality review must reject unexplained KPI regressions"
}

test_inline_dispatch_and_oam_comment_rules_are_durable() {
  local docs="${REPO_ROOT}/agent_playbook/DOCUMENTATION.md"
  local review="${REPO_ROOT}/agent_playbook/QUALITY_REVIEW.md"
  local oam_order_count

  assert_match '\[canonical OAM record layout\]\(ASM_STYLE.md#hardware-constants\)' "$(<"${docs}")" \
    "project docs must point to the canonical hardware-layout section"
  oam_order_count="$(
    grep -RF '[Y, tile, attributes, X]' \
      "${REPO_ROOT}/AGENTS.md" "${REPO_ROOT}/agent_playbook" | wc -l | tr -d ' '
  )"
  assert_eq "${oam_order_count}" "1" \
    "ASM_STYLE must be the sole playbook owner of the standard OAM field order"
  assert_match 'control-flow payload, not a standalone data table' "$(<"${docs}")" \
    "inline return-address handler words must stay exempt from data-table boilerplate"
  assert_match 'do not[[:space:]]+add boilerplate `Format:` or `Used by:` lines' "$(<"${docs}")" \
    "the inline-dispatch exception must forbid both redundant comment lines"
  assert_match 'Document only a non-obvious[[:space:]]+selector bias, encoding, or control-flow constraint' "$(<"${docs}")" \
    "the exemption must retain documentation for non-obvious inline contracts"
  assert_match 'Keep such payloads[[:space:]]+unlabeled unless a real source reference requires the boundary' "$(<"${docs}")" \
    "inline payload labels must not become unresolvable data-label KPI debt"
  assert_match 'standard OAM template may use.*OAM_FIELD_\*' "$(<"${docs}")" \
    "project comments must be able to cite the canonical OAM field family"
  assert_match 'describe locally only project-specific encoding or invariants' "$(<"${docs}")" \
    "canonical OAM prose must not erase project-specific format constraints"
  assert_match 'standard four-byte hardware OAM record alone does not require a[[:space:]]+project format doc' "$(<"${review}")" \
    "reviewers must not demand duplicate standard OAM format prose"
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
