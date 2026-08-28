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

test_borrowed_name_and_localization_review_rules_are_durable() {
  local root_rules="${REPO_ROOT}/AGENTS.md"
  local tooling="${REPO_ROOT}/agent_playbook/TOOLING.md"
  local review="${REPO_ROOT}/agent_playbook/QUALITY_REVIEW.md"
  local audits="${REPO_ROOT}/agent_playbook/REVIEW_AUDITS.md"

  assert_match 'Carry forward the analogue.s evidence, not its identifier alone' "$(<"${root_rules}")" \
    "prior-project reuse must preserve evidence rather than blindly copy names"
  assert_match 'checker does not compare routine bodies or validate borrowed procedure[[:space:]]+names' "$(<"${tooling}")" \
    "the constant advisory must not be mistaken for procedure-name validation"
  assert_match 'clean result means only that no evidence-backed constant near-miss was[[:space:]]+found' "$(<"${tooling}")" \
    "clean constant reuse output must retain its narrow meaning"
  assert_match 'confirm the action and subject against the[[:space:]]+local body, callers, and rename-ledger rationale' "$(<"${review}")" \
    "reviewers must validate borrowed names against local behavior"
  assert_match 'name/reason disagreement is unresolved review[[:space:]]+work even when the implementations are byte-identical' "$(<"${audits}")" \
    "rename rationale must remain an independent evidence check"
  assert_match 'identify the owning[[:space:]]+non-local scope and check for every intervening non-local label or helper' "$(<"${audits}")" \
    "localization findings must prove the proposed local scope"
  assert_match 'assemble it in a[[:space:]]+disposable worktree before making the finding blocking' "$(<"${audits}")" \
    "multi-entry localization blockers must be assembled outside the implementation tree"
}

test_rename_reason_and_oam_prose_tooling_rules_are_durable() {
  local tooling="${REPO_ROOT}/agent_playbook/TOOLING.md"

  assert_match 'executable labels in the newest pass' "$(<"${tooling}")" \
    "rename/reason comparison must stay scoped to current executable work"
  assert_match 'opposing concrete classes.*payload write.*cursor/position' "$(<"${tooling}")" \
    "rename/reason comparison must stay narrower than general prose lint"
  assert_match 'finding is not proof that either field is wrong' "$(<"${tooling}")" \
    "rename/reason candidates must require body and caller review"
  assert_match 'ASM comments and live[[:space:]]+project Markdown' "$(<"${tooling}")" \
    "OAM prose ownership must cover project source and docs"
  assert_match 'excludes immutable[[:space:]]+review archives and generated inventory snapshots' "$(<"${tooling}")" \
    "OAM prose lint must preserve review provenance and generated evidence"
  assert_match '\[canonical OAM record layout\]\(ASM_STYLE.md#hardware-constants\)' "$(<"${tooling}")" \
    "OAM prose findings must route authors to the canonical owner"
}

test_hardware_allowlist_recurrence_stays_advisory() {
  local workflow="${REPO_ROOT}/agent_playbook/PASS_WORKFLOW.md"

  assert_match 'noncanonical[[:space:]]+constants[[:space:]]+independently[[:space:]]+allowlisted[[:space:]]+in[[:space:]]+peers[[:space:]]+under[[:space:]]+an[[:space:]]+exact[[:space:]]+name[[:space:]]+or[[:space:]]+same-prefix[[:space:]]+literal' "$(<"${workflow}")" \
    "hardware allowlist recurrence must retain its narrow evidence shape"
  assert_match 'Both[[:space:]]+reports[[:space:]]+are[[:space:]]+advisory' "$(<"${workflow}")" \
    "cross-project recurrence must not become an automatic promotion gate"
  assert_match '`#`[[:space:]]+comments[[:space:]]+and[[:space:]]+blank[[:space:]]+lines[[:space:]]+are[[:space:]]+ignored' "$(<"${workflow}")" \
    "hardware allowlist documentation must name its comment syntax"
}

test_process_learning_cadence_guards_against_overfitting() {
  local audits="${REPO_ROOT}/agent_playbook/REVIEW_AUDITS.md"

  assert_match 'evidence-triggered,[[:space:]]+not[[:space:]]+a[[:space:]]+per-pass[[:space:]]+quota' "$(<"${audits}")" \
    "learning candidates must not become mandatory per-pass output"
  assert_match 'candidate[[:space:]]+rate[[:space:]]+should[[:space:]]+normally[[:space:]]+decline' "$(<"${audits}")" \
    "the learning loop must expect recurring friction to settle after fixes"
  assert_match '`_None\._`[[:space:]]+is[[:space:]]+a[[:space:]]+healthy[[:space:]]+expected[[:space:]]+result' "$(<"${audits}")" \
    "an empty learning-candidate section must remain an expected healthy outcome"
  assert_match 'pause[[:space:]]+before[[:space:]]+opening[[:space:]]+another[[:space:]]+process[[:space:]]+branch' "$(<"${audits}")" \
    "persistent friction must trigger diagnosis before more process churn"
  assert_match 'project-specific[[:space:]]+behavior[[:space:]]+or[[:space:]]+reviewer[[:space:]]+preference[[:space:]]+is[[:space:]]+being[[:space:]]+misclassified' "$(<"${audits}")" \
    "triage must guard against promoting local preferences into global rules"
  assert_match 'Persistent[[:space:]]+reporting[[:space:]]+is[[:space:]]+a[[:space:]]+reason[[:space:]]+to[[:space:]]+inspect[[:space:]]+the[[:space:]]+learning[[:space:]]+loop,[[:space:]]+not[[:space:]]+evidence' "$(<"${audits}")" \
    "candidate frequency alone must not justify promotion"
  assert_match 'Batch[[:space:]]+non-blocking[[:space:]]+observations[[:space:]]+until[[:space:]]+they[[:space:]]+recur[[:space:]]+or[[:space:]]+cross[[:space:]]+the[[:space:]]+meaningful-cost[[:space:]]+threshold' "$(<"${audits}")" \
    "non-blocking friction must accumulate evidence before process work begins"
}

test_pass_wrapper_transport_and_owner_snapshot_rules_are_durable() {
  local tooling="${REPO_ROOT}/agent_playbook/TOOLING.md"
  local workflow="${REPO_ROOT}/agent_playbook/PASS_WORKFLOW.md"

  assert_match 'Make[[:space:]]+wrapper[[:space:]]+preserves[[:space:]]+literal[[:space:]]+dollar[[:space:]]+signs[[:space:]]+and[[:space:]]+apostrophes' "$(<"${tooling}")" \
    "Make wrapper docs must keep literal prose transport explicit"
  assert_match 'snapshots[[:space:]]+warning[[:space:]]+count[[:space:]]+and[[:space:]]+generated[[:space:]]+localization[[:space:]]+owner[[:space:]]+pairs' "$(<"${workflow}")" \
    "pass lifecycle docs must retain localization ownership evidence"
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
