# Process Improvement Plan

Status: PI-1 through PI-5 and queue receipts are merged, including PI-2 runtime
delivery in [PR #105](https://github.com/khansen/nesrev/pull/105). PI-6 is merged
in [PR #141](https://github.com/khansen/nesrev/pull/141); PI-7 is merged in
[PR #142](https://github.com/khansen/nesrev/pull/142). PI-8 is merged in
[PR #143](https://github.com/khansen/nesrev/pull/143).
The first observation window is closed: the reviewer resumed and completed the
disclosed outstanding check. [PI-9](#pi-9-historical-provenance) phase A is merged
in [PR #147](https://github.com/khansen/nesrev/pull/147) and locally integrated
at the completed pass boundary. Phase B's separately reviewed provenance
restorations, later rename links and archive recovery are integrated on the
local-only corpus branch. Unresolved source-history gaps remain explicit.
The observation assessment and other investigations below are
not implementation or additional-pass authorization.
Queue triage on 2026-10-07 added bounded follow-ups below without starting
implementation or another observation run.
Raw-RAM input validation is merged in [PR #151](https://github.com/khansen/nesrev/pull/151)
and integrated locally. The documentation-reference classifier follow-up is
deferred pending evidence of recurring disruption.
The corrected-claim propagation wording is merged in
[PR #153](https://github.com/khansen/nesrev/pull/153) and integrated locally;
it adds no runtime gate or project pass. The interrupted-review assessment is
complete: pending states preserve unfinished notes, and archival preserves
limitations recorded in submitted reviews. The prompt clarification is merged
in [PR #155](https://github.com/khansen/nesrev/pull/155), independently approved
at `3e87e449e`, and integrated locally. No new state or completion gate is
introduced. The inline-dispatch boundary assessment is merged in
[PR #156](https://github.com/khansen/nesrev/pull/156) and integrated locally,
after independent approval at `dff78e29d` and optional precision refinements.
Existing unused-symbol warnings flagged the affected labels, but
unsupported baseline explanations obscured their significance.
A warning/raw-byte join separates additional synthetic cases without proving
consumption. Production integration is deferred pending measurement of its
noise and added value over existing warnings.
The embedded-pointer advisory change is merged in
[PR #157](https://github.com/khansen/nesrev/pull/157), independently approved
at `c05d92f57`, and integrated locally.
It retains discovery and evidence refusals while removing heuristic matches'
authority to fail verification. The structured proof replacement stays deferred.
The second window's explicit-deferral and no-candidate fixes are merged in
[PR #159](https://github.com/khansen/nesrev/pull/159) and
[PR #160](https://github.com/khansen/nesrev/pull/160); its assessment is merged
in [PR #161](https://github.com/khansen/nesrev/pull/161). They were integrated
before the separately authorized third five-pass window. Its
[assessment](#third-window-assessment) selects a bounded
[checkout-inspection follow-up](#checkout-inspection-permissions).
Updated 2026-10-15.

This plan prioritizes reproducible tooling gaps found during friction-queue
review over repeated reports of already-fixed problems. It describes shared
contracts and acceptance criteria; corpus-specific evidence and progress
remain on the local-only corpus branch.

<a id="recommended-order"></a>
## Recommended order

[PI-9 phase B](#pi-9-provenance-restoration) is complete within its reviewed
audit scope. Its committed evidence preserves original records, later rename
links and dated amendments without depending on retained Git history.

The [corrected-claim propagation wording](#triage-claim-propagation) was selected
ahead of the investigations below because independent passes repeatedly left
contradictory current artifacts. That bounded wording change is merged and
integrated; its effect on recurrence has not yet been measured.

The [interrupted-review prompt clarification](#interrupted-review-candidate)
is also merged and integrated. Existing state, archive and admission behavior
are unchanged; its effect on live interruption behavior remains unmeasured.

The bounded advisory implementation following the
[embedded-pointer feasibility audit](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#embedded-pointer-audit)
is merged in [PR #157](https://github.com/khansen/nesrev/pull/157) and integrated.
It keeps discovery, labels heuristic matches as unproven, and preserves
operational failures and independent pointer gates. The linked plan owns the
contract. No replacement proof engine or xasm extension is part of this change.

The [inline-dispatch assessment](#dispatch-boundary-candidate) is published.
Its warning/raw-byte join can surface review candidates, including mixed tails,
but cannot distinguish never-selected, pointer-shaped tails from consumed
entries. Production integration remains deferred until a separately selected
evaluation measures noise and incremental value. Complete selector proof is
not a prerequisite for that evaluation; no additional project pass is authorized.

The second window's [explicit-deferral integrity](#explicit-deferral-integrity)
and [no-candidate wording](#learning-candidate-noop) fixes are integrated.
The [checkout-inspection follow-up](#checkout-inspection-permissions) was
merged and its refreshed profile passed live checkout inspection. The next
single-pass observation selected a [runtime/inspection follow-up](#runtime-inspection-permissions)
for the remaining manual interventions. Keep corpus cleanup
and original evidence on the local corpus
branch. Any subsequent semantic work uses the user's explicit run limit;
this shared plan does not grant additional passes.
PI-1 through PI-5 and the queue-receipt
prerequisite are delivered; their implementation and activation records remain
below. Start each follow-up with a current reproducer and a bounded contract.
If existing tooling already resolves the observation, record that evidence and
retriage it instead of adding another gate. Keep other undecided friction
candidates in their project queues.

Each implementation should include a failing regression fixture, positive
controls, and representative cross-project checks. Follow the existing
[process-change review requirements](agent_playbook/REVIEW_AUDITS.md#process-change-review-sanity-checks),
including mutation tests in a disposable worktree and explicit checked,
skipped, and failed results. Do not convert uncertain heuristics into hard
gates merely to increase coverage.

<a id="observation-period"></a>
## Observation period

Status: the first five-pass window is closed, with the resumed reviewer
follow-up recorded separately from the preserved original archive. No additional
pass was started. PI-6 through PI-8
were integrated before the window began. Keep the workflow stable during each
separately authorized observation window. Assess after five completed passes;
an extension toward ten requires separate authorization and a reason to expect
the selected work to exercise missing paths. Insufficient coverage alone does
not authorize more passes or benchmarks. Report unexercised paths explicitly
rather than treating an absence of findings as proof of effectiveness.

Use existing review archives, friction queues and receipts. In the rationale
of each new triage receipt, use the fixed format
`cause: <value>; recurrence: <value>; evidence: <links>`:

- Cause values: `latent tooling gap`, `integration gap`, `implementer miss`,
  `uncertain`, or `mixed`. Explain uncertainty or contributing causes in the
  remaining rationale.
- Recurrence values: `first observed`, `repeated before fix`, or
  `repeated after fix`. Link the earlier observation when one exists.

`repeated after fix` requires a pass started after the fix was integrated into
that project's checkout, with the fix present at the admitted revision. Link
the local integration commit and pass-start revision. An upstream merge or a
receipt marked fixed is insufficient; re-archiving a pre-fix pass does not make
it a post-fix occurrence. Missing integration provenance is an evidence gap,
not evidence against the fix.

To record a recurrence manually, create a new candidate containing the original
observation text plus an indented continuation line linking the prior candidate
ID, any applicable local integration commit and new pass/review evidence. Keep all of it in one
candidate chunk; a separate top-level link bullet can leave only the link after
receipt filtering. Before triage, run
`python3 scripts/process_friction.py list --project <slug>` and verify that the
original text and context appear together under one new candidate ID. Preserve
the old receipt unchanged.

Compare repeated causes, review rounds and recorded operator rework at the
assessment. A repeat triggers investigation of rule visibility, ambiguity,
conflicts, self-review and tooling; it does not establish which caused the miss.
Correct isolated misses of existing rules through review. Prioritize tooling
for a demonstrated repeat or a single consequential silent failure, using the
existing [triage criteria](agent_playbook/REVIEW_AUDITS.md#process-learning-triage).
Blockers and silent correctness defects can interrupt the observation period.
Use existing evidence for this assessment; no new per-pass benchmark or
all-project performance campaign is required.

<a id="observation-initial-assessment"></a>
### Assessment and follow-up decisions

The work produced substantive semantic closure, including corrected ownership,
data/dispatch boundaries and reference identities. Review also found omissions
after green mechanical gates. This is evidence for retaining independent review,
not proof that every omission needs a new gate. Exact pass IDs, reviewed heads,
round counts, self-reported rework and failure logs remain in the local corpus
evidence companion and original archives.

| Finding or repaired path | Observed result and interpretation | Follow-up |
|---|---|---|
| Historical receipt text treated as live symbol residue | Repeated before any fix for that path; two different valid renames were withdrawn | Prioritize PI-9; preserve original receipts |
| Earlier scorecard wording and rename rationale changed to later vocabulary | A bounded follow-up found recoverable originals in three projects; not every edit was gate-driven | Extend PI-9 to historical fields and policy, then audit and restore proven provenance loss separately |
| Inline dispatch tail left classified as data | A consequential latent gap survived gates; review proved and repaired the source boundary | Bounded detection investigation, with no new hard gate yet |
| Naming-family and reference-coverage misses | Existing rules were missed, sometimes repeatedly; review corrected them | Investigate self-review and rule use; no new checklist or gate justified yet |
| Approval issued during usage-limit grace period | Reviewer resumed, completed the disclosed scratch parity check and confirmed the verdict; the original archive lacked the caveat | Follow-up closed through a linked supplement; assess interruption reporting without inferring review completeness from state alone |
| PI-6 reconciliation | Normal closeout and read-only handoff paths exercised with accepted final packets; no after-fix recurrence established | Refusal paths remain unexercised in this window |
| PI-7 deferrals | Valid capture and saved-corridor fallback exercised; a malformed explicit entry was rejected by preflight | Other refusal/context paths remain unexercised |
| PI-8 portability | All affected-scope decisions were `not-required`; no analyzer/fixture work triggered execution | No claim of production effectiveness from this window |

The receipt blocker is not an after-fix recurrence of PI-6, PI-7 or PI-8:
those repairs address different paths. Count review rounds from canonical
metadata. The resumed follow-up confirms the final verdict without adding a
new formal review round. Recorded rework mixes self-review corrections and rejected
commands; it is not a count of human interventions or measured elapsed cost.
Changes in round counts across different corridors do not establish a causal
productivity gain from the repairs.

Do not activate the monitor or experiment specs, add per-pass measurements, or
implement the rename-coverage candidate on the strength of this assessment.
Use existing logs for the remaining investigations. The closed window and
phase-A integration do not authorize another semantic pass. Exact revisions,
follow-up timestamps, evidence limitations and preservation checks remain in the
private corpus evidence companion.

<a id="second-window-assessment"></a>
### Second five-pass assessment — 2026-10-15

Final work was substantive and connected; first submissions needed consistent
rework. All five passes took two review rounds, with 16 blocking findings.
The scorecard records 52 rework items, which overlap the findings and include
self-corrections. Neither total measures human interventions or elapsed cost.
The five-pass stop was honored; the handoff logs show completed deliveries.
Exact project identities, revisions, archives and captures stay local.

The combined result added 256 semantic rename records (183 high-confidence and
73 scoped overlays), reduced unresolved labels by 41 and raw ROM calls by 27,
and removed 106 hardcoded counter sites. These are supporting measures, not
readability scores. Final relaxed verification preserved binary identity;
process and docs checks passed. One runtime analyzer passed 11 tests, and two
stored captures were reanalyzed against fresh assembler output. No fresh
emulator run or strict maturity completion is claimed.

| Finding | Cause and recurrence | Disposition |
|---|---|---|
| Explicit subjects were stemmed, reordered and truncated | Latent tooling gap; repeated before fix. A synthetic pair differing only in a fourth word silently loses one row | Script fix: preserve explicit identity; keep heuristic keys confined to tagged prose |
| Malformed explicit syntax produced two blank conditions among about 50 open rows; the ratio advisory stayed quiet | Latent tooling gap with malformed operator input: one observed incident, reported in three artifacts, with no recurrence in the remaining passes. A synthetic reproduction separately confirms that one blank row can escape. PI-7 did not cover missing separators/fields | Script/gate fix: reject incomplete explicit batches before closeout writes; validate each open ledger row independently of aggregate ratios |
| No-candidate statements with explanatory prose created queue work | Prompt/harness ambiguity; repeated before fix. Three no-new-candidate statements needed duplicate triage | Prompt fix: require the standalone sentinel; preserve ingestion of genuine observations |
| Sibling names, producers/callers and answerable identities were missed; constants were borrowed across domains by numeric equality | Implementer misses under existing rules; recurrent in this window, without proof that rule visibility caused them | Retain independent review and existing self-review requirements; no additional checklist or speculative semantic gate |
| Unequal visible terminal panes needed operator correction | Session setup mistake: a fixed window size exceeded the attached client's viewport | Restore client-driven sizing and equal layout; no launcher defect established, so no launcher change selected |

Seven new queue candidates describe two underlying deferral defects; their
frequency is not seven independent defects. PI-7's earlier kind/context repair
does not cover these newly reproduced paths. Do not label them regressions of
that repair or claim effectiveness of the new fixes before integration.
The review evidence supports keeping the implementer/reviewer separation;
it does not establish that every missed semantic relationship is automatable.

The implementation branches own the follow-up contracts, validation and
review/integration status in one place each: the
[PI-7 integrity follow-up](#explicit-deferral-integrity) and the
[no-candidate prompt follow-up](#learning-candidate-noop).
This assessment links to those records instead of maintaining parallel copies.

<a id="third-window-assessment"></a>
### Third five-pass assessment — 2026-10-15

The final work closed connected actor identities, motion, rendering and
projectile lifetimes. Review took eight rounds (2, 2, 1, 1, 2), with eight
blocking findings and one minor finding. Recorded rework was 48 items,
including self-corrections and overlapping review findings. The preceding
window took ten rounds, had 16 blocking findings and recorded 52 rework items.
Different corridors prevent attributing those changes to the process fixes.

The ledger added 316 rename records: 238 high-confidence, 66 scoped overlays
and 12 mechanical changes. Unresolved labels fell by 43, raw ROM calls by 20
and hardcoded counter sites by 146. Independent assessment reran 26 rendering
tests, assembled byte-identical PRG output and ran four static renderers
against fresh output. Final review packets supplied successful relaxed
verification, process and docs evidence; no new runtime or gold claim is made.

| Finding or exercised repair | Evidence and disposition |
|---|---|
| Approval interrupted routine checkout inspection | User confirmed a manual approval wait of about 38 minutes. Native policy reproduces a prompt for the branch-read command in the stalled batch. Select the bounded follow-up below; do not attribute every delayed read to a separate prompt. |
| Shared helpers and overwritten values were misinterpreted | Review corrected several names; one approved animation claim needed a later dated correction. Retain independent review and existing caller/consumer obligations, with no new semantic gate. |
| Temporary scripts guessed schemas and interfaces | Repeated ledger and renderer retries contribute to rework. Use existing helpers and inspect schemas; no new generic framework is selected. |
| Repeat count and current gap descriptions drifted | A review counted two occurrences where the ledger and packet showed three. Preserve the review, append a correction, update partial conditions and prioritize the live identity checkpoint locally. |
| Seven fixed queue candidates remained after integration | Receipt and prune resolved entries; preserve original archives and undecided candidates. |
| Explicit-deferral capture and preflight | All 19 new rows retained their exact explicit keys; the pre-PR #159 capture would normalize every one. Two malformed batches exercised PR #142's pre-existing misplaced-kind check before verification, not PR #159's new validation. |
| No-candidate guidance and handoffs | All 16 artifact sections used the standalone sentinel; no new queue entries were created. Deliveries completed, equal panes persisted and the five-pass stop was honored. |

Exact project identities, revisions, logs and cleanup receipts remain in the
local corpus evidence companion. A lower candidate count is a healthy outcome,
not proof that all friction is gone.

<a id="checkout-inspection-permissions"></a>
### Scoped checkout-inspection follow-up

Status: the user's external reviewer approved implementation `bcb297452` on
2026-10-16. The assessment row above now distinguishes live key preservation
from the older misplaced-kind check. Merged in
[PR #162](https://github.com/khansen/nesrev/pull/162), with the profile refreshed
and fresh agents tested. Live checkout inspection succeeded for both roles;
the subsequent single-pass window still needed capture approvals and a reviewer
mode change, as recorded in the [runtime/inspection follow-up](#runtime-inspection-permissions).

The launcher prompts for the whole `git branch` family, so a live branch query
also asks. A narrower allow cannot override a matching prompt: the native
policy uses the most restrictive decision. Preserve the mutation restrictions
and give both roles an approved, argument-free `checkout-status` entry instead.
The generated guide, startup, kickoff and handoff prompts direct routine
inspection through that entry. It reports live root, branch, HEAD and changes
without relying on saved review state or refreshing Git's index. Raw Git
inspection can still prompt; arbitrary Git arguments are not forwarded.

Acceptance: demonstrate native policy approval of the supported command,
correct live results before review initialization and in detached, unborn and
linked worktrees, no index/state writes, and refusal of arbitrary suffixes
before execution. Preserve branch creation/deletion/rename, config, worktree
and push restrictions under inherited broad Git grants. Mutation checks must
catch removal of the grant, guidance or no-optional-locks protection.
Existing staging, commits and handoffs must continue to work.

Validation on 2026-10-15: all 124 agent-review tests passed. The preliminary
Codex reviewer reran 95 of those tests (11 real-Git, 15 permissions/native-policy
and 69 launcher tests) and found no implementation issues. Three
separate synthetic checkouts covered a configured project, a legacy project
without `project.conf`, and an absent project without review state. All passed
live inspection, native policy evaluation, both-role grants and generated
guidance, including quoted paths and invocation from another working directory.
No ROM or project verification is needed for this checkout-level command.

The reviewer ran eight mutations in a disposable copy, restoring the approved
source between probes. Each focused test command exited 1 as intended:

| Mutation | Test command after `python3 -B` | Failure |
|---|---|---|
| Remove implementer grant | `tests/agent_review_permissions_test.py PermissionTests.test_checkout_status_grant_and_guide_cover_both_roles_and_projects` | Supported command absent from grants |
| Remove guide guidance | Same command as above | Supported command absent from guide |
| Remove bootstrap, kickoff or handoff guidance separately | `tests/agent_review_tmux_test.py LauncherTests.test_live_checkout_inspection_is_in_startup_kickoff_and_handoffs` | Supported command absent from the affected prompt |
| Remove `--no-optional-locks` | `tests/agent_review_git_test.py ProjectGitTests.test_checkout_status_reports_live_changes_without_review_state_or_index_refresh` | Index bytes/mtime changed |
| Accept command suffixes | `tests/agent_review_git_test.py ProjectGitTests.test_checkout_status_rejects_suffixes_before_git_is_called` | Expected parser refusal absent |
| Remove branch protection | `tests/agent_review_permissions_test.py PermissionTests.test_native_codex_policy_allows_exact_handoffs_but_not_generic_execution` | Native decision no longer required a prompt (`None != 'prompt'`) |

Refresh the installed profile and restart its agents after integration; a
reconnection preserves old processes and settings. Smoke-test the supported
inspection and handoff paths before the next authorized semantic pass.
No project verification wrapper changes or new recurring measurements are
part of this fix.

<a id="runtime-inspection-permissions"></a>
### Scoped trace execution, source inspection and live smoke follow-up

Status: implemented and tested on `fix/pass-cycle-runtime-inspection`,
branched from master `81d749afd`. The user's usual external reviewer gates
integration; the installed project profile and existing agents remain unchanged.

The fourth observation window contains one approved pass with three review
rounds, four blocking findings and six recorded rework items. It added 45 rename
rows (40 high-confidence, five scoped overlays); generic labels fell by seven,
raw ROM calls by one and counter sites by 25. The final static source audit
covered 640 room records and 47 writer sites. Independent assessment reproduced
PRG parity, all nine focused tests, the byte-identical audit receipt and refusal
of a missing writer row. Exact project identities and captures remain local.

The user confirmed approving emulator commands and switching the reviewer to
auto mode. Logs show nine desktop escalation requests and 1,429.915 seconds
between those requests and emulator start, in aggregate; that interval includes
approval handling and scheduling, not measured human response time alone. The
six accepted captures took about three seconds each. The reviewer used default
mode initially and auto mode later, so this is not a successful unattended run
under the launcher's default profile. Checkout inspection itself worked for
both roles. Two empty-log startup timeouts are distinct from those approval
delays; their cause remains unproven. Only the later timeout entered the friction
queue. The approval interruptions and mode change were missing from that queue.

The selected fix adds `find-project-symbols` for both roles and `trace-project`
for the implementer, with explicit project-bound prefixes in the generated
native profiles. Symbol searches read one validated project file without shell
loops. Trace dispatch accepts only `tools/trace/run_*.py` drivers in the selected
project, forwards arguments without a shell, and preserves exit status. The
profile explicitly trusts changing trace drivers and their dependencies with
desktop access outside the sandbox; it is not a boundary around that code.
Existing Codex rules remain shared by roles. No blanket shell/interpreter grant
or automatic switch to auto/bypass mode is added.

Generated guidance reaches the guide, bootstrap, kickoff and handoffs. Learning
guidance explicitly includes operator approval interventions and mode changes,
while distinguishing requests, confirmed prompts and emulator failures. The
new `--smoke-only` launch runs checkout inspection plus repeated source search
and actual capture commands in fresh scoped agents. It never starts handoff
watchers or releases a semantic pass. Its results need session/log inspection;
successful commands alone do not prove absence of human intervention.

Validation on 2026-10-16: all 94 focused operation, permission and launcher tests
passed (5 + 16 + 73). Full `make test` passed outside the sandbox: 686 shell
cases and 1,206 Java tests. The sandboxed attempt failed only the existing
supervised-emulator cleanup case; the unrestricted rerun passed it. Source
inspection and project-bound grants also passed across all 23 copied projects,
with inspected source files unchanged.

Eight bad-direction probes ran in a disposable copy; each named focused test
exited 1 with a failed assertion:

| Mutation | Test after `python3 -B` |
|---|---|
| Remove implementer trace grant | `tests/agent_review_permissions_test.py PermissionTests.test_project_operations_grants_scope_roles_projects_and_guidance` |
| Remove project from the trace grant prefix | `tests/agent_review_permissions_test.py PermissionTests.test_native_codex_policy_allows_exact_handoffs_but_not_generic_execution` |
| Remove reviewer search grant | `tests/agent_review_permissions_test.py PermissionTests.test_project_operations_grants_scope_roles_projects_and_guidance` |
| Accept symlinked project paths | `tests/agent_review_operations_test.py OperationsTests.test_search_refuses_other_projects_paths_symlinks_and_non_symbols` |
| Hide trace-driver failure | `tests/agent_review_operations_test.py OperationsTests.test_trace_preserves_arguments_runs_from_root_repeats_and_propagates_failure` |
| Remove repeated smoke operation | `tests/agent_review_operations_test.py OperationsTests.test_smoke_spec_validates_real_inputs_and_generates_repeated_standalone_commands` |
| Start a watcher during smoke | `tests/agent_review_tmux_test.py LauncherTests.test_smoke_only_delivers_both_probes_but_never_starts_watchers_or_changes_state` |
| Remove handoff operation guidance | `tests/agent_review_tmux_test.py LauncherTests.test_project_operations_guidance_reaches_both_roles_and_all_handoffs` |

A live disposable-worktree smoke used fresh Codex and Claude sessions with the
generated profile. Codex remained workspace-write/on-request and requested
escalation on both exact capture commands; the profile allowed both without
per-command human approval. Their request-to-capture-start intervals were
0.639 and 0.607 seconds. Both accepted 300-frame captures finished in about
three seconds. Claude stayed in default/manual mode and repeated the same
three-symbol search successfully, with seven matches and no approval prompt.
Both agents also inspected the live checkout. Neither a ready marker nor saved
review state was created, and no semantic pass was started. Setup consent and
readiness confirmation are excluded from the unattended-command claim. The
first launcher attempt failed during tmux pane allocation; an unchanged retry
succeeded before smoke dispatch. This is a setup failure, not a successful probe.

Raw validation logs, mutation diagnostics, native session paths, command timing
pairs and capture acceptance paths are indexed in the local
`/private/tmp/nesrev-runtime-inspection-evidence.json` review attachment.
These are bounded live results, not a guarantee that arbitrary shell commands,
new drivers or different administrator settings will run unattended. Production
installation still waits for external review, integration, profile refresh and
fresh-agent smoke validation in that checkout.

The emulator startup timeout investigation and general reviewer completeness
are outside this bounded permissions change. Copy-and-run validation of published
commands remains required; the last review round was avoidable command drift.

<a id="interrupted-review-candidate"></a>
### Assessment: preserve incomplete review at a usage limit

Status: bounded assessment completed on 2026-10-11 against `3c4e26b34` and
independently approved at `cf229bc9d`. The precision notes below incorporate
the review's optional follow-ups. Assessment merged in
[PR #154](https://github.com/khansen/nesrev/pull/154) and integrated locally.
The generated-prompt clarification is merged in
[PR #155](https://github.com/khansen/nesrev/pull/155), independently approved at
`3e87e449e` after wording and test refinements, and integrated locally.
Existing states, archive format and admission checks are retained. The assessment
estimated 1–3 hours plus independent review and CI for this follow-up. The value is
modest: one observed disclosure gap, with no established recurrence or incorrect
semantic verdict. Provider-specific limit detection and a new completion gate
are not justified by this evidence.

The preserved transcript confirms that the reviewer disclosed its skipped
independent build only in chat after approval. The submitted review itself
omitted the caveat, and the archive retained the submitted content. The reviewer
later completed that build and confirmed approval; a dated supplement preserves
the disclosure and outcome. This is an authoring/handoff gap, not demonstrated
archive data loss. Valid supplied packet evidence can support a completed review;
this incident does not establish a universal requirement for a duplicate build.

Source inspection and synthetic CLI probes establish the current boundaries:

- `import-artifact --kind review` accepts unfinished notes without a verdict
  and leaves state byte-identical. Both `READY_FOR_REVIEW` and
  `READY_FOR_REREVIEW` retain their head, round and reviewer ownership.
  Approval without the required verdict, archival while pending, and replacing
  an unfinished run are refused. Authored checkpoint text survives unchanged;
  no command enforces a pass count. `max_rounds` caps review rounds, not passes.
- A new watch worker delivers the pending turn once; the same worker does not
  repeat it. Saving notes leaves the implementer without a turn while review is
  pending. Existing launcher tests cover pending restart and preservation of
  operator instructions already in the saved prompt. After approval, honoring a
  pass limit depends on those instructions. Archival includes reviews and
  responses, not the implementation note; a fresh launch writes `task.md` from
  that launch's `--task` argument. These paths do not automatically carry a limit
  from every place it may have been recorded.
- A completed synthetic review can explicitly rely on its admitted packet and
  disclose the scratch build it did not rerun. Approval and archival preserve
  that disclosure. A caveat kept only outside the submitted artifact is absent
  from the archive, reproducing the observed information boundary.
- After approval, the next actor is the implementer. A fresh reviewer worker
  does not reopen the review, and artifact import refuses to replace it.
  Follow-up needs an explicit supplementary outcome under the historical-record
  contract; client continuation alone does not provide one.
- Ordinary approval checks the verdict marker, not semantic completeness. A
  deliberately premature `APPROVED` artifact with outstanding work is accepted.
  The pending controls therefore demonstrate a supported safe path, not an
  automated detector of unfinished review. Gold retains its separate checks.

At the assessed revision, the generated reviewer prompt in the
[handoff worker](scripts/agent_review.py) asked for one of two verdicts and gave
their commands, but did not describe the unfinished-review path or ask reviewers
to carry chat-only limitations into the artifact. The
protocol's [review-output contract](AGENT_REVIEW_PROTOCOL_SPEC.md#6-review-unit)
already asks for verification gaps, and its
[reviewer instructions](AGENT_REVIEW_PROTOCOL_SPEC.md#9-agent-instructions)
require findings in the artifact rather than only in chat. The follow-up should
make those instructions concrete at handoff, as implemented below:

- Read any existing checkpoint before resuming. If required work remains, save
  the exact reviewed head, inspected/rerun/supplied evidence, unchecked work and
  next steps in the existing draft and import it without a verdict. Keep review
  pending; neither approval nor requested changes is a pause signal.
- Before issuing a verdict, put evidence relied upon and checks skipped with
  their reasons in the submitted review. A completed review may use valid packet
  evidence without repeating every build. When implementing, reconcile this
  with the [read-only review wording](AGENT_REVIEW_PROTOCOL_SPEC.md#3-scope-and-rejected-ranges)
  about rerunning gates; explain which supplied evidence can be reused and which
  checks the reviewer must run. Do not silently relax an existing requirement.
  A limit warning alone decides neither completion nor rejection.
- Carry the authorized pass limit explicitly into the applicable handoff
  instructions; preserving this text is not mechanical enforcement. Keep
  post-approval discoveries as dated amendments in existing review/evidence
  artifacts under the historical-record contract; preserve the original review
  and archived verdict.

Restart re-delivers the prompt saved at `ready`/`reready`. New generated wording
will reach handoffs prepared after the change; it will not update existing
pending prompts. Implementation controls must cover both new and frozen prompts,
including preservation of saved operator instructions.

Validation: the original ten synthetic control assertions passed across first
review, re-review, completed review, chat-only disclosure and premature approval.
Their pass-limit assertions establish only retention of text explicitly put in
the review drafts by the probe, not enforcement or automatic propagation.
A clarified probe passes twelve assertions, including controls showing that a
limit in the implementation note is not automatically archived and does not
prevent a new run after approval.
On disposable copies, removing verdict admission or dropping archived review
text each made the corresponding control fail.
Existing [artifact-publication tests](tests/agent_review_artifact_test.py) passed
(7), as did three targeted [launcher tests](tests/agent_review_tmux_test.py)
covering pending restart, fresh-worker delivery and preserved operator
instructions. These exercise local CLI behavior with synthetic packet evidence
and a stubbed launcher, not model compliance under a live usage limit. No agent
was launched, no game pass or project verification gate was run, and no
performance or full-corpus claim is made. Any prompt implementation needs
controls for both unfinished and completed reviews; it must preserve unrelated admissions and
existing guidance, raising affected playbook budgets instead of shortening it.

Implementation — 2026-10-12: generated reviewer prompts now separate importing
an unfinished checkpoint from issuing a completed verdict. They name the draft
and imported checkpoint to read on resume and require evidence disclosures in
the submitted artifact. The protocol specifies when exact-head packet gates may
be reused and when checks must be rerun; gold's strict CI remains mandatory.
Both launcher roles read the task for scope and pass limits, handoffs ask agents
to preserve those limits, and approval prompts condition further passes on the
user's authorization. Gold review explicitly permits an unfinished checkpoint;
the final authorized pass stops after archiving and committing its review.
Later discoveries follow the existing dated-amendment contract. No pass counter
or completeness detector was added.

Regression controls exercise the generated import command in both review-ready
states, including gold review without a gold approval marker, refusal of
verdict-less approval and archival, completed-review
disclosures in archives, and frozen-prompt delivery without replacing saved
operator instructions. Prompt assertions cover the gold pause option, the
usage-limit warning's lack of a verdict, and packet admission's lack of proof
of semantic correctness or review completeness. These test CLI and prompt
behavior with synthetic projects, not whether a live model under a usage limit
obeys the guidance.
Existing playbook prose is retained; affected route ceilings grow by the exact
addition so their previous headroom is unchanged.

<a id="dispatch-boundary-candidate"></a>
### Assessment: incomplete inline-dispatch boundaries

Status: bounded investigation completed locally on 2026-10-13 against
`4ef25fe4e`, using xasm 1.9.0; revised after review of `f92d5b3ab` to include
the unused-symbol warning channel. Independently approved at `dff78e29d`,
with optional precision notes incorporated. Merged in
[PR #156](https://github.com/khansen/nesrev/pull/156) as `828dc958e` and integrated
locally; the rebase preserved all project and article contents.
Recommendation: **defer production integration pending a warning-candidate
noise and value assessment**. A candidate prompt is feasible without proving
consumption; a confirmed extent detector needs stronger evidence. The observed
source repair is complete. This assessment introduces no production script,
playbook rule, schema, source repair or project pass.

The originating review found additional handler words after an already-named
prefix. Three existing unused-symbol warnings already pointed at the affected
region: the raw tail label was baselined as a branch/offset table, described as
not executable code, and two omitted handlers were baselined with a claimed
inability to reference them symbolically. The tail's blob disposition still
said queued, with unknown format. Those explanations allowed the warnings to
remain without closing the boundary. Closing the selector's state transitions
and identifying the selected bank established consumption; a parity-preserving
symbolic conversion disproved the claimed symbolization limitation. This is
one confirmed boundary miss, not evidence of independent recurrence.

The synthetic controls use a return-address dispatcher that doubles its
selector and reads an inline word. Fresh listing, xref and validated instruction
records bind the bytes and instruction boundaries. A small fixture-only
interpreter enumerates all 256 input bytes for explicit caller bounds; it does
not infer arbitrary state-machine reachability.

| Control | Result |
|---|---|
| Nine symbolic words, selector 0–8 | All nine entries consumed; complete representation |
| Two symbolic words plus seven raw words, selector 0–8 | Seven omitted entries consumed; bytes identical to the complete table |
| Same raw tail, selector restricted to 0–1 | No omitted entry consumed, although every trailing word points to a real instruction |
| Four entries followed by non-pointer data, selector 0–3 | Complete with four symbolic words; two omitted entries when only the first two are symbolic; both representations assemble identically |
| Target inside an instruction or in data | Existing target resolver rejects it as an instruction start |
| Switched target with known, wrong or unknown bank | Existing resolver returns valid, invalid or unknown respectively; a fixed-bank caller alone does not establish the switched bank |

The NROM mirror control remains valid. An unconstrained RAM selector has no
supplied reachable-state proof and remains an uncertainty. The bank controls
supply context explicitly; they do not model MMC1 writes or infer bank state.

Existing signals and checks have different coverage:

- xasm's unused-symbol warnings directly surface the raw tail and labels of
  unreferenced handlers. The complete nine-word fixture has none; the other
  fixtures retain warnings even when their trailing data is valid. Warning
  presence alone does not classify consumption. On the synthetic truncated
  fixture, `verify.sh` accepts both an unsupported explanation and explicit
  uncertainty when the warning-symbol set matches the baseline; deleting one
  row fails. Its baseline check compares symbol membership. The docs check
  rejects the intake placeholder, but does not prove the replacement prose.
- The raw pointer-table checker reports neither the anonymous symbolic prefix
  nor a generically named raw tail. Giving the tail a pointer-table name makes
  strict mode refuse both the defect and the valid two-entry control. That
  enforces its naming/relocation policy, not consumer extent.
- The missing-extent scan reports zero for these fixtures. Existing index and
  consumer outputs do not join the caller's selector to the helper's
  return-address-derived reads. Instruction records expose the operations but
  do not supply this interprocedural proof.
- The orphan-opcode scanner emits the same two candidates for the defective
  and valid pointer-shaped tails, and none for the mixed-tail pair. These are
  opcode candidates, not evidence of omitted dispatch entries.
- NESrev accepts missing, two-word and nine-word recovery layouts. All three
  outputs reassemble byte-identically. The missing layout misclassifies the
  first table byte as `RTS`, leaving the other 17 as `.DB`; the short layout
  misclassifies seven tail bytes as `ROR`/`ADC`/`JMP`. The complete layout
  preserves all nine words and recovers their handlers. An explicit code-entry
  conflict with an inline record is refused. Recovery validates declared
  layouts and conflicts; it does not prove the count matches the selector domain.

A scratch NROM-only join evaluates a narrower candidate prompt: match an
unused label at an instruction start against adjacent raw `.DB` bytes that
encode its address. It uses emitted warnings, structured definitions, listing
bytes and instruction records; it does not infer a record alignment or a
consumer. Results on the same fixtures are:

| Fixture | Warning-join candidates |
|---|---|
| Complete nine-word table | None |
| Two-word prefix with nine selectable entries | All seven omitted handler labels |
| Four selectable entries, only two symbolic | Both omitted handler labels |
| Four symbolic entries followed by non-pointer data | None, despite unused-handler warnings elsewhere |
| Never-selected pointer-shaped tail | The same seven candidates as the consumed tail; consumption remains unknown |
| First raw target inside an instruction or in data | No candidate for that target; six candidates for the remaining, never-selected handler words |

This join distinguishes the mixed pair without selector proof, unlike the
other scans tested above. A candidate prompt can show the raw-byte location,
matching warned label and existing baseline rationale, then say **consumption
unknown; review the owning consumer and evidence**. It must not claim a missing
entry, extend a table, suppress a warning or invalidate a baseline on this
match alone. Existing warnings already flagged the affected labels; the
potential benefit is connecting them to raw bytes and making their explanations
easier to review, not demonstrating a new class of otherwise invisible defects.

Coverage is limited to labels that exist on decoded or seeded instruction
starts and still warn. Removing a target label or giving it a symbolic
reference removes that target from the join while its raw pair remains.
Unlabeled or already-referenced handlers are missed. Switched-bank matches
need bank context or must remain unknown; this join evaluates NROM only and
refuses to treat banked inputs as checked. The separate target-resolver
controls do not establish a banked join. Real-project noise, coverage and
incremental review value are unmeasured.
The originating case is outside this NROM probe: its archived bank context
suggests a bank-aware join could flag only two of seven omitted targets, with
two already referenced and three unlabeled. That is an archive-based estimate
of partial leads; a banked join remains untested.

To claim a consumed extent, consumer behavior, reachable selectors, byte-read
footprint and target bank still need justification. Those are requirements
for the stronger conclusion, not prerequisites for surfacing candidates.
The fixture interpreter demonstrates that distinction; it is not a proposed
production proof engine.

<a id="dispatch-baseline-explanations"></a>
**Observation: unsupported warning-baseline explanations.** The incident was
partly an explanation-review failure: existing warnings and an unresolved blob
disposition were present, but specific prose obscured the missing proof. This
observation remains open within this assessment; it is not another recurrence.
Close it when a bounded evaluation records the sampled baseline explanations'
evidence status, routes unsupported claims to their owning projects for
correction or explicit uncertainty, and records whether a shared follow-up is
accepted, deferred or discarded with reasons. Closure does not require a new gate.
The existing [baseline bootstrap contract](agent_playbook/NEW_PROJECT.md#warning-baseline-bootstrap)
already permits provisional shape-based reasons that state the consumer is not
yet recovered and name the revisit corridor, and forbids asserting stable
semantics without evidence. Applying that contract to retained explanations
is relevant here; neither a specific rationale nor a green warning-set
comparison establishes its truth. No automatic rationale validator or new
playbook rule is proposed.

The existing [recovery procedure](agent_playbook/DATA_RECOVERY.md#code-pointer-recovery)
provides a manual search, and
[bounded consumer audits](agent_playbook/CONSUMER_AUDITS.md) provide byte and
read-footprint helpers once the owning model is established. The recovery
procedure's address/flow heuristics do not close selector or bank proof, and
an apparent next instruction can itself be a misclassified pointer byte.
The next bounded evaluation, if selected, should compare warning-join prompts
with the warnings and baseline rows already visible in representative projects:
count useful connections, duplicates, ambiguous tails and missed labels before
deciding whether integration earns its review cost. Also classify matched
baseline explanations as evidence-backed, explicitly uncertain or unsupported,
and count claims of meaning without proof. Report address matches whose bank
is unknown as unresolved-bank candidates, listing possible target banks when
available; count them separately from resolved matches and keep consumption
unknown in both groups. That evaluation does not require a general selector
proof engine. A confirmed-extent detector remains a separate, stronger
proposal. No noise rate or production benefit has yet been demonstrated for
either approach, and these controls do not justify a new gate.

Validation covers nine entry/tail fixtures, separate unknown-selector and
bank controls, four recovery configurations, the warning join with two added
label/reference controls, and three synthetic warning-baseline runs through
`verify.sh`. The docs-baseline limitation was inspected in source, not tested
through a full docs wrapper. Deliberately removing the consumer's doubling or
reducing the caller's bound is caught by the original fixture checks. The local
evidence retains exact commands, diagnostics, artifacts and traces for review.
Full project gates, corpus-wide discovery, emulator execution and performance
measurements were not run. These synthetic results do not establish production
coverage, real-project noise or runtime reachability in an arbitrary project.

<a id="rename-coverage-candidate"></a>
### Candidate: inventory coverage across semantic renames

Status: observation candidate, not approved implementation. The reproduced
selector-name regression showed that a byte-preserving rename can make an
inventory silently omit entries. Consider a general comparison only after
observing which other consumers exhibit the same failure.

The proposed comparison would flag unexplained losses of represented pointer
targets, split pairs or table bodies across a rename-only edit. Binary parity
is necessary but does not establish that an edit is rename-only: symbolization,
directive changes and corrected classifications can also preserve every byte.
Review the source change and use fresh evidence from the same producer, reader
and options for both revisions.

Compare represented bodies and entries by stable locations and rename mappings,
not just row counts or symbol spellings. Counts can stay constant while one body
disappears and another appears; aliases can legitimately change row counts.
Advisory findings are a separate case: fixing a raw pointer body can correctly
remove its finding while preserving the binary. A disappearing finding needs
an explanation, not an automatic coverage-failure verdict.

Before proposing a gate, demonstrate another affected consumer or a remaining
consequential omission, and distinguish those losses from legitimate changes.
Prefer reusing existing validated artifacts; the cost of a general comparison
is unmeasured. A future implementation spec must settle identity matching,
eligibility, evidence freshness, exceptions, diagnostics and cost. This candidate
adds no wrapper invocation or gate during the observation period.

<a id="friction-triage-followups"></a>
## Follow-ups from queue triage — 2026-10-07

The corpus queue review routes reports here without implementing a fix or
changing the order above. Receipt decisions preserve the original observations;
repeated review rounds are not independent demonstrations of a defect. The
local evidence companion records fixtures, current-code inspections, limitations
and project-specific examples. These items need bounded implementation proposals,
not new universal gates inferred from old review suggestions.

<a id="triage-input-guards"></a>
### Validate input domains and documentation references

**Raw-RAM validation — complete.** Merged in
[PR #151](https://github.com/khansen/nesrev/pull/151) as `87ecb6cff` and integrated
on the local corpus branch. Updates validate supplied addresses and existing
rows before ledger mutation, preserving distinct mirror addresses, supported
overlays and inactive history. The supported domain and refresh boundaries live
in the [raw-RAM queue contract](agent_playbook/PASS_WORKFLOW.md#raw-ram-queue).

**Documentation reference classification — deferred (2026-10-11).** The token
classifier can treat external identifiers such as `TRACE_OUT` as asm references.
The benefit of a fix is modest: fewer false docs-check failures and fewer
formatting workarounds. A false positive is reproduced, but frequent disruption
to passes has not been established. Adjacency to raw-RAM validation does not
justify making this the next implementation priority.

Estimated effort is **2–4 hours, plus review and CI**, assuming one narrow,
explicit convention for external identifiers. This includes implementation,
regression tests, corpus docs checks and documentation. The classifier is small;
most effort is in proving that an exception cannot hide genuine broken
references. Plain text or a complete command example is the cheaper workaround.

Revisit if false positives repeatedly interrupt passes or those workarounds
materially impair the docs. Any implementation must retain rejection of genuine
unknown asm symbols and current-scorecard mistakes. Do not exempt arbitrary
backticked text or scan historical reviews as live docs.

<a id="triage-closeout-prose"></a>
### Make closeout's authored-input behavior explicit

The existing-row admission path ignores supplied focus and notes while the
new-row path uses them. Decide whether conflicting explicit inputs should refuse
or produce a clear warning and editing instruction. Preserve historical rows
and the existing separation between authored cells and generated KPI refresh.
Cover explicit rechecks, new rows, malformed notes and deferral capture; a
blanket overwrite of prior pass history is not an acceptable fix.

<a id="triage-runtime-session"></a>
### Isolate and reproduce emulator session state

Evaluate a capture profile that isolates persistent cheats and saved session
state while permitting explicitly requested Game Genie scenarios. Preserve the
current bounded runner, fresh completion evidence, exit-status handling and
process-group cleanup. First reproduce configuration/cheat persistence and
startup movie behavior in disposable profiles; do not experiment on the user's
emulator configuration. Specify how Lua wrappers report initialization failure
and resolve task-specific paths before adding automatic recovery. Audio recording
and cross-capture savestates require platform/version evidence; a report about
one launch method does not establish that the emulator lacks a capability.

<a id="triage-diagnostics"></a>
### Improve diagnostic summaries without changing admission policy

Assess a terminal maturity-failure roll-up that preserves each original error
and exit status. A final summary helps tail readers but cannot make arbitrary
head truncation safe. Separately reproduce the tiny-candidate warning with a
broadened objective. Missing objective/reference fields currently warn by design;
any proposal to refuse them must explicitly decide compatibility and the
admission contract rather than treating the warning as a regression.

<a id="triage-owner-attribution"></a>
### Recheck alias and consumer ownership reports

Use fresh listing/xref/data-consumer artifacts to reproduce same-address extent
alias selection, split-pointer consumer ownership, and address-domain naming
collisions. Include legitimate shared scratch, CPU/PPU equal-valued constants,
hardware vector fetches and indirect consumers as controls. Existing direct and
pointer-table `Used by` checks already cover part of the historical reports.
Do not turn an unsupported or indirect attribution into a hard mismatch or
extend assembly-source parsing to recover assembler facts.

<a id="triage-reference-maintenance"></a>
### Make current project debt discoverable

Evaluate one owning-project destination for analogue corrections, indexed from
the architecture comparison. Distinguish shared machinery from shared names,
and retire the current debt entry when its evidence condition is closed.
Reconcile dated corpus dashboards from canonical inventories before considering
automation; a semantic debt cannot be declared closed just because its old
symbol disappeared. Recheck dedicated-format/overview links and trace-command
discoverability as documentation maintenance, without requiring a new gate for
every prose assertion.

For cross-project quantitative comparisons, evaluate recording both inputs'
hashes, units and enumerated ranges alongside the claim, so unavailable private
inputs remain explicit limits rather than silently assumed verification. Recheck
shared-name claims after either project's vocabulary changes. A source symbol's
existence or hash does not prove a measured cross-project claim.

<a id="triage-review-accounting"></a>
### Clarify review accounting and localization wording

Keep rename-range diagnostics advisory while distinguishing newly claimed
renames, edits to historical ledger rows, and sanctioned generator-label
deletions. Existing observations demonstrate false positives in the proposed
hard gate. Also resolve the localization guidance's unqualified `JSR`/`JMP`
exception versus its outside-scope exception with assembled positive and
negative examples. Rework counts remain authored judgments; a mandatory prose
clause needs a demonstrated reporting benefit, not an assumption that a regex
can verify the count.

<a id="triage-claim-propagation"></a>
### Carry corrected claims through current artifacts

Status: merged in [PR #153](https://github.com/khansen/nesrev/pull/153) and
integrated locally after independent approval at `89efdb5d7`. The canonical
[current-artifact rule](agent_playbook/DOCUMENTATION.md#corrected-claim-propagation)
covers corrected claims, format boundaries, reachability decisions and
vocabulary families, including indirect restatements and linked overviews.
QUALITY_REVIEW links the sweep and clarifies that corrections to existing
semantic claims apply before gold closeout; PASS_WORKFLOW reserves the maturity
restriction for adding claims. Historical records remain protected under PI-9;
temporary session stop instructions belong in handoff/pass state, with a pointer
from the deferral contract.
Existing guidance is retained and affected route budgets preserve their prior
headroom. No runtime checker, new document requirement or project pass was added.
The subsequent local rebase preserved all article and project contents.
Effectiveness remains unmeasured until later authorized passes exercise the rule.

<a id="triage-evidence-methods"></a>
### Clarify the limits of modeled and captured evidence

Prepare focused wording for RUNTIME_EVIDENCE and bounded consumer-audit review:
controls must distinguish the competing explanations, and zero-hit results need
evidence that the triggering scenario occurred. Record intervention points and
whether out-of-bounds bytes came from current writes, stale state or emulator
initialization; any fill-pattern claim needs version/configuration evidence.
Before classifying a small deterministic state space as runtime-only, assess
whether complete enumeration is practical, bind its model to the relevant entry
paths and retain its output and limits. An agreeing model is not emulator
evidence; a disagreement requires checking the model as well as the document.
Do not require enumeration or additional captures for every question.

<a id="triage-boundary-review"></a>
### Clarify family closure and boundary evidence

Propose wording that keeps a containing family open while its unresolved source
or boundary evidence remains unaudited, even if a useful subset is documented.
For multi-stage queue producers, review publication/rollback at the caller's
stored commit boundaries as well as the byte helper. Define an advisory view
of outstanding negative-offset findings before runtime deferral, zero/disabled
descriptor aliases in blob matches, and consistent positive-offset consumers.
Use current structured artifacts and include legitimate prefixes, shared tails,
biased selectors and disabled entries as controls. Establish supported cases
before implementation; no automatic reachability proof, universal audio model,
source parser or new admission gate is accepted by this item.

<a id="triage-constant-evidence"></a>
### Investigate constant meaning with bounded evidence

Repeated reports justify evaluating an advisory for value-coincidence mistakes:
show the store sites and basic-block value provenance for selector/request bytes,
and compare equal-valued constants with their consumers. Include legitimate
overlays, unrelated equal constants, composite masks and cross-subsystem reuse
as controls. Name prefixes and equal values are candidate signals, never proof
that names conflict. Separately assess compare-to-ADC/SBC carry dependencies:
distinguish the encoded operand from the effective quantity, and cover incoming
branches, flag-changing instructions and intentional carry use. Consume structured
assembler facts; measure noise before deciding whether either advisory is useful.

<a id="triage-review-facts"></a>
### Evaluate a structured view of policy-review evidence

The requested definition/body/reference/owning-scope view is not supplied by the
active-policy membership checker. Evaluate one bounded read-only view from
current structured artifacts, including fall-through predecessors and same-address
aliases. Preserve mechanical counts separately from authored semantic claims;
the view cannot prove branch polarity or the truth of evidence prose. Clarify
whether fall-through belongs in the global-label contract, and specify which
body/reference/localization facts can be reproduced. Row order has no independent
semantic value and should not become an admission gate.

<a id="triage-shared-staging"></a>
### Document staging for shared project indexes

Document the sanctioned explicit Git staging/commit route for shared
`projects/*.md` files that `agent_review.py stage-project` deliberately refuses.
Keep project staging scoped, include the shared change in the reviewed commit
range, and preserve unrelated work. Do not widen stage-project to stage an
arbitrary shared directory automatically.

<a id="triage-portable-examples"></a>
### Evaluate a personal-path advisory

Assess a lexical advisory for personal absolute paths in active tracked command
examples, with controls for repository-relative commands, deliberate external
input paths and historical evidence. No blanket no-personal-path rule currently
exists; decide the documentation convention and supported scope before adding
a check. The report supports a small portability investigation, not a semantic
detector or a repository-wide refusal.

## Delivery and tracking

Implement shared changes on feature branches from current `master`, using
separate worktrees. Shared changes, commit messages, and PR descriptions must
not name actual games or include corpus-specific symbols, paths, or review
references. Use synthetic fixtures and generic examples instead. Keep
game-specific evidence, migrations, and eventual queue pruning on the
local-only corpus branch; never push that branch or private ROM fixtures.
Each implementation branch updates this plan with its status and
reviewed commit or PR reference. Before activating a gate on the corpus,
prepare supported local migrations and test them together with the tooling.
For PI-2 runtime activation, the user explicitly accepts newly exposed missing
evidence as failing CI debt. This changes the landing prerequisite, not the
checker: unsupported inputs must fail, never skip or pass by exemption.
Record the before/after failure set and independently review the supported
migration and each newly exposed failure before landing.

| Branch | Scope | Status |
|---|---|---|
| `docs/five-pass-process-assessment` | Second five-pass assessment and bounded follow-up contracts | Merged [PR #161](https://github.com/khansen/nesrev/pull/161) |
| `fix/explicit-deferral-integrity` | Preserve explicit subjects and require complete deferrals before closeout writes | [Canonical delivery record](#explicit-deferral-integrity) |
| `fix/learning-candidate-noop` | Require a standalone no-candidate sentinel in generated prompts | [Canonical delivery record](#learning-candidate-noop) |
| `fix/pass-cycle-readonly-inspection` | Scoped live checkout inspection and third-window assessment | [Canonical delivery record](#checkout-inspection-permissions) |
| `fix/pass-cycle-runtime-inspection` | Scoped trace execution, source inspection and live smoke | [Canonical delivery record](#runtime-inspection-permissions) |
| `fix/pi-1-checker-coverage` | Consumer parsing and PPU stream coverage | Merged [PR #98](https://github.com/khansen/nesrev/pull/98); reviewed `70e488a7f` |
| `feat/pi-2-policy-evidence` | Manifest membership and disposition checks | Merged [PR #100](https://github.com/khansen/nesrev/pull/100); reviewed `447b72477` with local activation migration |
| `feat/pi-2-runtime-evidence` | Runtime deferrals and executable evidence | Merged [PR #105](https://github.com/khansen/nesrev/pull/105); independently approved `c405c932a` with the supported local migration and explicit failing debt |
| `feat/pi-3-consumer-audits` | Reusable audit machinery | Merged [PR #102](https://github.com/khansen/nesrev/pull/102); reviewed `90fda2af3` with the local adapter migration |
| `feat/pi-4-review-bundles` | Complete evidence and gate reporting | Merged [PR #103](https://github.com/khansen/nesrev/pull/103); reviewed `eff6b00ab` |
| `fix/pi-5-intake-baselines` | Historical measurement protection | Merged [PR #104](https://github.com/khansen/nesrev/pull/104); reviewed `b9aab397d` with the receipt-only local migration |
| `feat/process-queue-lifecycle` | Receipt migration and pruning-safe ingestion | Merged [PR #101](https://github.com/khansen/nesrev/pull/101); reviewed `8bafbf7f4`; local pruning active |
| `fix/pi-6-review-handoff-freshness` | Read-only closeout reconciliation at handoff | Merged [PR #141](https://github.com/khansen/nesrev/pull/141); reviewed `72cad08f6` and `e15e9fe5e`; preparation timing exception approved |
| `fix/pi-7-deferral-capture` | Deferral condition validation and saved corridor context | Merged [PR #142](https://github.com/khansen/nesrev/pull/142); approved `252487518` with early-validation follow-up `760235ad2` |
| `fix/pi-8-analyzer-portability` | Executable clean-export runtime fixture evidence at handoff | Merged [PR #143](https://github.com/khansen/nesrev/pull/143); approved `a1a586b10` |
| `fix/raw-ram-input-validation` | Address-domain and ledger validation before raw-RAM updates | Merged [PR #151](https://github.com/khansen/nesrev/pull/151); squashed `87ecb6cff` has the approved `b54e601a8` tree; integrated locally |
| `docs/corrected-claim-propagation` | Propagate corrected claims through current artifacts while preserving history | Merged [PR #153](https://github.com/khansen/nesrev/pull/153); independently approved `89efdb5d7`; integrated locally |
| `docs/interrupted-review-assessment` | Assess interruption, evidence disclosure and existing pending-state behavior | Merged [PR #154](https://github.com/khansen/nesrev/pull/154); independently approved `cf229bc9d` with optional precision notes incorporated; integrated locally |
| `feat/interrupted-review-checkpoints` | Clarify unfinished checkpoints, evidence disclosure and authored pass limits in review prompts | Merged [PR #155](https://github.com/khansen/nesrev/pull/155); independently approved `3e87e449e`; integrated locally; state transitions and gates unchanged |
| `docs/dispatch-boundary-assessment` | Assess inline-dispatch boundaries, unused warnings and baseline explanations | Merged [PR #156](https://github.com/khansen/nesrev/pull/156); independently approved `dff78e29d` with optional precision refinements; integrated locally; production noise and added value unmeasured |
| `fix/embedded-pointer-advisory` | Make legacy embedded-pointer matches explicitly unproven and report-only | Merged [PR #157](https://github.com/khansen/nesrev/pull/157); independently approved `c05d92f57`; integrated locally; evidence failures and independent pointer gates retained |

Use ordinary process/tooling branch review, including bad-direction tests
and representative corpus checks. Do not use the project-pass handoff state
machine for these branches. Remote publication and corpus rebases are separate
landing actions, not implicit consequences of creating a local commit.
For the previously authorized delivery items, obtain review approval before each
PR, merge only after verification, then fetch and rebase the local corpus onto
updated `master`. Rerun affected CI after each merge; report pre-existing
unfinished-input failures separately and never relabel relaxed checks as
strict-CI success. Prune eligible queue entries incrementally once receipts
and their migration tests are in place.
Unselected observation follow-ups remain planning items. The second-window
fixes were separately selected by the operator; updating this plan alone does
not authorize publication, integration or another project pass.

<a id="pi-9-historical-receipt-residue"></a>
<a id="pi-9-historical-provenance"></a>
## PI-9 — Preserve historical provenance during symbol renames

Status: phase A merged in [PR #147](https://github.com/khansen/nesrev/pull/147)
as `32747f299`, including the independent-review fixes and mandatory CI locale
coverage. Phase A was integrated at a completed pass boundary without changing
project files. Phase B's restorations, rename-link amendments and separately
reviewed archive recovery are now integrated on the local-only corpus branch.
The committed evidence records the reviewed scope and unresolved gaps. This
section specifies both phases; no separate spec is required. These repairs
neither started nor authorize an additional semantic pass.

Before phase A, closeout's [residue sweep](scripts/project_pass_residue_check.sh) treated old
symbols in canonical friction receipts and earlier scorecard rows as current
references. The [preflight rule](agent_playbook/PASS_WORKFLOW.md#completion-checklist)
explicitly told agents to paraphrase historical mentions to satisfy that sweep.
The [docs symbol check](scripts/check_docs.sh) and
[reference rules](agent_playbook/DOCUMENTATION.md#reference-document-use) also
required scorecard symbols to resolve against current assembly. Phase A addressed
these pressures together so that excluding receipts alone would not leave
other checks forcing the loss of attribution.

A bounded follow-up found original wording still recoverable from Git in three
projects: earlier scorecard symbol citations were paraphrased, and earlier
rename reasons were rewritten using later knowledge. The latter was not forced
by the checker. These examples establish feasibility, not corpus-wide damage
counts. Some historical edits are valid corrections; others were already
repaired during review. The private evidence companion records the exact cases.

<a id="pi-9-history-contract"></a>
### Phase A — Historical and current-reference contract

Historical names describe the revision in which they were recorded; they do not
claim that a current symbol still exists. Use this explicit boundary:

| Artifact or field | Treatment |
|---|---|
| Canonical friction receipts and archived reviews | Historical evidence. Preserve existing content, IDs, source references and dispositions; keep archive exclusions explicit. A rename must not rewrite them. |
| Earlier completed scorecard rows | Historical pass outcomes, including topic, notes, symbol spellings, measurements and recorded results. Exclude their symbol references from current-name checks, retaining structural and lifecycle validation. |
| Current scorecard row and prose outside historical rows | Current authored content. Continue checking current symbol references; exempting the whole scorecard is incorrect. |
| Earlier-pass `renames.csv` entries | Preserve all five fields, including original rationale, confidence and pass attribution. A later rename appends a new old-to-new link; later understanding must not be backdated into an earlier reason. Keep existing ledger schema checks. |
| Current assembly, systems/format docs, memory map, crosswalk, working notes and active inventory fields | Current state. Continue checking and updating live references and factual owners under their existing contracts. An old pass number or date alone does not make an active decision or owner historical. |

For scorecards, closeout forwards its resolved pass ID to docs-check; standalone
docs-check uses the latest pass ID in the validated scorecard. Only completed
rows with a lower ID are historical for these checks. The selected/latest row remains current
even after its result cells are filled. An explicit recheck of an older pass
does not exempt later rows. Reuse the scorecard parsers and lifecycle rules:
missing or ambiguous context, malformed cells, duplicate/out-of-order IDs and
unfinished earlier rows must not acquire an exemption through a loose text
match. Source line numbers must survive filtering for useful diagnostics.
Identical repeated headers continue the same pass log. Legacy nonnumeric
annotations remain ordinary checked text and receive no historical exemption.
Because lifecycle validation shares this parser, process-check also refuses a
second `pass_id` table with a conflicting header. This is an intentional
validation tightening beyond the two symbol checks, not a historical exemption.

Apply the same boundary in closeout's residue sweep and docs-check's backticked
symbol validation. Recognize receipts by their canonical project path and the
existing receipt reader/validator; malformed schema, wrong project identity or
invalid candidate-content hashes produce a clear evidence error. A missing
receipt ledger remains supported. Do not exempt all JSON, all inventories,
arbitrary caller-selected files, or every file named like a receipt. Existing
raw-operand closure, current owner reconciliation and current-pass ledger
validation remain in force. No assembler-fact parser or new xasm output is
needed for this authored-text boundary.
Receipt IDs hash normalized candidate content only; rationale, sources and
destinations are schema-validated but not covered by that content hash.
Preservation of those fields, earlier rename reasons and review archives is
policy, with byte-identity regression tests, not a tamper-detection guarantee.

Land the corresponding playbook changes with the tooling: replace the
historical-paraphrasing instruction in PASS_WORKFLOW and align DOCUMENTATION's
reference-stability and rename-ledger rules. Explain the distinction above and
retain current-state cleanup. Neither deleting old names nor stripping their
backticks is a historical repair. This is a policy correction as well as a
checker fix; agents following the old instruction were not necessarily
disregarding the playbook.

Acceptance for phase A:

1. A synthetic rename with its old spelling only in a valid receipt or an
   earlier completed scorecard row completes canonical closeout and docs-check.
   Cover bare and backticked historical names. Earlier rows, rename records,
   receipts and archives remain byte-identical, including repeated closeout.
2. Put the same old spelling in the current scorecard row, scorecard prose
   outside the historical rows, a current document and an active inventory
   owner. Each fails the applicable existing check. An ordinary JSON file with
   stale active text remains covered. Later rows in an older-pass recheck are
   not silently treated as historical.
3. Missing receipts work; malformed receipts refuse with their diagnostic.
   Invalid scorecard structure/lifecycle refuses rather than hiding references.
   Test standalone docs-check's latest-pass selection as well as closeout.
   Both symbol lists and their comparison must use consistent collation;
   exercise valid and missing symbols under a UTF-8 locale that sorts them
   differently from C. A residue check with no renames does not decode unrelated
   docs; unreadable documents needed for a rename scan refuse clearly with 65.
4. A two-pass rename chain keeps the first row's five fields unchanged and
   appends the second rename. Later discoveries remain attributed to the later
   pass. Current raw-RAM owner reconciliation still updates active fields.
5. In scratch mutations, restoring either check's old historical input selection
   breaks its positive case; blanket scorecard/inventory exclusions break the
   current-reference negative cases. Exercise canonical wrappers, not only a
   helper. Recheck the two withdrawn renames in isolated project copies and
   sample projects with and without receipts, preserving parity.

This changes existing checks, with no new assembly invocation or per-pass
command. Do not add all-project performance testing. If measurement is needed,
use one representative affected path under the existing performance policy.

Initial validation at `f177e68e6`: 13 focused Python tests, all 676 shell cases
and 1,206 Java tests passed. Nine scratch mutations failed on their intended assertions,
including restored historical scans, blanket exemptions, skipped receipt
validation, missing pass-context forwarding and changed failure order. The full suite required an
unrestricted rerun for its existing process-cleanup tests' `ps` access.
Read-only validation accepts 3,744 historical rows and the receipt ledgers across
23 projects; this is not a full corpus verification or a completed history audit.
The two withdrawn renames pass residue/docs checks and canonical parity
verification in an isolated copy, with unchanged receipt bytes. The old residue
checker rejects the same replay. Exact pins, logs and timing remain in the
private evidence companion.
Three alternating measured pairs after warmup on one large project keep both
affected wrappers within budget: standalone docs-check +3.50%, complete closeout
recheck -0.56%. An initial +6.86% docs-check result led to reusing an existing
Python scan, with refusal order preserved and tested. No all-project timing
campaign was run.

External review found inconsistent sort/comparison collation that the initial
fixtures missed. Both symbol lists and their comparison now use C collation.
The follow-up passes 31 affected shell cases (including the 13 Python contracts)
under `en_NZ.UTF-8`, and docs-check passes on all 23 pinned projects under that
locale. The new collation fixture selects an installed UTF-8 locale with a
demonstrably different order; this run exercised `ca_AD.UTF-8`, with both valid
and genuinely missing symbols. Local hosts without such a locale explicitly skip
that fixture. CI generates `en_US.UTF-8` on Linux and requires a differing
collation on both platforms, failing rather than skipping if one is unavailable;
the toolchain log also records the environment's locale. Three scratch mutations reject the sort mismatch, eager no-rename
document reads, and unhandled decode errors. The supported `make -C` invocation
from outside the repository also passes; direct helper invocation outside the
repository root is not newly supported. Full shell/Java suites and timing were
not rerun for this follow-up. The old timing receipts did not record locale
and do not establish performance across locales.

The final landing head `e25193bd1` subsequently passed all 678 shell cases and
1,206 Java tests locally and in Linux/macOS CI before PR #147 merged. The local
integration preserves every project file; no performance measurement was repeated.

<a id="pi-9-provenance-restoration"></a>
### Phase B — Audit and restore existing project provenance

Status: complete within the independently reviewed audit scope and integrated
on the local-only corpus branch. The evidence companion links the committed
restoration and rename-link packets, unresolved gaps and separate archive
recovery. Previously working rename trails are preserved after restoration;
unavailable earlier source history is not reconstructed by inference. The
following contract also governs any later repair batch.

Keep shared tooling/playbooks and corpus repairs in separate reviewable commits.
The audit may run read-only before phase A lands; restoration must wait until
the reviewed contract is integrated into each affected checkout at a pass
boundary. Reconcile against then-current HEAD instead of applying stale patches
or rewriting an active pass's files.

1. Pin the corpus revision and inspect historical record changes across the
   existing projects. Use Git versions and preserved review artifacts, keyed by
   project, artifact and pass/record identity. Classify each proposed repair as
   lost attribution, legitimate correction, already repaired, or unresolved.
   Distinguish gate-driven changes from independent editorial changes. Record
   the projects and history ranges inspected; do not equate no match with proof
   of intact history when earlier revisions are unavailable.
2. For each confirmed loss, record the source revision/path and exact original
   text, the later edit, and the proposed restoration in the existing private
   evidence companion. Restore only the affected historical fields. Preserve
   unrelated later rows and current source, names, ownership and inventories.
   Never synthesize a missing name, reason, confidence, pass ID or rename chain.
   If Git and saved artifacts cannot establish the original, record the gap.
   Restoring an earlier target must also preserve its documented trail to later
   names. Append missing old-to-new linkage amendments without rewriting the
   restored rows, citing the revision that establishes each correspondence.
   Distinguish an observed source rename from a later ledger correction whose
   source-rename timing is unavailable; the latter must say so in its reason.
   Reuse recorded confidence rather than claiming new semantic proof. Attribute
   a pass-associated change to its recorded pass. For an off-pass sweep, use
   the first subsequent recorded project pass as an explicit filing convention,
   citing both revisions; this does not claim the rename happened in that pass.
   If no such pass or supported correspondence exists, retain an explicit gap.
   Preserve existing links, account for scoped names and expression components,
   and check that restoration loses no previously working trail. Do not create
   fictional intermediate names from a mechanical rewrite of historical text.
   Project history may already have been squashed and may be squashed again.
   Commit the exact before/after records and the source excerpts, definition
   facts and pass-attribution evidence needed to review each repair. Retain
   revision IDs as provenance references, not as the only surviving evidence;
   temporary packets and local preservation refs are insufficient. Mark missing
   pre-squash source evidence explicitly rather than reconstructing it by guess.
3. Keep genuine later discoveries and factual corrections as dated amendments
   in existing review/evidence artifacts, identifying the original pass/record
   and supporting revision. Do not reinstate a disproved claim without its
   correction, erase a review verdict, invent a semantic pass, or add a rename
   row for a rename that never happened. Existing receipt/archived content stays
   unchanged; suspected damage to either requires a separately reviewed recovery
   using the original identity/content evidence.
4. Verify restored fields against the cited originals, preserve record order and
   unrelated content, and review each before/after diff. Rerun affected docs and
   process checks after the final edit; report existing failures distinctly.
   Run canonical project verification for any accompanying semantic/source edit,
   keeping deferred rename work separate from the historical restoration. Record
   repaired, already-correct and unresolved cases. A repeat audit of repaired
   records should propose no further restoration.
5. Commit restorations normally, with source revisions and any amendments linked
   from the evidence companion. Do not rewrite Git history. Only after landing
   and local integration should the existing friction workflow reconcile the
   observations; no receipt pruning is implicit in the repair.

Phase B's acceptance is an attributable, reviewed repair for every confirmed
case in the declared audit scope, with unresolved evidence gaps explicit. It
does not promise to recover uncommitted text that was never preserved. The
read-only history audit needs no ROM builds or performance campaign; validation
is limited to the checks affected by each resulting change. Phase A changed
the checks; the separately reviewed phase-B repairs are now integrated.

<a id="pi-6-review-handoff-freshness"></a>
## PI-6 — Check closeout reconciliation at review handoff

Status: review accepted `72cad08f6` and normalization fix `e15e9fe5e`;
the preparation timing exception was approved on 2026-10-03.
A committed stale
raw-RAM count reproduced an accepted packet with green verification, process and
documentation gates. Synthetic coverage also reproduces stale owners after a
rename. The packet now checks the seven derived raw-RAM fields and missing
candidate rows with fresh assembly evidence, using closeout's existing refresh
calculation. The comparison also requires byte-identical CSV serialization using
the writer shared with closeout, including its blank-status default. Check and
refresh both preserve an absent ledger when there are no candidates; refresh
retains existing empty ledgers and creates a queue when candidates appear. The precise
scope, retained historical-row behavior, and refusal
contract are in [the packet specification](PROJECT_PASS_REVIEW_PACKET_SPEC.md#cache-preparation).

- Reproduce stale closeout output against current wrappers using a synthetic
  pass whose final edits change ledger ownership. Identify which closeout
  outputs need checking and document that boundary in the packet contract.
- Add the smallest read-only validation that detects outstanding reconciliation
  against the exact reviewed inputs and tooling. A timestamp or recorded
  invocation alone must not certify freshness. Packet creation must preserve
  tracked ledgers, authored decisions, scorecards and pass history.
- Report stale, failed and unrun validation explicitly, and make handoff refuse
  each state. Keep packet generation, handoff validation and their spec aligned;
  diagnostics must identify the stale output and the required operator action.

Done when: a stale-owner fixture with otherwise green gates is refused for the
intended reason; a reconciled head succeeds; relevant edits after reconciliation
make it stale again; cold-cache and repeated checks leave tracked files unchanged.
Confirm the refusal through the handoff path as well as packet generation.

Validation on xasm 1.8.1 before the final absent-ledger guard: 661 shell tests
and 1,206 Java tests pass. Fresh
comparisons and byte-identical writer output pass on all 23 local project ledgers.
The real stale-count packet passes the old gates and parser, then fails the new
handoff; reconciled, cold-cache and repeated packets succeed without tracked
writes. The original review covered five deliberate regressions; two additional
mutations catch a field-only verdict and a diverging CSV writer. CLI handoff and
packet reuse refuse disabled, failed and unrun reconciliation. The check skips
unneeded briefing work and remains independent of corrupt briefing caches.
The absent-ledger follow-up passes three focused wrapper cases, seven CSV unit
tests and 34 packet-parser tests. Removing the guard fails its regression for
creating an empty ledger; existing empty ledgers and new candidates are positive
controls. The approved timing and 23-project comparison were not repeated for
this guard, which does not alter their populated-ledger path.

Final timing uses three alternating pairs after warmup on the largest source
project. Median wall changes are +5.20% for read-only preparation with
reconciliation, +0.13% for cached next-pass, and +2.15% for the complete packet.
Approved: +5.20% median on read-only packet preparation, largest project,
11.54 → 12.14 s. Cause: the reconciliation runs the closeout raw-RAM refresh
the packet previously skipped. Default pass-prep is unchanged; the full packet
is +2.15%. This path now has no headroom left: the next addition must offset
its cost. This is a bounded exception under
[the performance plan](PROJECT_CI_PERFORMANCE_PLAN.md#non-regression-requirement),
not a change to the general 5% limit.
The earlier +4.82% preparation measurement described the reviewed revision,
not this final result. Original assembly counts were two, zero and five
respectively in that warm-cache setup; the follow-up adds no assembly calls.
Packet runs use the explicit unresolved-label allowance; these are semantic-pass
verification results, not strict maturity evidence.

<a id="pi-7-deferral-capture"></a>
## PI-7 — Preserve meaningful deferral conditions and corridor context

Status: merged in [PR #142](https://github.com/khansen/nesrev/pull/142) after
approval of `252487518`, with early input validation added from review.
Baseline wrapper regressions reproduce a bare `static` or `runtime` accepted as
the revisit condition, a saved
corridor omitted from new deferrals, and missing context left undiagnosed.

The parser now rejects a bare kind in the second field, case-insensitively,
before writing any rows from the batch. Closeout also calls the same parser in
its initial Python process, before scorecard writes, assembly, or other stages.
Malformed second-field conditions and unknown third-field kinds therefore leave
project files unchanged; correcting the entry permits a plain rerun without
`PASS=<id>`. Later capture retains its own validation. Two-field conditions such
as `compare the callers` and explicit third-field kinds retain their meanings. Subject-only
and tagged-NOTES capture still leave the evidence condition for the operator;
the check does not infer whether arbitrary prose is meaningful.

For new rows, explicit nonempty `FOCUS` wins. Otherwise the capture uses only
`corridor_objective.selected_corridor` from `current_pass_plan.json` when both
`project` and `intended_pass_id` match. Integer and digit-string pass IDs match
numerically; booleans and other types do not. Missing, unreadable, malformed,
legacy, or mismatched plans warn and leave the corridor blank. Legacy generated
clusters and anchors are not treated as selected corridors. Missing context
does not discard the operator's deferral or fail an intentional legacy recheck.
An empty or duplicate-only capture needs no context and emits no new warning.
Existing authored rows, including historical blank corridors or conditions,
are not repaired automatically; repeat capture remains byte-idempotent.

- Reject kind keywords misplaced in the condition field before writing the
  ledger, with the supported `subject :: revisit condition :: kind` syntax in
  the diagnostic. Preserve valid two-field entries and meaningful conditions;
  this check does not claim to judge the quality of arbitrary prose.
- Prefer an explicit nonempty `FOCUS`; otherwise use the corridor saved for
  the matching project and pass. Specify missing/legacy-plan behavior and
  diagnose missing context without borrowing another pass's objective.
- Preserve existing authored rows and repeated-closeout idempotence. Do not
  silently rewrite old conditions or classify incomplete entries as runtime
  evidence. Review any required ledger migration separately.

Done when: both misplaced keywords fail without ledger changes; valid static
and runtime entries retain their meanings; explicit focus wins, a matching
saved corridor fills an omitted focus, and a mismatched plan cannot supply it.
Exercise both the parser and the canonical closeout wrapper.

Validation: eight focused Python tests, 53 closeout/proof-debt shell cases, and
five deliberate regressions pass their expected assertions. The repository run
passed 665 of 666 shell cases; the emulator-runner case was blocked by the
sandbox's refusal of `ps`, then passed all 17 of its tests in an unrestricted
retry. The 1,206 Java tests passed separately because the initial shell failure
stopped `make test` before Java. Strict playbook, hygiene and diff checks pass.

Copied-ledger checks preserve all 113 authored rows in 23 projects, append only
the requested new row, and leave bytes unchanged on repeated or rejected capture.
Three historical kind-only conditions and seven blank corridors remain authored
debt for separate review; this implementation does not migrate them. The check
does not claim 23 full project-verification runs.

The reviewed revision's representative largest-source closeout was measured
with identical inputs, one warmup and three alternating pairs, including a new
deferral on every run.
Median wall time changed by +0.31%; all measured runs completed with relaxed
verification. The new corridor was recorded and existing rows were preserved.
No assembly or subprocess invocation was added, and packet preparation is
unchanged. No all-project timing campaign was run.

The preflight follow-up adds no process or assembly invocation. Its regression
rejects both bare kinds and an invalid third-field kind before verification,
compares every project-file hash, then completes a corrected ordinary closeout.
Focused correctness checks cover the follow-up; the reviewed timing and corpus
results were not rerun.

<a id="explicit-deferral-integrity"></a>
### PI-7 integrity follow-up — 2026-10-15

Merged in [PR #159](https://github.com/khansen/nesrev/pull/159) and integrated
before the third observation window. Independent re-review approved
`ac2a91b9b`, including the preflight, ambiguous-match warnings and documentation
revisions. The earlier PI-7 record
above describes its original delivery; this follow-up replaces subject-only
explicit capture.

Explicit subjects now retain their trimmed spelling, order and full length.
Two keys sharing the first three normalized words remain separate. Legacy
normalized and curated rows are recognized by their original deferral text on
rerun; existing rows are preserved. Use established curated keys for ongoing
gaps. Repeat detection groups exact subject strings: `Cue identities`,
`cue identities` and `cue identity` are now three keys, whereas the old heuristic
grouped them together. Reuse the same spelling and case across passes; no
historical migration or cross-key equivalence is introduced. When an explicit
entry matches only an existing subject column with different deferral text,
capture preserves the row and warns on stderr. Inspect that match and choose a
distinct key if it is a different gap; matching curated keys remains supported.

Explicit entries require a subject and nonempty condition, with an optional
valid kind. Missing/empty/extra fields and conflicting duplicate subjects fail
the entire batch in existing closeout preflight, before any writes. Identical
duplicates remain idempotent. Closeout now rejects `Deferred:` tags in NOTES
unless complete explicit entries are supplied, before verification or any
project-file writes. Empty, whitespace-only or separator-only `DEFERRALS` do
not bypass this refusal. Supply `DEFERRALS="subject :: condition"` and rerun;
no manual ledger repair is needed after this refusal. The standalone capture
helper still supports draft tags, but this is not a closeout path. The process
check rejects each open row with a blank condition, independent of debt ratios;
closed historical rows and aggregate advisories remain unchanged.

Validation: `python3 -B tests/deferral_capture_test.py` passes 13 tests.
The shell harness's 44 relevant deferral, proof-debt, closeout and process-check
cases pass, including canonical Make closeout and external-tool-root forwarding.
Invalid explicit batches and tag-only closeout leave all fixture project-file
hashes unchanged. The new tag test uses the real process checker, proves
verification never ran on refusal, then completes an ordinary corrected rerun
with one fully populated row. Other closeout stages are fixture stubs.
Valid reruns preserve authored rows. A single blank open condition among 20
complete open rows fails with its ledger line and subject; empty ledgers and
closed history pass. Strict playbook, repository hygiene and diff checks pass.

Bad-direction proof in a disposable copy restores the master versions of
`scripts/deferral_capture.py` and `scripts/project_process_check.sh`:

| Check | Exit and expected failure |
|---|---|
| `python3 -B tests/deferral_capture_test.py` | 1: distinct-key loss, accepted malformed batches and duplicate conflicts |
| Shell `test_closeout_rejects_invalid_deferrals_before_any_writes_or_gates` | 1: expected refusal 2, received success 0 |
| Shell `test_process_check_requires_each_open_deferral_condition` | 1: expected refusal 1, received success 0 |

Copied-ledger checks cover all 23 local projects and preserve all 143 authored
rows. Every copy accepts two distinct explicit keys, preserves bytes on rerun,
and rejects malformed capture without writes. No open row lacks a condition;
there is no newly exposed condition debt or migration. Rechecking all 143 rows
by their stored subject preserves each file byte-for-byte; 124 legacy matches
warn because their descriptions differ from their keys. This is the intended
nonblocking diagnostic, including for curated keys. This is a ledger sweep,
not 23 full project-verification runs.

On the largest local assembly source, one warmup per version followed by three
alternating before/after pairs measured median changes of -0.29% for
`project-process-check` and -0.99% for relaxed `project-pass-closeout`.
Every run completed successfully; closeout captured a new deferral each time
from restored identical inputs. No command or assembly invocation was added.
No all-project timing campaign or live post-integration observation was run.
These timings cover the original explicit-input path; no assembly or process
was added by the review revision.
The revision was also compared directly with `abdc2cfce` on the largest source
using ordinary NOTES and no explicit deferrals: one warmup per version and
three alternating measured pairs all passed, with a -0.44% median change in
relaxed closeout time. The standalone process-check implementation is unchanged
by this revision, so its timing was not repeated.

Review-revision mutations in disposable copies:

- Restoring `abdc2cfce`'s `project_pass_closeout.sh` makes the shell case
  `test_closeout_deferrals_reject_tagged_notes_before_writes_and_allow_corrected_rerun`
  exit 1: `verification ran before tagged deferral rejection`.
- Restoring `abdc2cfce`'s `deferral_capture.py` makes
  `python3 -B tests/deferral_capture_test.py DeferralCaptureTests.test_subject_only_matches_warn_without_rewriting_legacy_or_curated_rows`
  exit 1 in all three subcases: the subject-only-match warning is absent.

Shell cases run with the repository test library and workflow cases sourced,
`REPO_ROOT` set to the disposable checkout, a fresh `NESREV_TEST_TMPDIR`, and
`set -euo pipefail`. The production checker is not stubbed in the tag test.
Restoring the master capture against the revised synthetic fixtures still
makes `python3 -B tests/deferral_capture_test.py` exit 1 (24 failed assertions).

The three revised branch diffs apply cleanly together to `75665c03c`.
In that disposable combined checkout, `make test` exits 2: 684 of 685 shell
cases pass, while the process-cleanup case cannot execute sandbox-denied `ps`.
Its unrestricted `python3 -B tests/fceux_runner_test.py` retry passes all 17
checks. `javac NESrev.java NESrevTest.java -Xlint:unchecked` and
`java NESrevTest` then pass all 1,206 Java tests; the initial shell failure had
prevented Make from reaching them. No full-corpus verify/CI or live agent run
was performed.

<a id="pi-8-analyzer-portability"></a>
## PI-8 — Demonstrate runtime-analyzer test portability at handoff

Status: merged in [PR #143](https://github.com/khansen/nesrev/pull/143) after
approval of `a1a586b10`, including the temporary-directory isolation follow-up. Review of `05c8fa6cd`
accepted the existing contracts; the follow-up review verified the refusal and
Git-discovery regressions and their bad-direction behavior.
The baseline maturity
checker accepts an analyzer that reads an ignored local capture through its
source path; its temporary working directory does not isolate the analyzer.
Review packets run only structural runtime checks, so neither behavior proves
that fixtures work from committed inputs alone.

The implementation reuses the manifest and existing acceptance/refusal runner
in a clean export of the reviewed commit. The affected input scope, dependency
boundary, per-case evidence and packet schema-3 refusal contract are defined
in [the packet specification](PROJECT_PASS_REVIEW_PACKET_SPEC.md#runtime-analyzer-portability).
The new step is independent of assembly prerequisites and does not add work to
pass preparation, next-pass generation or ordinary process checks.

- Audit the current [runtime-evidence fixture contract](agent_playbook/RUNTIME_EVIDENCE.md)
  and packet checks first. Define the affected analyzer/manifest/fixture scope,
  then reuse declared test commands rather than inventing another test registry.
- Run the affected synthetic tests in a clean export with only committed test
  inputs and documented tool dependencies. They must need no reference ROM,
  emulator, ignored capture or live recording. Keep this check separate from
  ROM-dependent parity gates and pending live runtime evidence.
- Include command, checked scope and actual exit status in the handoff evidence.
  Missing, failed or unrun required tests must be visible and prevent acceptance;
  finding a test filename is insufficient.

Done when: a portable positive fixture passes; a failing test and a test relying
on an ignored local capture are refused with useful diagnostics; malformed
synthetic evidence fails its analyzer's refusal case. Existing supported
analyzers and changes outside the affected scope retain explicit, tested
behavior. Passing fixtures do not close pending live-capture questions.

Validation: 20 portability tests, 39 existing runtime-contract tests, 39 packet
parser tests, and 15 packet shell cases pass. The packet tests exercise the real
handoff CLI, including successful acceptance and refusal of failed or unrun
runtime evidence. Nine deliberate regressions fail their intended assertions.
All 23 projects retain their runtime classifications: 19 active fixture cases
across two projects pass from clean exports; the remaining projects explicitly
require no execution. This is a runtime-contract sweep, not full-corpus CI.

The earlier full suite at `c8ed5b319` passed 670 of 671 shell cases; the remaining
case hit the sandbox's process-inspection restriction, then its 17 tests passed
on an unrestricted retry. All 1,206 Java tests passed separately. The final
export and membership-lookup changes were checked with the affected runtime
and packet tests and the corpus sweep; the full suite was not repeated.

The larger project with active runtime contracts supplies the packet timing
sample. One warmup per variant followed by three alternating measured pairs
gives +3.27% median wall time, within the 5% budget. All measured packets validate;
verification uses `ALLOW_UNRESOLVED_LXXXX=1`. This is one affected-path sample,
not corpus-wide timing. Export only the reviewed project and shared root entries,
and batch Git membership lookup, to keep the added execution within budget.
No new fixture execution is added to pass preparation, next-pass or process checks.

The review follow-up refuses a resolved temporary root or scratch directory
inside the reviewed repository, including symlink aliases, before executing any
fixture. Every case uses the validated external scratch parent, with child
`TMPDIR` and `GIT_CEILING_DIRECTORIES` set there. The regression reproduces an
analyzer finding ignored inputs through Git under a repository-local `TMPDIR`;
the external-parent test also verifies that neither the case directory nor the
export discovers an unrelated enclosing repository. Affected tests and both
active corpus contracts were rerun. The prior timing receipt is reused: this
bounded path validation adds no subprocess, export, or fixture execution; no
new performance run or full-suite run was needed.

## PI-1 — Make checker coverage explicit

Baseline defects: the [parser](scripts/used_by_xref_check.py) accepted a bare
consumer name but ignored the same name in backticks, allowing zero parsed
claims despite many annotations. Separately,
[PPU packet checking](scripts/ppu_packet_line_check.py) required a particular
label substring, excluding documented streams with other semantic names.

Work:

- Recognize the supported annotation syntax, including backticked names,
  while preserving legitimate indirect-consumer handling.
- Discover PPU streams from explicit format/inventory evidence rather than
  requiring `PpuPacketStream` in the label. Handle internal payload labels.
- Report discovered, parsed, checked, and unsupported/skipped counts.
  Unexpected zero coverage must be visible, not indistinguishable from a
  successful check of every declaration.

Done when: an invalid backticked consumer and a malformed stream with a
different label name fail for the intended reasons; valid direct and
indirect consumers and valid streams pass; unsupported cases are identified.

### PI-1 implementation and activation prerequisites

The implementation accepts backticked consumers and checks concrete consumer
names even when their dispatch qualifier is unsupported. Packet discovery now
uses explicit `Format:` declarations, with support for declared payload fields,
shared suffixes, and same-address aliases. Both checks report their coverage
and identify unsupported cases; see [checker coverage](agent_playbook/CHECKER_COVERAGE.md).

Local validation on 2026-09-05:

- `make test`: exit 0; 568 shell and 1206 Java tests passed.
- Three new regressions fail against the old checkers at `683a22c64`:
  backticked missing consumer, missing consumer behind an unknown dispatch
  qualifier, and malformed packet under a nonstandard label name.
- Fresh-xref corpus scans exercised direct, qualified, partially supported,
  and unsupported annotations. Packet scans exercised ordinary, grouped,
  shared-suffix, and alias declarations. Coverage counts do not assert
  semantic ownership; grouped declarations must not claim coverage of only
  their first stream.
- Representative strict CI and applicable pass-time checks were exercised in
  an isolated corpus worktree. An existing unresolved-label gate still fails
  strict CI on an unfinished input; relaxed verification is not strict CI.
  Per-input commands, counts, failures, and migration evidence stay local.

Initial independent review of `8ebf6fe10` approved the consumer changes and
identified PPU boundary gaps. Follow-up regressions cover grouped wording
after the canonical prefix, payload fields inside shared suffixes, and
annotated same-address aliases. All three fail against `8ebf6fe10` and pass
with the fixes. A further regression covers either field owner across three
chained aliases or suffixes, including unrelated-owner refusal; it fails
against `20c9069e4` and passes with shared ownership context. Both independent
reviewers in tmux panes `%0` and `%1` approved `70e488a7f` on 2026-09-05;
no material implementation findings remain. The implementation landed in
[PR #98](https://github.com/khansen/nesrev/pull/98).

The newly exposed stale consumer names and matching current memory-map
references were corrected in a local-only migration using current
producer/consumer evidence. Historical pass records remain unchanged.
With the reviewed checkers overlaid, verification and full CI pass for every
migrated input. A fresh-xref corpus scan reports zero consumer hard errors;
unsupported annotations and ownership advisories remain explicit. No assembly
instructions or data bytes changed. Packet-layout advisories remain advisory,
not new hard gates or gameplay-bug claims. Friction queues remain unchanged.

Include the verified local migration when updating the corpus to the merged
tooling, then rerun the affected gates. Keep its detailed evidence local.

## PI-2 — Validate evidence membership and runtime deferrals

Evidence: the [policy-baseline checker](scripts/policy_baseline_audit_check.py)
compares live totals with summary markers without validating the manifest's
actual membership and dispositions. The
[blob-disposition row validator](scripts/data_blob_dispositions_check.py)
accepts a `runtime_gated` row with no artifact when its prose fields are
populated. That row-level probe does not establish that every other project
gate can be bypassed.

Work:

- Give the active policy manifest an explicit reference and validate its
  member set, applicable dispositions, and retained-headerless accounting
  against current source evidence, not just matching totals.
- Separate active evidence from immutable review snapshots. Do not subject
  every archived review to current-symbol linting or rewrite historical prose.
- Cross-link runtime-gated inventory rows and deferrals to a specific open
  question, trace plan, tracked runner/analyzer, and acceptance/refusal
  fixtures. A filename or nonempty explanation alone is not sufficient.
- Reconcile runtime debt across inventories and deferrals; preserve legitimate
  explicitly supported runtime gaps without claiming the question is resolved.

Done when: equal-count/wrong-member manifests, invented disposition counts,
and artifact-free runtime deferrals fail; valid manifests and executable
runtime plans pass; negative fixtures reject traces missing required signals.

The policy-evidence lane uses a separate [active CSV manifest](agent_playbook/POLICY_BASELINE.md)
to validate exact live membership, inventory classification, applicable review
and localization decisions, and distinct retained-headerless accounting.
Historical snapshots remain unchanged. The runtime-evidence lane is separate;
implementing policy membership does not resolve runtime deferral validation.

The runtime lane introduces an [active question manifest](agent_playbook/RUNTIME_EVIDENCE.md)
that reconciles open runtime deferrals and runtime-gated blob/family artifacts.
Maturity executes tracked analyzer acceptance/refusal fixtures; process checks
report structural coverage without claiming fixture execution. Capture plans
can remain legitimately pending; fixtures never establish a live result.

Activation review identified a legacy runtime classification without matching
trace infrastructure. Keep that unsupported evidence failing; do not invent a
manifest, substitute unrelated trace assets, or reclassify merely for green.
The supported manifest migration is prepared locally. On 2026-09-06 the user
authorized lifting the activation hold while retaining newly exposed missing
evidence as genuine CI failures. Rebase, rerun shared tests and joint corpus
checks, then obtain fresh approval before PR creation and merge. This rollout
does not authorize new semantic passes or captures, and it must not describe
accepted failing debt as green or runtime questions as resolved.

Prior implementation validation at `7b19459aa`: 39 focused Python cases, 587
shell tests and 1206 Java tests passed. Four regressions failed against
pre-change tooling: artifact-free
blob, existing plan without question manifest, artifact-free runtime family,
and missing optional blob inventory hiding an open runtime deferral. Preliminary
independent review confirmed the activation boundary and executable-fixture
mutation sensitivity; its optional-inventory finding is fixed and tested.

Fresh independent review approved `c405c932a` and supported migration readiness
with no material findings. Rebased validation passed 39 focused cases, 600 shell
tests and 1206 Java tests. Four unchanged-base validator regressions and four
disposable mutation directions (six intended assertions) reject the weakened
behavior. Independent execution reproduced these controls and the complete
runtime-contract sweep: 20 of 22 inputs pass; two retain missing evidence.

Prepared joint strict CI passes 17 of 22 inputs: the same four unfinished-input
failures plus one newly exposed, user-accepted runtime-evidence failure. All 22
binary comparisons pass. Independent review checked that exact delta against
the baseline's 18 passing inputs and reviewed the supported positive fixture
plus six isolated refusals. The initial cold-cache run is retained as failed
setup, not activation evidence; canonical non-authoring preparation and the
corrected run preserve tracked state. These results establish tooling delivery,
not completed runtime questions or green corpus CI.

Policy-lane validation: `make test` passes 585 shell and 1206 Java tests.
Five synthetic regression cases fail against the previous implementation:
equal-count wrong membership, invented reviewed counts, overlap double
counting, inapplicable dispositions, and source renames preserving totals.
The read-only corpus sweep found that every input needs the new active
manifest; pre-existing incomplete audit fractions remain unfinished work.
Local migration and joint validation must precede activation.

## PI-3 — Reuse executable consumer-boundary audits

Evidence: physical table extents and documented lengths can differ from the
actual read range when a helper changes an index or callers select overlapping
records. Boundary claims need caller-state and consumer evidence, not merely
the next label's address.

Work:

- Reuse bounded techniques from local consumer audits when their contracts
  recur; express shared regression cases with synthetic data and consumers.
- Distinguish physical allocation, selected record, and actual read range.
  Account for carry, eight-bit wrap, helper side effects, overlapping tails,
  and multi-channel timing where the consumer requires them.
- Tie checks to fresh source/listing evidence. State which caller invariants
  remain manually proved; an enumerator is not a general control-flow proof.

Done when: regression fixtures reject the old incorrect bounds/models,
including relevant wrap and helper effects, while the correct models pass.
Keep game-specific semantics local; extract shared machinery only where the
same contract genuinely recurs. Do not attempt a general 6502 proof engine.

The [consumer audit helpers](agent_playbook/CONSUMER_AUDITS.md) provide fresh
assembled evidence, instruction contracts, byte arithmetic and bounded index
walks, plus separate allocation/selected-record/actual-read reporting. They are
optional audit machinery, not a new corpus-wide heuristic gate. Caller-state
and scheduler invariants remain explicit local proof obligations.

Validation: 15 focused Python cases, 587 shell tests and 1206 Java tests pass.
Six disposable mutation directions are detected: discarded carry, wrong helper
increment, zero-count omission, hidden out-of-allocation reads, disabled byte
contracts and stale assembled evidence. Two existing local audits reuse the
helpers and produce byte-identical before/after reports; all 12 of their existing
regressions and both canonical verify/strict-CI runs pass. The adapter migration
changes no assembly or semantic claims and stays on the local corpus branch.
Independent review additionally checked exhaustive byte arithmetic, all byte
counter starts, representative old/new adapter equivalence and changed helper
bytes. It approved implementation and adapter readiness with no material findings.

## PI-4 — Make review bundles self-contained and reproducible

Evidence: the [review-packet wrapper](scripts/project_pass_review_packet.sh)
labels a project-filtered history section “Complete Commit List And
Diffstat,” omitting root-level changes. Other reproducibility gaps include
cold coverage caches, missing private ROM fixtures, and different assembler
binaries reporting the same version.

Work:

- Show the complete review-range commit/path inventory, with focused project
  diffs clearly distinguished from root/shared changes.
- Record resolved tool paths and hashes, reviewed SHAs, fixture prerequisites,
  and deterministic cache-preparation steps. Retain existing HEAD and clean
  tracked-worktree guards.
- Provide a terminal summary of every required gate's command and actual
  exit status, including explicit not-run results and all failure categories.
- Keep the [packet specification](PROJECT_PASS_REVIEW_PACKET_SPEC.md), wrapper,
  [handoff parser](scripts/agent_review.py), and fixtures aligned. Preserve the
  structured gate sections the parser consumes or update that consumer in
  the same change. Distinguish successful packet generation from successful
  required gates.
- Distinguish missing prerequisites from parity or semantic failures. Provision
  private ROM fixtures only from authorized local inputs; never download or
  commit them. Keep committed-pass validation separate from mutating closeout.

Done when: a root-only change is visible, a cold review worktree prepares its
evidence or fails clearly, tool/fixture mismatches are diagnosed, and the
summary cannot hide a failed or unrun gate behind successful earlier output.
Producer/consumer fixtures must verify the summary and handoff validation
agree on the reviewed SHA and each required gate's status.

The implementation records unfiltered history and per-commit changed paths,
resolved tool/input hashes and optional expected-hash comparisons, explicit
non-authoring cache preparation, and every required result in a terminal JSON
summary. The shared parser checks all three gates and four supporting results
against their fenced sections; failed, unrun, incomplete or contradictory
evidence blocks handoff, including reused packets. Legacy ephemeral packets
must be regenerated; archived review judgements remain untouched.

Initial independent review found unchecked supporting commands, missing output
blocks and assembler/metadata contradictions. The revised contract checks every
command's tool, target and subject, binds build selections to recorded tool
identity, and requires captured output while permitting genuinely empty output.
Explicit/reused handoff regressions cover those refusals. Independent re-review
approved `6c0e04186` with no material findings. Final validation passed 31 focused
cases, 597 shell tests and 1206 Java tests; both representative cold-cache
integrations pass without tracked-state changes. Seven new regressions reject
the old validator for the intended missing-refusal reasons. Independent review
also passed 46 shell cases, 13 positive controls and 55 malformed-packet refusals.

## PI-5 — Separate intake snapshots from historical baselines

Evidence: [project intake](scripts/project_intake.sh) synchronizes pass 0
after expensive checks. Legacy scorecards can lack that row, while existing
historical measurements can be silently replaced with current values.

Work:

- Preflight scorecard compatibility before expensive work.
- Separate refreshable current intake measurements from immutable historical
  pass measurements. Define an explicit migration for legacy scorecards;
  never invent an original baseline from today's counts.
- Refuse or explicitly migrate an incompatible historical row rather than
  silently overwriting it.

Done when: fresh scaffolds, legacy pass-1-only scorecards, and existing
historical pass-0 rows have tested behavior; current snapshots refresh
idempotently and historical measurements remain intact.

The [intake-baseline contract](agent_playbook/INTAKE_BASELINES.md) separates a
once-only marked scaffold capture from current intake snapshots. Existing rows,
including retrospective measurements, remain unchanged. Missing original
pass-zero history requires an explicit idempotent migration receipt rather than
invented counts. Preflight runs before expensive work; publication follows
successful canonical intake gates and refuses intervening scorecard changes.
Direct pass-zero synchronization no longer infers unrun outcomes or refreshes
historical measurements. Active semantic-pass measurement behavior is retained.

Independent review approved `28427b0a4` with no material findings. Final
validation passed 19 focused cases, 599 shell tests and 1206 Java tests. Two
old-wrapper regressions and five disposable mutation directions fail as intended.
All 22 copied scorecards preserve history: 20 require no migration and two
require explicit receipts reproduced byte-for-byte by independent review.
Representative canonical intake runs and repeats pass with unchanged historical
rows and byte-identical repeated snapshots. Independent checks additionally
cover low-level replacement/file-sync failures and four pass-zero refusal modes.

## Friction files are triage queues, not archives

<a id="learning-candidate-noop"></a>
2026-10-15 follow-up: merged in
[PR #160](https://github.com/khansen/nesrev/pull/160) and integrated before
the third observation window. Independent re-review approved `6e5fa50d8`,
including the launcher-guidance assertion.

Generated role and launcher prompts require exactly `_None._` alone when there
is no new candidate. Status explanations and references to already-queued issues
belong outside the section; recurrences need new evidence. Ingestion remains
conservative: substantive text following a no-candidate statement is retained.
No receipts, archives, states or admission gates change. This wording addresses
duplicate queue work; the [third-window assessment](#third-window-assessment)
records the observed use without claiming a causal productivity gain.

Validation: `python3 -B tests/agent_review_artifact_test.py` (11 tests),
`python3 -B tests/process_friction_test.py` (36 tests), and
`python3 -B tests/agent_review_tmux_test.py` (68 tests) pass. These synthetic
fixtures cover both roles, project/checkout boundaries, the exact no-candidate
instruction in `kickoff()` output, sentinel no-ops and preservation of new
evidence. No game data is needed.
In a disposable copy, replacing `scripts/agent_review.py` with the master
version makes
`python3 -B tests/agent_review_artifact_test.py ArtifactTests.test_both_role_prompts_require_an_unambiguous_no_candidate_section`
exit 1 for both roles: the exact sentinel instruction is absent. Removing the
shared-guidance line from `scripts/agent_review_tmux.py` in a disposable copy
also makes
`python3 -B tests/agent_review_tmux_test.py LauncherTests.test_kickoff_requires_an_unambiguous_no_candidate_section`
exit 1 because the instruction is absent from the launcher's kickoff text.
Strict playbook, repository hygiene and diff checks pass. Prompt text adds no
command, assembly or validation work; full handoff timing was not rerun for
this wording change.

Recommendation: prune entries after triage. Keep only candidates still
awaiting a decision or a specific missing piece of triage evidence. Accepted
but unfinished implementation belongs in this plan or another named backlog,
not in both places.

All removal actions below require the migration and tests in the cleanup
sequence first. During migration, keep existing entries and their import
markers until their durable receipts are saved and receipt-aware ingestion
is active; the routed destination already owns the implementation work.

| Disposition | Durable destination | Queue action |
|---|---|---|
| Accepted tooling/harness fix | Named plan item or issue, with evidence and acceptance criteria | Remove once routed |
| Accepted reusable rule | Canonical playbook, after process review | Remove once promoted |
| Project-specific evidence gap | Appropriate project inventory, trace plan, or qualifying working note | Remove once routed |
| Duplicate | Existing destination, adding any distinct evidence/source links | Merge and remove |
| Fixed, superseded, or discarded | Brief rationale in the triage change/commit or decision record | Remove |
| Not yet decidable | Concise candidate with source link and missing decision/evidence | Retain |

Historical review text belongs in
`projects/<slug>/docs/reverse_engineering/reviews/pass-<id>.md`.
Git history preserves previously committed queue contents and pruning
decisions. Do not create a second prose archive or retain completed-item
tables inside the queues. Once empty, a friction file may be removed: the
archiver already creates it when new candidates arrive.

Before pruning, check archive coverage and tracking status. Git history does
not protect untracked notes. Preserve unique useful evidence and its disposition
in the appropriate durable destination before removing its sole copy.
Check the relevant content, not just whether an archive file exists:
`learning_artifacts` in [review ingestion](scripts/agent_review.py) imports
implementation notes as well as reviews and responses, while `render_archive`
retains only reviews and responses. Implementation-note candidates therefore
need the same content-preservation check, even when their linked review is
already archived.

### Queue cleanup and ingestion follow-up

The [receipt implementation](agent_playbook/PROCESS_FRICTION.md) now separates
durable decisions from queue residency. Validation at `bc7db7435` passed
34 Python cases, 586 shell tests and 1206 Java tests. Copied migration checks
covered all 20 existing queues without changing their live content. Six named
regressions fail against pre-receipt ingestion; independent review additionally
exposed fenced-marker, empty-example, unknown-metadata and atomic-write gaps.
Those fixes and the remaining extraction-layer correction were independently
approved at `8bafbf7f4` and merged in PR101. Final validation passed 35 focused
Python cases, 586 shell tests and 1206 Java tests. Receipt backfill preceded
the first local pruning batch; undecided entries remain queued.
These are mechanism tests, not dispositions for the actual queue contents.

Execute in this order; steps 1–4 are prerequisites for actual queue pruning.

1. Record durable destinations and dispositions for existing candidates,
   mapping accepted work to PI-1 through PI-5 or another named owner. Recheck
   current tooling, preserve unique useful content, and consolidate distinct
   evidence at the destination without yet deleting queue entries or markers.
2. Implement receipt-aware [review ingestion](scripts/agent_review.py).
   Current deduplication depends on markers inside the queue; deleting them
   lets re-archiving recreate old work. Backfill durable receipts from existing
   marker-only queues before removal, recording candidate source identity,
   content, disposition, and destination references outside the queue.
   Activate receipt-aware ingestion before pruning is exposed to normal
   re-archiving. Keep receipts small; storage/schema is an implementation
   decision, not a second narrative archive. A receipt persistence failure
   must leave the candidate and markers available for retry.
3. Pass the migration and ingestion tests below in disposable fixtures,
   including existing queues and complete queue-file deletion. Do not use
   live queue pruning as the migration experiment.
4. Clarify the canonical
   [triage rule](agent_playbook/REVIEW_AUDITS.md#process-learning-triage):
   after migration, durable routing or promotion ends queue residency even
   when implementation remains. Keep the receipt prerequisite explicit.
5. Only then prune routed, resolved, obsolete, and non-actionable entries,
   checking each removal has its durable disposition and any required import
   receipt. Remove empty queue files if useful. Do not move all old prose
   wholesale into another backlog or keep completed-item tables in the queue.

Migration and ingestion acceptance tests:

- Start with existing marker-only queues: route → backfill receipts → prune
  → re-archive. Unchanged candidates stay absent, including when the entire
  queue file was removed.
- Fail receipt persistence: the candidate remains available for a safe retry;
  no removal occurs on an incomplete receipt write.
- Re-import a partially triaged block, or triaged candidate A alongside new
  candidate B: A stays absent and B remains discoverable. A whole-document
  hash change must not reopen A; a pass-level “seen” flag must not suppress B.
- Re-import unchanged candidate content under a new run or rebased SHA:
  the already-triaged item stays absent without suppressing new evidence.
- Explicit empty or non-actionable sections create no queue work; genuinely
  new candidates do create it.

Known cleanup candidates include already-fixed Make dollar transport and
scoped-owner snapshot issues, items already recorded as disposed, and
superseded blanket worked-example requirements. Do not revive
these without a fresh reproducer. Likewise, a rejected or false-positive
heuristic is not a pending hard-gate requirement merely because it appears
in an older review.

This document records the proposed work and lifecycle. It does not itself
change tooling, playbooks, review archives, or existing friction queues.
