# Controlled Project Experiments — Specification

Status: proposed; no experiment controller, isolation backend, or evaluator is
implemented by this document. Approval of this specification does not launch
runs, waive reference intake, authorize spending, or publish artifacts.

## 1. Purpose and scope

Provide a repeatable, initially self-hosted way to compare independent,
from-scratch disassembly runs. Candidate factors include supplied prior
projects, manuals and FAQs, implementer and reviewer models, reasoning levels,
runtime tools, and workflow versions. Preserve enough evidence for an
independent evaluator to explain which output is better, where, and why.

The experimental unit is one fresh run of one ROM under one assigned condition.
A pass, label, claim, or review round is an observation within that run, not an
independent replication. Reproducibility means reconstructing the conditions
and measuring variation; hosted models need not reproduce identical output.

Support two distinct study objectives:

| Objective | Primary comparison |
|---|---|
| Fixed resources | Quality at a preregistered resource limit |
| Target quality | Resources consumed before independent confirmation of the target, subject to a cap |

Pass count and self-declared gold status are descriptive measurements, not
common budgets or independent quality judgments. The first implementation
should support fixed-resource studies; target-quality studies require the
additional stopping contract in section 5.

Shared code, fixtures, examples, commit messages, and eventual PRs remain
project-neutral. Actual ROMs, reference documents, corpus identities, run data,
and findings stay in private local storage. No pushes, production-branch
rebases, or production-project edits are part of running an experiment.

## 2. Roles and existing contracts

The study owner selects questions, resources, permitted inputs, and the human
assistance policy. A deterministic controller prepares and schedules runs,
enforces supported limits, captures artifacts, and dispatches evaluation.
It does not need a continuously running supervisor model.

Each run has one implementer and one pass reviewer, using the existing
[handoff protocol](AGENT_REVIEW_PROTOCOL_SPEC.md) and
[review packets](PROJECT_PASS_REVIEW_PACKET_SPEC.md). Either role can use a
supported agent application; model and reasoning choices are independent.
Neither role participates in final evaluation of its own run.

The evaluator uses fresh sessions and separately governed resources. It can
inspect the entire frozen output and the owner's full reference set. A human
adjudicator resolves consequential disagreements or unsupported conclusions.
Evaluation findings never reach an unfinished experimental run. The only
permitted stopping signal is the preregistered target result in section 5.

Retain the canonical [intake](agent_playbook/NEW_PROJECT.md),
[pass workflow](agent_playbook/PASS_WORKFLOW.md),
[quality criteria](agent_playbook/QUALITY_REVIEW.md), and
[scoped permissions](agent_playbook/AGENT_PERMISSIONS.md). Existing
[analysis bundles](ANALYSIS_BUNDLE_SPEC.md) bind assembled evidence to inputs;
they do not certify an experiment's conditions or semantic correctness.

New study-level state lives outside the run's checkout and is controller-owned.
Each run owns its own `.agents/current.json`, watcher identities, tmux session,
agent homes, and Git repository. Never use a production review state file to
coordinate experiments or share one state file between runs.

## 3. Frozen study manifest

Before allocating runs, validate and freeze a versioned manifest. Store its
canonical serialized bytes and SHA-256 digest with an explicit owner approval
receipt. All defaults must resolve into the frozen manifest; unknown keys,
duplicate keys, unresolved required settings, and incompatible conditions
refuse launch. A plan preview shows inputs, permissions, run count, resource
ceilings, expected manual work, and capabilities the host cannot enforce.

| Field group | Required content |
|---|---|
| Identity | Schema/version, study ID/revision, parent revision if any, question, hypotheses, primary endpoints, planned contrasts, exploratory analyses |
| Design | Factors and levels, explicit condition matrix, ROM blocks, fresh repetitions per cell, allocation seed, run order, concurrency policy |
| Inputs | Exact ROM/container and analyzed-region hashes, private asset IDs, reference/corpus manifests with per-file hashes, allowed network and runtime inputs |
| Software | Tooling commit and exported tree digest, controller version, playbook/prompt/template hashes, assembler and generator identities, host/runtime/OCR dependencies |
| Roles | Agent executable/version, requested and resolved model identity, reasoning settings for each role, exposed generation settings, prompt/context/compaction policy |
| Isolation | Backend/version, mount and network policy, fresh-session policy, permitted plugins/connectors, contamination checks |
| Execution | Primary budget, secondary limits, closeout/shutdown reserves, clock and watchdog contract, checkpoint eligibility policy, metering precision, restart/retry rules, human assistance and permission policy |
| Policy | Experiment-only overrides, affected rules/checks, exact permitted deviations, reference-intake consent requirements |
| Evaluation | Rubric/profile version, reference-set digest, hidden task/sample commitment, evaluator identities/settings, calibration receipt, scoring/denominator rules, adjudication policy, per-phase evaluation budgets |
| Retention | Artifact locations, capture completeness requirements, secret redaction, access controls, retention and export policy |

Keep credentials out of manifests and logs. Private asset identifiers resolve
inside owner-controlled storage; distributable examples contain only synthetic
identifiers. A digest establishes identity, not truth or hostile-tamper safety;
agents must not be able to overwrite manifests, evidence receipts, or outcomes.

Record execution-time resolved settings and timestamps too. If a backend
cannot expose an exact model snapshot, record that limitation and the observed
model alias. A study requiring a pinned snapshot must refuse such a backend.
Do not silently substitute a missing model, reviewer, tool, or reasoning level.

For an implementer comparison, hold the reviewer and other settings fixed.
If both roles change, label the contrast as a comparison of complete pairings.
Similarly, distinguish manual availability from manual-preprocessing quality
or effort: freeze supplied extraction artifacts, or explicitly include
extraction in the measured workflow and budget.

## 4. Input isolation and deliberate policy variation

### Isolation boundary

Prepare an allowlisted export of the frozen shared tooling and templates into
an independent repository. No existing target disassembly, authored recovery
controls, target-specific semantic hints, or previous run output enters the
starter. Every run begins with the user-supplied ROM and performs intake.
Any common precomputed input must be declared and identical where applicable;
a study beginning after semantic intake is a different study scope.

Sibling worktrees and fresh Git branches are insufficient isolation: shared
objects, other worktrees, home directories, caches, and processes can expose
withheld information. Use an OS-enforced boundary such as a suitably configured
container or VM with a tested allowlist. A backend that cannot enforce the
study's access restrictions cannot claim an isolated comparison.

Provide fresh application state, histories, memories, emulator configuration,
temporary directories, and tool caches. Supply authentication through a narrow
mechanism without importing conversation history or unrestricted host access.
Disable undeclared plugins/connectors and expose no other run's processes,
filesystem, Git objects, sockets, or logs. Review agents and subprocesses obey
the same boundary as implementers. The controller and evaluator stores remain
outside it, even when no other run is currently active.

Network access is denied except for declared services and resources. Model
service access is distinct from browsing. For reproducible reference/runtime
inputs, pre-stage approved snapshots and replay assets with hashes. An arm
studying live search must record retrieved content, provenance, timing, and
network policy; it cannot be described as having fixed external inputs.

### Treatment definitions

Both run roles receive the assigned reference access unless reviewer access
is a separate factor. The evaluator's richer references remain inaccessible
until run outputs are frozen, and are never copied back to the run.

`prior_art: withheld` means no supplied prior-project corpus, comparison index,
or derived project evidence. It cannot remove knowledge learned during model
training. Shared playbooks and generic tooling remain identical across arms;
report their retained domain knowledge as part of the baseline.

`manual: withheld` must specify FAQ, guide, translation, extracted vocabulary,
and browsing access separately. If the intended question concerns access to
all game-reference knowledge, exclude equivalent sources too. Audit the prior
corpus for copies of the target's solution or withheld references. If overlap
is intentional, describe the contrast narrowly as direct manual availability,
not absence of that information. Inventory both source and derived artifacts.

### Explicit policy profiles

The ordinary [prior-project reuse rule](AGENTS.md#prior-project-reuse-gate)
and [reference intake gate](agent_playbook/DOCUMENTATION.md#terminology-crosswalk)
remain the production defaults. A study profile must enumerate each deliberate
override, its justification, affected wrapper behavior, and applicability.

The owner must explicitly approve a no-manual condition after the warning:
the final disassembly's terminology and semantic precision will likely be
lower without a manual. That approval can cover named runs in the frozen
study, avoiding repeated questions. Missing files, an empty folder, approving
this specification, or approving an unrelated study are not waivers. Supplied
FAQs still require processing. Manual-present arms stop if their promised
manual is absent or unreadable; they never silently switch conditions.

Do not make agents invent an analogue or pretend a withheld check ran.
Experiment-aware integration must report `not applicable under study profile`
only for the explicitly varied process requirements. Preserve raw check exit
statuses and diagnostics separately from study eligibility. If a current
wrapper cannot represent the profile, implement and review that integration
before launch; do not swallow its failure or rewrite it as a pass.

Parity, evidence integrity, normal permissions, and honest reporting remain
mandatory. Approved ablations establish condition compliance, not weaker
semantic truth standards. Report experimental target attainment separately
from ordinary gold approval whenever the normal process contract differs.

## 5. Resource accounting and stopping

Choose a primary resource ceiling and record secondary ceilings. All run
agent work counts: intake, extraction, planning, implementation, pass review,
rework, context reconstruction, and closeout. Record tool/runtime time and
human assistance too. Evaluation has a separate fixed policy and budget.

Record tokens by provider category where exposed, measured spend where
available, active elapsed time, wall time, tool usage, and human minutes.
Include caching or discounts in cost attribution. Mark unavailable measures
as unavailable; never infer precise spend from subscription quota percentages.
Different tokenizers make token counts imperfect cross-model budgets. State
what the chosen ceiling actually equalizes and report other measures alongside.

A launch preflight must prove that the backend can meter and bound the selected
resource. Document measurement lag, possible in-flight usage, and cancellation
behavior. Reserve enough headroom for that bound. Interactive CLI adapters
without bounded token/spend control may participate in wall-time-limited
pilots, with tokens reported observationally; they must not claim a hard
token/spend cap. Prompt instructions alone do not enforce a ceiling.

At the preregistered reserve threshold, refuse another semantic pass and ask
the pair to finish review/closeout within the remaining budget. Reserve a
separate shutdown margin: fence new dispatch and begin cancelling owned work
early enough that writers stop by the hard limit. Freeze available evidence;
an incomplete final pass receives no unmetered finishing time. Retain the
unfinished tree and review state separately from the last eligible checkpoint.

### Deadline enforcement

For the v1 wall-time budget, start the clock before launching either agent,
including bootstrap. Authentication waits, approvals, needs-input pauses,
reviews, and session restarts do not pause or reset it. Record provisioning
and preflight time separately; neither may perform agent work on the task.
Freeze the duration and reserve policy in the manifest, then record the start,
deadline, clock identity, and shutdown bound in controller-owned run state.

A trusted supervisor outside the agents' writable environment enforces that
deadline independently of the study controller and tmux watchers. Killing or
disconnecting the controller must not leave an unbounded agent or emulator.
The supervisor owns the run's containment boundary and rejects attempts to
extend its deadline. Loss of enforcement must stop owned work and prevent
redispatch; detecting overspend afterward is not successful limit enforcement.

Recovery uses the original deadline. The backend must account for suspend and
clock discontinuities; if it cannot prove the remaining allowance after a
restart or reboot, keep the run stopped and record an infrastructure failure.
A missed bound is a recorded protocol deviation, never a compliant capped
run. Remote request cancellation and residual billing remain observable
limitations; v1 makes no hard token or monetary guarantee.

### Checkpoint eligibility

The primary fixed-resource output is the latest checkpoint meeting the
preregistered parity/review requirements within budget. If none exists,
report that fact and the failure outcome. Secondary inspection of unfinished
work must be labeled and cannot replace the primary output after seeing scores.

Make eligibility a durable receipt from a trusted recorder. At a quiescent
handoff boundary, before agents can edit again, capture and bind:

- the exact reviewed Git head/tree and immutable copies of required artifacts;
- the matching completed review verdict and parity/gate results, including
  the declared strict or relaxed mode and their source bindings;
- cumulative usage, the study/run/attempt identities, and the recorder's
  completion timestamp under the run's clock contract.

Publish that receipt atomically before the hard deadline. Partial capture,
chat-only approval, mismatched evidence, or a receipt published after the
deadline cannot qualify. A capture failure leaves the previous complete
checkpoint eligible and preserves incomplete work separately. Independent
evaluation may later find faults in the selected checkpoint; those are findings,
not grounds to replace it with an earlier, better-scoring output.

The implementer's follow-up archive commit is not an eligibility prerequisite:
the receipt already preserves the actual review and its reviewed source. If
archival is unfinished at the limit, record it as pending and do not grant time
to complete it. Post-stop copying, hashing, or packaging may only preserve
already-frozen evidence; it cannot create missing approval, run missing gates
on the run's budget, or backdate eligibility. Independent evaluation remains
separately metered.

For target-quality studies, predefine submission opportunities and the full
independent target rubric. Submit only frozen candidates; after a failed
assessment, allow at most the preregistered bare target-not-met signal, never
hidden findings or answers. Record assessment cost separately and apply the
same opportunities to every arm. Runs not attaining the target by the cap are
right-censored for time-to-target reporting, not assigned invented completion
times or omitted. Ordinary pass review can continue within the cap.

Human assistance follows a common policy: permitted logistical actions,
semantic help rules, maximum wait, time accounting, and whether a question can
be answered at all. Record every intervention and its content. Additional
semantic evidence outside the assignment is a protocol deviation, not a quiet
favor. Batch runtime perception questions where useful without hiding their
cost. Authentication and tool approval friction count in the intervention log.

## 6. Controller state and recovery

The state machine is proposed behavior, not an existing launcher interface:

```mermaid
flowchart LR
    A[Draft study] --> B[Frozen and approved]
    B --> C[Isolated run prepared]
    C --> D[Running intake and passes]
    D --> E[Stopping and capturing]
    E --> F[Frozen output]
    F --> G[Blinded evaluation]
    G --> H[Judgments locked]
    H --> I[Unblinded report]
```

Persist controller state atomically with monotonic event sequence numbers.
Use one active controller lease per study and one dispatch owner per run.
Bind every operation to study digest, run ID, attempt ID, expected state, and
worker generation. Duplicate events are idempotent; stale workers cannot
resume a stopped run. Transitions verify required artifacts before publishing
the next state. Recovery never reconstructs success from chat or pane titles.

Track execution outcomes separately from validity and quality:

- Execution: target submitted, budget exhausted, user stopped, blocked awaiting
  input, agent failed, or infrastructure failed.
- Validity: compliant, approved deviation, contaminated, or evidence incomplete.
- Assessment: target met/not met/unassessed plus the quality dimensions.

A needs-input pause keeps the budget ledger and the declared clock policy.
Restarting a session cannot reset allowances. Infrastructure retries follow a
predeclared rule with a fresh attempt ID and retained failed-attempt evidence;
charge all attempts against the approved study ceiling and report retry cost
separately. Do not selectively retry poor semantic outcomes. Resume the same attempt only
when its checkpoint, context-reconstruction policy, and isolation still match.
Record outages and interrupted reviews rather than declaring them approved.
Controller lease recovery also verifies the independent supervisor and original
deadline before dispatch. An expired deadline forbids resuming either role,
even if a pending review notification would otherwise be deliverable.

Do not add a second state machine for individual pass verdicts: consume the
existing handoff protocol. Study-level stop enforcement must also cover
pre-edit pass start and agent dispatch; blocking post-commit `start-pass`
alone would allow an extra pass to be implemented. Do not terminate unrelated
emulators, tmux sessions, or processes during recovery.

## 7. Artifact and provenance contract

Use a private study store outside all run-accessible roots. A proposed layout:

```text
<study-store>/<study-id>/<revision>/
  study.json                 frozen manifest
  approval.json              owner authorization bound to manifest digest
  assets.json                private input inventory and hashes
  allocation.json            planned condition/run mapping; evaluator-hidden
  events.jsonl               controller-owned event journal
  runs/<run-id>/<attempt-id>/
    environment.json
    usage.jsonl
    interventions.jsonl
    checkpoints/<checkpoint-id>/
    final/manifest.json
  evaluation/
    protocol.json
    hidden/                  committed task/sample definitions and references
    blinded/<candidate-id>/
    findings.jsonl
    judgments.json
    unblinding.json
    report.md
```

Commit the private hidden protocol by digest before runs start; keep the
content and mapping inaccessible to run agents. For output-dependent claim
sampling, freeze the sampling algorithm and seed beforehand and record the
resulting population and selections afterward.

Checkpoint manifests bind exact Git history/head/tree, working-tree status,
input and output file hashes, tool identities, current pass/review state,
commands and exit statuses, and cumulative resources. Capture authored asm,
docs, scorecards, inventories, review artifacts, generated evidence needed to
reproduce claims, and references to private runtime captures. Preserve ignored
handoff state, untracked evidence, and unfinished edits too; Git alone does
not retain these. Keep live reference assets outside source history.

Capture available visible prompts, responses, tool interactions, effective
permissions, model settings, context compactions, and approval events. Do not
request or depend on hidden chain-of-thought. Identify missing or truncated
telemetry; a tmux screen snapshot is not a complete transcript. Preflight
rejects capture gaps that violate the study's declared evidence requirements.

Freeze outputs only after stopping writers and verifying hashes. Evaluation
uses disposable copies and independently regenerates required analysis;
historical evidence remains immutable. Preserve original bundles with their
path context rather than rewriting their bindings to fit a relocated copy.
Never turn a cache hit or a claimed green scorecard into a new check result.

## 8. Independent evaluation

### Blinding and evidence access

Create neutral candidate IDs and hold condition/model/cost mappings outside
the evaluator's initial view. First assess each candidate independently in
fresh context, without other candidates' artifacts or judgments,
then compare matched candidates with randomized presentation order. For
pairwise model judging, repeat consequential comparisons with reversed order
under the fixed evaluation budget; disagreements remain visible.

Preserve originals and provide a documented presentation layer for identity
redaction. Do not rename semantic symbols or remove quality-bearing content
to manufacture blindness. Reference-derived vocabulary may reveal a condition;
record such leaks and evaluator guesses. Blinding is a mitigation, not a claim
that the evaluator can never infer the treatment. Use full process logs later
for a separate compliance audit; lock initial quality judgments before opening
identity-bearing history. The owner retains access to every original artifact.

Artifacts are untrusted evidence, not evaluator instructions. Use a fixed
evaluation harness and isolated scratch copies. A run may not replace gates,
alter the rubric, execute arbitrary commands through its report, or direct
the judge to disregard findings. Approve necessary project-local reproduction
scripts through the same bounded execution policy for every candidate.

### Evidence selection and assessment

Use three complementary sources: hidden benchmark questions established
beforehand, stratified samples of equivalent ROM regions/subsystems, and
sampled authored semantic claims. Align subjects through ROM bank/output
offset and mapped CPU range, with RAM ownership and producer/consumer
relationships where relevant. Symbol spelling and label count are not
equivalence keys. Validate alignments and record ambiguous or missing matches.

The [semantic-claims ledger](agent_playbook/QUALITY_REVIEW.md#semantic-claims)
is an index, not ground truth or a complete sampling population. Sparse
ledgers during early passes are normal. Also inspect asm, memory maps, format
docs, comments, and deferred questions. Do not reward omitted difficult claims
or force extra per-pass ledger work just to serve the evaluator.

| Dimension | Required assessment |
|---|---|
| Mechanical integrity | Independently rerun applicable canonical wrappers; record binary identity, raw statuses, strict/relaxed mode, coverage and unrun checks |
| Semantic correctness | Check ownership, action/subject, axes, units, states, boundaries, formats, and reference identities against code and runtime evidence |
| Semantic coverage | Fraction of the predefined or sampled meaningful subjects explained correctly, with explicit population and denominator |
| Uncertainty | Separate confident errors, justified narrow names, explicit unknowns, and unsupported speculation |
| Readability/editability | Anchored inspection and fixed-budget developer tasks on disposable copies |
| Evidence quality | Reproducible claims, valid reference mappings, trace acceptance and limits, contradiction handling |
| Efficiency | Run and evaluation resources reported separately, including rework and human assistance |

For each sampled subject, record supported, contradicted, unresolved,
unaddressed, or not assessable, along with rationale, severity, confidence,
and exact evidence references. An unknown answer key or missing evaluator
capability is not a candidate error. Report assessment coverage and unresolved
adjudication explicitly. Preregister severity and scoring rules; high-impact
confident errors cannot be concealed by many trivial correct aliases.

Manuals establish vocabulary but do not prove its mapping to code. Existing
completed disassemblies are candidate evidence, not unquestioned answer keys.
Require instruction/data-flow or accepted runtime evidence for disputed
implementation semantics. Correct a faulty benchmark by issuing a versioned
evaluation amendment and reassessing all affected candidates, retaining the
original judgments and the reason for correction.

Developer tasks use the same solver configuration, fresh context, task inputs,
resource limits, and semantic acceptance tests across candidates. Examples
include locating an editable table, explaining a state transition, or making
a small verified behavior change. Tests must accept equivalent correct
solutions rather than require one run's names. Evaluation edits never feed
back into the experimental outputs or get committed as project work.

### Adjudication and reporting

Calibrate the evaluator on separate synthetic examples containing known
semantic errors, omissions, and cosmetic differences. Human-check a
preregistered sample of agreements as well as major disagreements. Use an
independent second judgment for decisive contested findings, within the
evaluation budget; preserve unresolved cases if that budget is exhausted.
Do not assume the same model family provides independent error patterns.

Prefer a dimension-by-dimension report with concrete findings. If an aggregate
score is desired, freeze weights and blocker rules before outputs exist.
Report rubric sensitivity separately; never choose weights to favor a result.
Only after judgments are locked reveal the assignment and cost mapping.

### Pilot evaluation profile

`pilot-evaluation-v1` names the reference protocol for the first implementation.
Its counts are bounded pilot defaults, not a statistical power claim. Freeze
the concrete subjects, selection algorithm/seed, severity definitions, evaluator settings,
and separate limits for mechanical checks, semantic review, developer tasks,
comparison, and human adjudication before launching runs. Refuse unresolved
limits. A different sample size or scoring policy requires a named profile
revision before outputs exist.

| Evidence set | Selection and use |
|---|---|
| Eight hidden questions | Author ROM-linked questions and evidence-backed answer criteria before runs; include them in the primary subject set. |
| Sixteen sampled subjects | Select four meaningful subjects from each of control flow, RAM ownership, data formats, and reference identities. Freeze the population and use the committed seed; exclude overlap with the hidden questions. These complete the 24-subject primary set shared by every candidate for that ROM. |
| Up to eight authored claims | Sample candidate assertions from asm and docs using the frozen algorithm; inspect all if fewer exist. Report these separately, with the actual denominator, so omission cannot improve the primary score. |
| Two developer tasks | Locate an editable table and perform one small behavior change on disposable copies, using prewritten acceptance checks and equal per-task limits. Report success and resources separately from semantic coverage. |

If a ROM cannot support those populations or tasks, choose and approve a
revised profile before launch. Do not invent subjects or substitute easier
ones after inspecting candidate outputs.

For each primary subject, assign one status against its frozen answer criteria:

| Status | Meaning |
|---|---|
| Supported | The candidate explains the subject correctly, with supporting evidence. |
| Contradicted | A current candidate claim conflicts with established evidence. |
| Unresolved | The candidate leaves the subject uncertain or only partially explained. |
| Unaddressed | The candidate provides no meaningful account of the subject. |
| Not assessable | The evaluator lacks the evidence, capability, or remaining budget to judge. |

Count explanations carried by names and structure as well as prose. Superseded
historical ledger entries are not current claims.
`supported` earns one unit; `contradicted`, `unresolved`, and `unaddressed`
earn zero, with their counts kept separate. Conflicting claims about the same
subject prevent a supported rating unless the candidate explicitly resolves
them. These units measure sampled correct coverage, not whole-ROM completion.

Keep the common denominator of 24. Report any `not assessable` subjects and
lower/upper assessment bounds: supported/24 through
(supported + not-assessable)/24. These are not statistical confidence intervals.
Do not drop such subjects only for one candidate or convert inability to judge
into a candidate error. Faulty answer
keys require the versioned amendment and reassessment described above.
Missing eligible checkpoints are failures to deliver, with quality unassessed;
reports include their frequency alongside scored outputs and never compare
only successful runs without that qualification.

Report material contradictions separately: these are errors that would
misdirect a gameplay change, such as incorrect ownership or axis identity.
More correct minor subjects cannot cancel them. V1 produces dimensional
comparisons and explicit tradeoffs, without a weighted overall winner.
Human review covers every proposed material contradiction and a seeded 20%
sample of supported ratings, rounded up. Exhausted adjudication budgets leave
dispositions provisional and visible.

Before spending on live project pilots, the evaluator must pass a synthetic
calibration suite with four planted-error pairs (swapped axes, false RAM
ownership, wrong table extents, wrong entity identity), two omission pairs,
four cosmetic-only pairs, and two cases with insufficient answer evidence.
The clean originals have authored answer keys. The harness withholds expected
dispositions from the judge, which receives the normal artifact/evidence
interface. Two fresh calibration runs under the frozen settings must both:

- identify all four planted errors with the relevant evidence, without
  inventing corresponding errors in the clean originals;
- mark the two omitted subjects unaddressed, retaining their denominators;
- preserve semantic statuses and coverage for cosmetic symbol/prose variants;
- leave the two insufficient-evidence cases not assessable.

Record per-case judgments and a human-checked calibration receipt. Failure
blocks live pilots until the evaluator is revised and recalibrated. Success
establishes this limited harness check, not general disassembly expertise;
candidate findings still need evidence and adjudication. Preserve calibration
history, and use separate fixtures for tuning and acceptance.

## 9. Experimental design and interpretation

Block comparisons by ROM revision and randomize or interleave condition order
within each block. Freeze host concurrency and resource allocation; overloaded
parallel runs must not be compared to uncontended runs as model differences.
Record service outages, backend drift, dates, and environment deviations.

Select repetition counts and primary contrasts before execution. One run per
cell is a harness pilot, not evidence of a stable treatment effect. Report
per-run and per-ROM differences, variability, and appropriately qualified
uncertainty. Do not treat correlated labels/claims as additional run samples,
discard budget-exhausted runs, or generalize from one ROM to all games.
Preserve the complete allocation table, including failures and excluded runs
with the preregistered exclusion reason. Separate planned from exploratory
analyses and account for multiple comparisons when making inferential claims.

The first live harness pilot uses one ROM and two conditions: supplied prior
projects available versus withheld, with the same manual and FAQ set available
in both. Hold agent pairing, reasoning, tools, and budget fixed. One fresh run
per condition exercises the machinery; it does not establish a stable effect.

Once that pilot passes its operational checks, a new approved study revision
can extend to the two-by-two design:

| Condition | Supplied prior projects | Manual |
|---|---|---|
| A | Available | Available |
| B | Withheld | Available |
| C | Available | Withheld |
| D | Withheld | Withheld |

This tests both individual effects and whether their combination behaves
differently. Repeat fresh runs once the harness works, then broaden the ROM
blocks. Add model and reasoning factors in a separate planned study rather
than multiplying conditions before evaluation is credible. Use pilot data for
planning variability and budget; do not present it as a preregistered
confirmatory result or reuse its exposed hidden tasks without disclosure.

## 10. Governance and process improvement

Study approval authorizes only its named conditions, run count, resource
ceilings, inputs, and assistance policy. Normal sandbox and tool approvals
remain active. No blanket bypass, publication authority, or unrelated host
access follows from experimental intent. The owner can stop work immediately;
that produces a preserved stopped outcome, not silent deletion.

Freeze tooling, playbooks, prompts, evaluator rules, and permission profiles
for a study revision. An event-driven friction monitor may record observations
but must not patch, rebase, or restart experimental runs automatically.
Necessary changes require an amendment or new revision, reviewed software,
renewed approval for changed scope, and an explicit affected-run policy.
Previously completed outcomes remain attributable to their original version.

Evaluate a process improvement itself as a declared treatment in a subsequent
comparison. Do not tune the process against hidden evaluation findings and
then describe continued work as another independent repetition. Keep a
development/pilot set separate from later confirmation inputs and tasks.

The reporting package includes the protocol, deviations, all allocations and
outcomes, input/tool digests, findings with evidence links, judgments before
and after adjudication, blinding limitations, resource summaries, and analysis
code/version. Publishing any package requires separate owner authorization
and exclusion of private references, credentials, and corpus-specific data
from shared tooling history. Reproduction may require the owner's private
assets; say so instead of claiming a public self-contained benchmark.

## 11. Acceptance criteria and rollout

Implement on tooling branches using synthetic fixtures, following the
[process-change review requirements](agent_playbook/REVIEW_AUDITS.md#process-change-review-sanity-checks).
Record actual checks and mutation results; these are future requirements,
not verification claims about this specification.

Required behaviors:

1. A frozen manifest is sufficient to reconstruct assignments and input
   visibility. Changed assets, unresolved model settings, invalid waivers,
   unsupported budget guarantees, and policy mismatches refuse launch.
2. Isolation tests exercise sibling repositories/Git objects, symlinks, homes,
   caches, process state, network, connectors, and reviewer access. A benign
   sentinel in a withheld source is unreadable; permitted references remain
   usable. Do not rely solely on the agent's promise or absence of an access log.
3. Fresh runs do not inherit prior sessions, analysis caches, or semantic
   output. Intake and pass wrappers still work with each supported profile;
   deliberate exclusions never turn parity or integrity failures into green.
4. Budget/stop tests cover slow metering, active model requests and subprocesses,
   closeout/shutdown reserves, agent death, restarts, duplicate handoffs, and
   exhausted review rounds. Kill the study controller during active work and
   prove the independent supervisor still stops the run by its deadline;
   restart after expiry and prove no pending handoff can resume it. Test loss
   of enforcement and clock uncertainty too. No extra pass or budget reset
   occurs; unrelated work survives.
5. Crash injection around artifact publication preserves the last complete
   checkpoint and unfinished work. Changed heads, missing outputs, altered
   hashes, partial telemetry, and stale workers are diagnosed, never accepted
   as a complete or approved run. An approved source with matching evidence
   and an on-time receipt remains eligible without the later archive commit;
   incomplete, late, or mismatched receipts do not. Post-stop packaging cannot
   change that decision.
6. Evaluation detects synthetic swapped axes, false RAM ownership, incorrect
   table extents, omitted hard cases, and confident wrong identities. Pure
   symbol renames and extra prose do not improve a correctness score. Unknown
   answer keys and unsupported runtime scenarios remain explicitly unassessed.
   The pilot profile's calibration must pass before live pilots; test its
   sample selection, common denominators, status scoring, and failure reporting
   with deterministic synthetic judgments as well as the actual evaluator.
7. Blind presentation preserves semantic evidence; reversed pair order,
   identity leaks, prompt injection in artifacts, judge disagreement, and
   evaluation-budget exhaustion receive recorded dispositions.
8. Reports retain failures and censored runs, distinguish raw gates from
   study compliance, and reproduce allocations, sampled subjects, denominators,
   and aggregates from frozen records. Amendments never overwrite history.

Demonstrate bad-direction proofs in disposable fixtures: remove a visibility
restriction, disable manifest binding, reset a budget on restart, accept a
stale checkpoint, or score only volunteered claims. Each corresponding test
must fail for the intended reason. Exercise ordinary non-experiment launch
and review too, ensuring opt-in study support does not alter production rules.

### V1 implementation boundary

The feasibility milestone selects and names one isolation backend and one
agent-application adapter, with pinned versions and demonstrated capabilities.
V1 supports only that combination; the two run roles remain separate sessions
with independently selected supported models and reasoning settings.

V1 includes serial runs, fixed wall-time budgets, independently enforced
deadlines, approved-checkpoint capture, the pilot evaluation profile, and a
private comparison report. Pre-stage references and runtime assets; deny live
browsing and undeclared network access. The normal pass-review protocol and
production permission rules remain in force except for explicit study profiles.

Defer concurrent run scheduling, additional backends/adapters, hard token or
monetary limits, live-search treatments, and target-quality stopping. Manifests
requesting unsupported features refuse launch; they do not silently downgrade.
The feasibility exit criteria are isolated authentication, sufficient declared
telemetry, deadline enforcement despite controller loss, and capture of a
reviewed checkpoint without contaminating or altering production state.

Roll out in stages: validate manifests and isolation without agents; rehearse
state/capture/evaluation with synthetic outputs; pass evaluator calibration
and resource-accounting checks; run the two-condition pilot; then freeze a
repeated study or the expanded four-condition pilot under a new revision.
Do not claim unattended scientific comparisons until the budget and isolation
backend, evidence capture, and independent evaluation meet these contracts.

### Rough planning estimate

Planning ranges assume one experienced implementer with independent review.
An engineering day is focused implementation/review effort, not an agent pass
or a model-quota estimate. These ranges do not authorize work or spending.

| Deliverable | Estimated engineering effort |
|---|---|
| Spec refinement and feasibility prototype | 2–4 days |
| Useful v1 pilot implementation, including basic evaluation | 10–20 additional days |
| Full system described by this specification, including deferred capabilities | Approximately 6–10 weeks total, including the earlier stages |

Reuse the existing pass-review protocol, verification wrappers, and trace
supervisor. New work covers manifest validation, isolation/authentication,
deadline enforcement, usage and artifact capture, evaluation, reporting, and
recovery tests. Split these into reviewable tooling changes. Isolation and
agent telemetry integration, plus evaluator calibration, are the largest
uncertainties; revise the estimate after the feasibility milestone.

The estimate excludes live experiment runtime and model costs, authoring the
private ROM benchmark/answer keys, and human adjudication of study results.
Those need separate budgets in each study's preview and approval.

## 12. Design references

Blocking and randomized run order apply the experimental-design guidance in
[NIST's randomized block designs](https://www.itl.nist.gov/div898/handbook/pri/section3/pri332.htm).
The proposed judge safeguards respond to documented position, verbosity, and
self-preference biases in
[Judging LLM-as-a-Judge with MT-Bench and Chatbot Arena](https://arxiv.org/abs/2306.05685).
That research does not establish an evaluator's accuracy on disassembly;
the local calibration and evidence requirements above remain necessary.
