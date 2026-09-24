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

The evaluator uses fresh sessions and separately governed resources. Initial
quality assessment receives the blinded evidence view defined in section 8
and the owner's full reference set. Original history and process logs become
available for the compliance audit only after quality judgments are locked.
A human adjudicator resolves consequential disagreements or unsupported
conclusions. Evaluation findings never reach an unfinished experimental run;
the only evaluation-derived signal it may receive is the preregistered bare
target result in section 5. Budget and owner stops remain independent.

The benchmark author must not provide live semantic assistance to run agents.
One owner may author benchmarks and operate the study, but their run-facing
actions are limited to the frozen logistical protocol in section 5. Later
studies allowing semantic help need a separate helper without access to the
hidden tasks, answer keys, or other runs' outputs.

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
| Design | Factors and levels, explicit condition matrix, ROM blocks, fresh repetitions per cell, allocation seed, run order, concurrency and provider-capacity policy, inference/uncertainty method and multiplicity handling |
| Inputs | Exact ROM/container and analyzed-region hashes, private asset IDs, reference/corpus manifests with per-file hashes and contamination audit, per-condition manual/FAQ/guide policy, allowed network and runtime inputs |
| Software | Tooling commit and exported tree digest, controller version, playbook/prompt/template hashes, assembler and generator identities, host/runtime/OCR dependencies |
| Roles | Agent executable/version, requested and resolved model identity, reasoning settings for each role, exposed generation settings, prompt/context/compaction policy |
| Isolation | Backend/version, mount and network policy, fresh-session policy, provider-side feature controls, permitted plugins/connectors, contamination checks |
| Execution | Primary budget, secondary limits, closeout/shutdown reserves, clock and backend lease contract, checkpoint eligibility policy, metering precision, restart/retry and primary-attempt rules, input-event detection bounds, human assistance and permission policy |
| Stopping | Budget and owner stops, local gold/review-exhaustion/input/quota/history-rewrite outcomes, target-quality submission opportunities and permitted feedback, unused-budget reporting |
| Policy | Experiment-only overrides, affected rules/checks, exact permitted deviations, reference-intake consent requirements |
| Evaluation | Rubric/profile version, reference-set digest, hidden task/sample commitment, evaluator identities/settings, calibration receipt, shared subject-assessability and pending-judgment policy, scoring/denominator rules, adjudication policy, shared block-review and per-candidate/phase budgets |
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

Network access is denied except for declared services and resources. Allowing
the model endpoint does not authorize provider-side search/fetch, persistent
account memory, remote execution, or account-level connectors. The adapter
must enforce the declared feature allowlist through request and account
controls, record their effective settings, and test these paths separately
from direct sockets. Prompts asking the agent not to use them are insufficient.
If an application cannot disable or isolate undeclared provider capabilities,
it cannot participate in that isolated study profile.

For reproducible reference/runtime inputs, pre-stage approved snapshots and
replay assets with hashes. An arm studying live search must record retrieved
content, provenance, timing, and network policy; it cannot be described as
having fixed external inputs.

### Treatment definitions

Both run roles receive the assigned reference access unless reviewer access
is a separate factor. The evaluator's richer references remain inaccessible
until run outputs are frozen, and are never copied back to the run.

`prior_art: withheld` means no supplied prior-project corpus, comparison index,
or derived project evidence. It cannot remove knowledge learned during model
training. Shared playbooks and generic tooling remain identical across arms;
report their retained domain knowledge as part of the baseline.

Every `prior_art: available` corpus requires an owner-reviewed contamination
audit before its manifest is frozen, regardless of manual availability. Apply
the audit to source, docs, history, generated listings, and derived artifacts,
not just the starter tree. Exclude the target's existing disassembly, previous
run outputs, sibling revisions/ports, and equivalent target solutions. The
first pilot also excludes same-engine projects that expose the target's
substantial implementation; shared generic NES idioms remain legitimate prior
art. Record lineage and content-similarity evidence, exclusions, and uncertain
matches. Unresolved substantial overlap refuses that corpus for the pilot.
Studying such transfer requires a separately named and approved treatment;
it must not be described as an uncontaminated from-scratch prior-art contrast.

`manual: withheld` must specify FAQ, guide, translation, extracted vocabulary,
and browsing access separately. If the intended question concerns access to
all game-reference knowledge, exclude equivalent sources too. In addition to
the corpus audit above, check every allowed source for copies or derivatives
of withheld references. If reference overlap is intentional, describe the
contrast narrowly as direct manual availability, not absence of that
information. Inventory both source and derived artifacts.

### Explicit policy profiles

The ordinary [prior-project reuse rule](AGENTS.md#prior-project-reuse-gate),
[reference intake gate](agent_playbook/DOCUMENTATION.md#terminology-crosswalk),
and [reference-coverage cycle](REFERENCE_COVERAGE_CYCLE_SPEC.md) remain the
production defaults. A study profile must enumerate each deliberate override,
its justification, affected wrapper behavior, and applicability.

The owner must explicitly approve a no-manual condition after the warning:
the final disassembly's terminology and semantic precision will likely be
lower without a manual. That approval can cover named runs in the frozen
study, avoiding repeated questions. Missing files, an empty folder, approving
this specification, or approving an unrelated study are not waivers. Supplied
FAQs still require processing. Manual-present arms stop if their promised
manual is absent or unreadable; they never silently switch conditions.

Withholding a manual does not disable reference planning or evidence checks.
Record `REFERENCE_SCOPE` at pass selection against the arm's available sources,
including why no reference concept applies when appropriate. Keep the canonical
inventory and crosswalk, processing supplied FAQs and recording the withheld
source and approved limitation without importing its contents. Gold submissions
still require `## Reference Coverage`, linked Sources/Inventory/Mappings/Gaps
evidence at the reviewed head, and the existing `EXPLICIT MANUAL WAIVER` outcome
with its linked user decision. Important unresolved identities remain blockers;
a waiver does not prove a mapping or waive evidence for available sources.

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

Freeze a provider-capacity policy for execution and evaluation. Serial order
must not let an earlier run consume the quota available to a later one. Use
equivalent reserved capacity or verified comparable reset windows, matching
account classes and declared model-specific limits across repetitions. Exclude
unrelated account usage during those windows. Record starting quota, reset
boundaries, rate limits, throttling, and outages. If capacity cannot be
verified, the adapter cannot claim this controlled comparison. Random order
alone does not cure quota carryover. Unexpected quota exhaustion is a recorded
provider-limited outcome; it does not earn a selective retry or silently move
the run into a fresh quota window.

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

A trusted deadline supervisor outside the agents' writable environment fences
dispatch and shuts down owned work independently of the controller and tmux
watchers. It is backed by a backend-enforced expiring sandbox lease, installed
before any agent starts. The isolation backend owns the expiry timer outside
the controller/supervisor processes and their termination group. The lease has
an immutable hard deadline; only the supervisor can renew its shorter liveness
expiry, never beyond that deadline. Freeze renewal intervals and teardown bounds
so expiry plus teardown cannot exceed the hard limit. Agents have no renewal or
deadline-extension capability.

If the supervisor dies, renewal stops and the backend fences and terminates
all run-owned work within the lease bound, even if the controller also dies.
Preserve durable evidence outside the sandbox's lifetime. Loss of a valid lease
forbids redispatch. A backend without independently enforced expiry fails
preflight; an in-process timer or another child of the supervisor is not a
backstop. Detecting overspend afterward is not successful limit enforcement.

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

The receipt must also prove continuous review coverage. Starting at the frozen
starter commit for the first checkpoint, or the previous eligible checkpoint
thereafter, account for every intervening commit through the proposed head.
Each must fall inside a recorded, approved review range or be a verified
archive-only commit. V1 uses linear history and binds the actual ranges and
commit IDs; choosing a later review base cannot hide an intervening change.
At every handoff, capture, and redispatch, require the current head to descend
from each existing boundary: the last recorded handoff head and latest
eligible checkpoint. Before either exists, use the frozen starter. Check
before advancing either boundary. A rewrite that breaks this ancestry stops
v1 as `protocol violation: history rewrite`. Preserve the last eligible
checkpoint and the rewritten tree with that outcome; never silently continue
with an increasingly stale primary output. Include this restriction in run
instructions; v1 has no history-rewrite recovery.

An archive-only exception permits exactly the deterministic review archive
and generated learning-candidate updates produced from that approval by the
pinned tooling. Preserve all archive-generation inputs and check the output
against those inputs, approved artifacts, and parent tree; a path allowlist
or commit title alone is insufficient. Other changes, including gameplay docs
or source bundled with an archive, require review. In a future profile allowing
exhausted-rounds overrides, an override is never an approval receipt; its
changes need an eventual approved range before eligibility. V1 stops at
exhausted rounds. Missing coverage rejects the new checkpoint and preserves
the prior one.

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

### Human interaction and early stops

V1 avoids owner response time as a treatment confound. Pre-stage assets,
authentication, scoped permissions, and explicit intake decisions without
performing agent work on the task. A deterministic adapter acknowledges only
non-authorizing startup prompts already satisfied by those frozen decisions,
using the same response schedule in every arm. It cannot grant a new permission
or invent a manual waiver. An unexpected request for human action fences
dispatch and stops the attempt as `blocked awaiting input` within the frozen
detection/shutdown bound. It does not wait for whichever time the owner happens
to respond. Normal approval controls remain active.

The adapter must expose durable permission-request and assistant-turn-end
events, bound to run, role, and worker generation. Run instructions require
an explicit `needs_input` outcome for questions to the user. At each active
role's turn end, the controller checks that outcome and the recorded handoff
state. Expected handoff waits are normal. A turn ending without a recognized
outcome or handoff stops as `agent failed: unclassified stop`, preserving its
text and counting as an agent outcome for that arm. V1 sends no automatic
continuation prompt. Missing event telemetry instead stops as infrastructure
failed. Pane silence alone cannot identify either productive work or an input
request. Rehearse actual adapter events, including a question displayed in a
pane without the required marker.

For later studies permitting live help, preregister response windows, maximum
wait, allowed content, and time accounting identically across arms. Semantic
helpers must be separate from benchmark authors and see only that arm's allowed
references, without condition/model labels or hidden evaluation material.
Record every intervention and its content, including logistical approvals.
Extra semantic evidence is a protocol deviation. A sole owner who knows the
answer keys may only execute frozen logistical responses or stop the study;
they cannot improvise answers to the run's semantic questions.

Fixed resources means a common ceiling, not guaranteed equal consumption.
In v1, local gold approval stops further passes as `local gold stop`;
independent evaluation still determines quality. `REVIEW_ROUNDS_EXHAUSTED`
stops as `review rounds exhausted`, without a human override or a fresh retry.
Capture the latest eligible checkpoint and keep unfinished work separate.
Report the stop reason and consumed and unused budget for every terminal
outcome in section 6, including protocol violations. Do not describe a
partial-budget outcome as having used the full cap or as independently
attaining the target.

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

- Execution: target submitted, local gold stop, review rounds exhausted,
  budget exhausted, provider limited, user stopped, blocked awaiting input,
  protocol violation, agent failed, or infrastructure failed.
- Validity: compliant, approved deviation, protocol invalid, contaminated,
  or evidence incomplete.
- Assessment: evaluation pending/complete/incomplete, target outcome
  (met/not met/unassessed), and the quality dimensions.

V1 permits recovery of the same attempt, not automatic fresh attempts. Its
first attempt is the primary one even if it fails. Resume only when its state,
context-reconstruction policy, and isolation still match; retain the original
deadline and all charged usage. A terminal outcome in section 5 cannot resume.
For later profiles permitting needs-input pauses, those waits also retain the
declared clock policy; v1 stops instead of pausing for input.

Future profiles allowing fresh infrastructure attempts must freeze eligible
failure classes and retry counts before launch. All attempts share the run's
original deadline and aggregate resource ceilings; a new attempt receives only
the remainder, fresh isolated inputs, and no earlier semantic output. Stop the
old attempt before dispatching another. The last attempt started under that
rule is primary, using its own latest eligible checkpoint; if it has none,
report failure to deliver. Never select the best attempt or silently substitute
an earlier checkpoint from a different attempt. Preserve every attempt and
report retry resources. A separately budgeted rerun is a new allocation under
an approved revision, not a replacement for the failed observation.

Controller recovery verifies the backend lease, supervisor, and original
deadline before dispatch. An expired lease or deadline forbids resuming either
role, even if a pending handoff is deliverable. Record outages and interrupted
reviews rather than declaring them approved.

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
fresh context, without other candidates' artifacts or judgments. Freeze a
seeded candidate order and a common subject order before evaluation, then
compare matched candidates with randomized presentation order. Reserve equal,
non-transferable per-candidate budgets for each assessment/adjudication phase
and fixed pairwise-comparison budgets. Do not consume a shared pool on early
candidates and leave later ones unassessed. Log exhaustion and apply the pilot
profile's pending-judgment and incomplete-evaluation rules to each candidate.
For pairwise model judging, repeat consequential comparisons with reversed
order under the fixed evaluation budget; disagreements remain visible.

Preserve originals and provide a documented presentation layer for identity
redaction. The initial quality view excludes original Git metadata, co-author
lines, role/model attribution in archives, usage records, and process logs.
Retain substantive findings and code evidence under neutral evidence IDs;
keep the original-to-presented mapping outside the judge's access. If tools
need Git, provide a fresh scratch repository without the original history.
Trusted mechanical checks may use the originals and return anonymous results.
Do not rename semantic symbols or remove quality-bearing content to manufacture
blindness. Reference-derived vocabulary may reveal a condition; record such
leaks and evaluator guesses. Blinding is a mitigation, not a claim
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
and exact evidence references. Shared primary subjects use the common
assessability rule below. An unknown answer key or missing evaluator capability
is not a candidate error. Report pending judgments and adjudication separately;
they are unfinished evaluation work, not semantic ratings. Preregister severity
and scoring rules; high-impact confident errors cannot be concealed by many
trivial correct aliases.

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

Record evaluator-family relationships to both run roles in the frozen profile.
For model-comparison studies, an evaluator related to one arm cannot be the
sole judge of the contrast: use a judge outside the compared families or a
balanced judge panel with independent human adjudication of decisive findings.
Apply the same judging protocol to every arm, retain each judge's ratings,
and report sensitivity to judge choice. If that check is unaffordable, label
the comparison exploratory with unresolved self-preference risk. Keeping one
evaluator fixed across arms is necessary but does not establish neutrality.

Prefer a dimension-by-dimension report with concrete findings. If an aggregate
score is desired, freeze weights and blocker rules before outputs exist.
Report rubric sensitivity separately; never choose weights to favor a result.
Only after judgments are locked reveal the assignment and cost mapping.

### Pilot evaluation profile

`pilot-evaluation-v1` names the reference protocol for the first implementation.
Its counts are bounded pilot defaults, not a statistical power claim. Freeze
the concrete subjects, answer criteria, initial shared assessability decisions,
selection algorithm/seed, severity definitions, evaluator settings, and separate
limits for shared block review, mechanical checks, semantic review, developer
tasks, comparison, and human adjudication before launching runs. Refuse
unresolved limits. A different sample size or scoring policy requires a named
profile revision before outputs exist.

| Evidence set | Selection and use |
|---|---|
| Eight hidden questions | Author ROM-linked questions and evidence-backed answer criteria before runs; include them in the primary subject set. |
| Sixteen sampled subjects | Select four meaningful subjects from each of control flow, RAM ownership, data formats, and reference identities. Freeze the population and use the committed seed; exclude overlap with the hidden questions. These complete the 24-subject primary set shared by every candidate for that ROM. |
| Up to eight authored claims | Sample candidate assertions from asm and docs using the frozen algorithm; inspect all if fewer exist. Report these separately, with the actual denominator, so omission cannot improve the primary score. |
| Two developer tasks | Locate an editable table and perform one small behavior change on disposable copies, using prewritten acceptance checks and equal per-task limits. Report success and resources separately from semantic coverage. |

If a ROM cannot support those populations or tasks, choose and approve a
revised profile before launch. Do not invent subjects or substitute easier
ones after inspecting candidate outputs.

Before launching runs or opening any candidate output, record each primary
subject's initial assessability, reason, and evidence/capability basis alongside
its answer criteria in the frozen protocol. If that basis cannot settle the
criteria, mark the subject not assessable for every candidate, including
confident guesses, explicit unknowns, and omissions. Candidate wording cannot
change this decision. Later changes require a versioned amendment identifying
new evidence or capability, with the original decision retained and every
affected candidate reassessed. Relative candidate performance is not a basis
for changing assessability.

Only for assessable subjects, judge each candidate against the answer criteria.
Inspection or adjudication left unfinished by one evaluator's budget exhaustion
is a pending judgment. It does not change subject assessability or become an
unresolved candidate rating. Preserve completed judgments, but withhold final
primary scores, bounds, and comparative conclusions involving that candidate
while required judgments remain pending. Candidate-specific authored claims
are a separate evidence set and never change which primary subjects can be
assessed.

Provisional dispositions elsewhere in this specification mean pending judgments
under this rule. If required judgments remain when their fixed inspection or
adjudication budget is exhausted, close assessment as `evaluation incomplete`,
retain the partial judgments and reasons, and withhold the final primary scores
and comparisons. V1 provides no additional evaluation budget or selective
retry. Report incomplete evaluation as an outcome, without dropping the run.

For completed judgments, use these statuses:

| Status | Meaning |
|---|---|
| Supported | The candidate explains the subject correctly in names, structure, or prose, and the evaluator verifies it against the answer criteria. |
| Contradicted | A current candidate claim conflicts with established evidence. |
| Unresolved | The candidate leaves the subject uncertain or only partially explained. |
| Unaddressed | The candidate provides no meaningful account of the subject. |
| Not assessable | The subject's reference evidence or required evaluator capability is insufficient; the same primary subject receives this status for every candidate. |

Count explanations carried by names and structure as well as prose. A precise
correct name can be supported when the evaluator establishes its meaning from
code/runtime evidence; the candidate need not duplicate that meaning in a
comment. On an assessable subject, a vague or explicitly incomplete account
is unresolved; an assertion contradicted by evidence is contradicted. On a
subject that cannot be settled, retain the common not-assessable status and
record unsupported certainty versus acknowledged uncertainty separately as
evidence quality. Neither earns extra quantitative credit.
Superseded historical ledger entries are not current claims.
`supported` earns one unit; `contradicted`, `unresolved`, and `unaddressed`
earn zero, with their counts kept separate. Conflicting claims about the same
subject prevent a supported rating unless the candidate explicitly resolves
them. These units measure sampled correct coverage, not whole-ROM completion.

Keep the common denominator of 24. For finalized evaluations, report the shared
`not assessable` subjects and lower/upper bounds: supported/24 through
(supported + shared-not-assessable)/24. The latter count is identical across
candidates in the ROM block. These are not statistical confidence intervals;
pending judgments cannot be inserted into either count. Do not drop subjects
only for one candidate or convert inability to judge into a candidate error.
Faulty answer keys require an amendment and reassessment as described above.

Missing eligible checkpoints are failures to deliver, with quality unassessed;
reports include their frequency alongside scored outputs and never compare
only successful runs without that qualification.

Report contradicted/24 as a co-primary observed error rate, including
non-material errors. Report a coverage increase with a higher error rate as a
tradeoff; include incorrect guesses alongside correct coverage. Material
contradictions are errors that would misdirect a gameplay change, such as
incorrect ownership or axis identity; report them separately. More correct
minor subjects cannot cancel them. V1 produces dimensional comparisons and
explicit tradeoffs, without a weighted overall winner.

Human review checks the shared primary-subject assessability decisions once per
ROM block before the protocol freezes, using the shared block-review budget.
Any amendment rechecks its changed decisions before reassessment. Candidate
content cannot replace this evidence/capability check.

For each candidate's assessable primary subjects, human review covers every
proposed material contradiction plus a seeded 20% sample from each remaining
nonempty rating stratum, rounded up separately. Include unresolved and
unaddressed ratings: search for missed explanations under different names or
locations as well as checking over-credit. Apply the same sampling separately
to authored claims, including their not-assessable claims, whose subjects may
differ by candidate. Freeze rules/seeds, retain selected IDs and denominators,
and preserve initial and adjudicated ratings. Budget exhaustion follows the
pending-judgment and evaluation-incomplete rule above; it never permits dropping
a required stratum.

Before spending on live project pilots, the evaluator must pass a synthetic
calibration suite with four planted-error pairs (swapped axes, false RAM
ownership, wrong table extents, wrong entity identity), two omission pairs,
four cosmetic-only pairs, and two subjects with insufficient answer evidence.
For each insufficient-evidence subject, present a confident unsupported guess,
an honest unknown, and an omission as otherwise equivalent candidate variants.
The clean originals have authored answer keys. The harness withholds expected
dispositions from the judge, which receives the normal artifact/evidence
interface. Two fresh calibration runs under the frozen settings, with no
feedback between them, must both:

- identify all four planted errors with the relevant evidence, without
  inventing corresponding errors in the clean originals;
- mark the two omitted subjects unaddressed, retaining their denominators;
- preserve semantic statuses and coverage for cosmetic symbol/prose variants;
- mark each insufficient-evidence subject not assessable for all three
  variants, with identical bounds and observed error rates, while preserving
  their different uncertainty disclosures.

Record per-case judgments and a human-checked calibration receipt. Failure
blocks live pilots until a revised evaluator passes a fresh acceptance set.
Once acceptance outcomes inform a revision to the evaluator, prompt, rubric,
or harness, retire that fixture set to tuning and require a fresh, sealed
acceptance set covering the same error classes and controls.
Renaming the exposed cases is not a fresh set. Freeze the revised configuration
before opening the new set; exhausted fixture or calibration budgets keep live
pilots blocked. Preserve every failed round and fixture lineage. Replaying old
cases is a regression check, not new acceptance evidence. Success establishes
this limited check, not general disassembly expertise; candidate findings still
need evidence and adjudication.

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

Freeze one FAQ/guide set, possibly empty, across all four conditions and record
it explicitly in each condition's manifest. Audit any overlap with the manual;
this design varies direct manual availability, not necessarily all knowledge
the manual contains. Varying FAQ access is a separate factor or study revision.

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
   A prior-art corpus containing the target, a sibling revision, or excluded
   same-engine solution refuses the first pilot even when both arms have a
   manual; clean generic analogues remain usable.
2. Isolation tests exercise sibling repositories/Git objects, symlinks, homes,
   caches, process state, network, connectors, and reviewer access. Also attempt
   provider-side search/fetch and account memory/connector retrieval through
   the allowed model endpoint. A benign sentinel in a withheld source is
   unreadable; permitted references remain usable. Verify effective capability
   controls, not just an agent's promise or absence of an access log.
3. Fresh runs do not inherit prior sessions, analysis caches, or semantic
   output. Intake and pass wrappers still work with each supported profile;
   deliberate exclusions never turn parity or integrity failures into green.
   Manual-withheld fixtures retain `REFERENCE_SCOPE`, processed FAQ evidence,
   and linked gold assessments/waivers; missing or invalid evidence still fails.
4. Budget/stop tests cover slow metering, active requests and subprocesses,
   closeout/shutdown reserves, agent death, restarts, duplicate handoffs, and
   exhausted review rounds. Kill the study controller during active work and
   prove the supervisor still stops the run by its deadline. Kill the supervisor
   alone and then both processes; the backend lease must terminate owned work
   within its bound in both cases. Deny attempts to renew beyond the original
   deadline; reject a backend without independent expiry. Restart after expiry
   and prove no pending handoff can resume. Test clock uncertainty too. No extra
   pass or budget reset occurs; unrelated work survives.
5. Crash injection around artifact publication preserves the last complete
   checkpoint and unfinished work. Changed heads, missing outputs, altered
   hashes, partial telemetry, and stale workers are diagnosed, never accepted
   as a complete or approved run. An approved source with matching evidence
   and an on-time receipt remains eligible without the later archive commit;
   incomplete, late, or mismatched receipts do not. Post-stop packaging cannot
   change that decision. Insert an unreviewed intake commit or source changes
   into an archive commit; either breaks eligibility until an approval covers
   it. Exact generated archive-only commits remain eligible exceptions. Detect
   content tampering even inside permitted paths. Amending or rebasing recorded
   history must stop v1 with the explicit protocol-violation outcome at the
   next handoff, capture, or redispatch; appending reviewed commits still works.
   For future profiles permitting exhausted-rounds overrides, also reject a
   skipped range until a later approval actually covers it. V1 permits no such
   override.
6. Evaluation detects synthetic swapped axes, false RAM ownership, incorrect
   table extents, omitted hard cases, and confident wrong identities. Pure
   symbol renames and extra prose do not improve a correctness score. Unknown
   answer keys and unsupported runtime scenarios remain explicitly unassessed.
   The pilot profile's calibration must pass before live pilots; test its
   sample selection, common denominators, status scoring, and failure reporting
   with deterministic synthetic judgments as well as the actual evaluator.
   Correct name-only explanations can be supported by code evidence; incorrect
   guesses increase the reported error rate. Plant false-negative ratings and
   verify all nonempty strata are sampled per candidate. A feedback-driven
   evaluator revision cannot reuse its exposed acceptance set to qualify.
   Incomplete answer evidence must give a guess, honest unknown, and omission
   the same primary not-assessable subjects and bounds. New verified evidence
   updates every affected candidate through an amendment. Verify that initial
   assessability and its block review predate the runs and any output access;
   an unamended post-output reassignment must fail. Review shared assessability
   once per block, never as a candidate rating. Inspection timeouts leave
   pending judgments; exhausting the fixed judgment budget records evaluation
   incomplete with no finalized primary comparison and no change to the common
   not-assessable count.
7. Blind presentation preserves semantic evidence; reversed pair order,
   identity leaks, prompt injection in artifacts, judge disagreement, and
   evaluation-budget exhaustion receive recorded dispositions.
   Check Git/co-author and archive metadata redaction, seeded assessment order,
   and reserved per-candidate budgets. Model comparisons must enforce the
   declared self-preference check or carry the explicit exploratory limitation.
8. Reports retain failures and censored runs, distinguish raw gates from
   study compliance, and reproduce allocations, sampled subjects, denominators,
   and aggregates from frozen records. Amendments never overwrite history.
9. Startup acknowledgements use only frozen authorizations and do not depend
   on owner latency; unexpected input, local gold, review exhaustion, and quota
   stops preserve explicit outcomes and unused budgets. A depleted shared quota
   refuses the next controlled launch. Same-attempt recovery keeps the original
   deadline; v1 refuses fresh retries. Future retry profiles must demonstrate
   the original aggregate cap and deterministic primary-attempt selection.
   Hidden answer keys never enter logistical responses or helper context.
   Inject mid-pass permission requests, explicit input outcomes, unmarked
   questions at turn end, and event-channel loss. Recognized input requests
   stop as blocked awaiting input; unclassified turn ends count as agent failed;
   lost telemetry counts as infrastructure failed. Each stops within the
   declared bound, without a v1 continuation prompt. Expected handoff waits
   must not trigger failures, and agent stops remain in arm failure counts.

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

V1 includes serial runs, fixed wall-time budgets, backend-enforced sandbox
leases, approved-checkpoint capture with continuous review coverage, the pilot
evaluation profile, and a private comparison report. Pre-stage references and
runtime assets; deny live browsing and undeclared network access. The normal
pass-review protocol and production permission rules remain in force except
for explicit study profiles.

Defer concurrent run scheduling, additional backends/adapters, hard token or
monetary limits, live-search treatments, fresh infrastructure retries, live
semantic assistance, and target-quality stopping. Manifests requesting
unsupported features refuse launch; they do not silently downgrade.
The feasibility exit criteria are isolated authentication and provider features,
verifiable quota capacity, sufficient declared telemetry, lease enforcement
despite controller and supervisor loss, bounded input-event detection, and
capture of a continuously reviewed checkpoint without altering production
state. Also complete a rehearsal on synthetic project material using the actual
agent adapter, backend, and scoped permissions: intake, an ordinary pass,
review-requested changes, approval, archive, and another pass. It must complete
without unexpected startup or mid-pass prompts. Fix rehearsal failures and
repeat before the live pilot; no blanket permission bypass follows from them.
An unsupported capability blocks that adapter/backend combination.

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

Reuse the existing pass-review protocol, verification wrappers, and supervised
FCEUX runner. New work covers manifest validation, isolation/authentication,
deadline enforcement, usage and artifact capture, evaluation, reporting, and
recovery tests. Split these into reviewable tooling changes. Isolation and
agent telemetry integration, plus evaluator calibration, are the largest
uncertainties. These ranges assume a backend can enforce independent lease
expiry and an adapter exposes provider-feature and capacity controls. Prove
those during feasibility; otherwise select another combination and reestimate
before building the remaining controller.

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
