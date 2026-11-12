# Structured-pass pilot and Codex client retrospective

**Period:** 31 October–12 November 2026

**Written:** 12 November 2026

**Repository snapshot:** master `e36aeacc5`, after PR #179

This document consolidates the implementation retrospective, the independent
reviewer's retrospective, and their subsequent corrections discussed with the
owner. Its purpose is to understand the results, costs and contributing
decisions. It is a retrospective with suggested improvements, not a rule
document, implementation plan or authorization to start further work.

## Assessment

The effort produced a useful project result and a reusable, opt-in client. The
route to those results was substantially slower and more dependent on manual
coordination than intended. Local technical progress repeatedly obscured the
cost of the overall approach.

The strongest architectural result was continuity across a client change. A
pass begun by a Claude implementer was completed by Codex, reviewed by Claude,
and closed and applied through the service. Generations, reports, approval
coverage and publication state survived outside either model's conversation.

The pilot establishes feasibility for the exercised configuration. It does not
establish that structured passes save tokens, produce better work, or finish
faster than the ordinary workflow. There was no controlled comparison. The
benefit of durable service state also does not, by itself, establish the value
of every confinement mechanism or admission procedure used around it.

## Results and scope of evidence

- The project pass closed a coherent object-draw format corridor: coordinate
  groups, 71 sprite streams, symbolic attribute operands and a format document.
  Independent external review approved it without required changes. Application
  passed inventory, binary-identity verification, process and documentation
  gates. Project changes remained local.
- [PR #178](https://github.com/khansen/nesrev/pull/178) added bounded review
  batching. On the recorded workload, traversal fell from 1,047 calls at one item
  per page to 66 calls with a requested limit of 40. The sequence of 1,103 change
  records was preserved. Pages could end early at the byte ceiling.
- [PR #179](https://github.com/khansen/nesrev/pull/179) promoted the exercised
  Codex adapter, process helper, tests and fixtures. Those six files were
  byte-identical to the accepted preflight. Documentation recorded the evidence,
  limitations and operational lessons. Both required PR CI jobs passed before
  merge.
- These two late-pilot deliverables built on the service, Step 2A and guide work
  already delivered through PRs #175–177. They did not complete Step 2B, runtime
  confinement or default rollout.

The authenticated Codex preflight exercised CLI 0.167.0 on macOS arm64 with
`gpt-6-astra` at `xhigh`. All 17 phases passed in the final attempt, including
nine denial probes and three compactions followed by successful facts calls.
Role-boundary checks and observed process cleanup passed. The real pass then
used Codex as implementer and the existing Claude reviewer.

This was not a full native preflight of both roles. Reference-media access and
reviewer-side feasibility remain open. Linux CI exercised the repository tests,
not authenticated Linux client execution. Process sampling was not a syscall
trace; the canary observed access through its FIFO; usage reports were lower
bounds where interrupted activity might not have been reported.

The pilot also involved disclosed service, prompt and client transitions. It
does not support an unchanged-configuration, unassisted-pilot claim.

## Effort and elapsed time

| Measure | Recorded observation | Interpretation |
| --- | --- | --- |
| Successful final preflight | 336.7 seconds, or 5 minutes 37 seconds | The final 17-phase campaign was short once the client and proof procedure worked. |
| Post-admission takeover completion | 1,331 seconds, or 22 minutes 11 seconds | Includes the remaining repair, reviewer continuations and closeout; excludes earlier semantic work and preparation. |
| Takeover invocations | Two Codex invocations and two Claude reviewer invocations | The first reviewer invocation returned normally with work unfinished; the second continued it. |
| Review activity | Claude reported 84 dated entries over 12 days, including 31 entries on 9–11 November, 24 of them takeover preparation through completion | These are counts from the reviewer's corrected log breakdown, not an independently recounted measure of active work. |
| Takeover development | Revisions through r14 and five live preflight attempts | Much of the elapsed effort went into client engineering, evidence handling and coordination. |

The initial Claude-based attempt exhausted its wall window without completing
review coverage. Quota waiting consumed much of that window, and the reviewer
faced the impractical one-item paging workload. These were separate constraints;
the record does not support attributing the whole delay to either one.

Approximately three days of client engineering preceded a remaining completion
task of about 22 minutes. That is a useful indication of the detour's cost to
the original pass. It is incomplete accounting for the reusable client produced
along the way. Its future payoff is still unproven and cannot retrospectively
justify continuing the detour without reassessment.

## What worked

**Durable service state supported the handoff.** The replacement implementer
could read the pending report and current generation rather than reconstructing
work from another provider's conversation. Service-owned edits, gates,
publication and review coverage remained authoritative.

**Independent review found consequential defects.** Unreachable facts calls,
surviving descendant processes, incorrect process-identity reconciliation and
an incomplete admission comparison were real problems. Fixing them was
necessary for the operating conditions promised by the pass.

**The observed live stops contained execution.** The failed live attempts
stopped rather than silently accepting unfamiliar or incomplete evidence. This
does not mean every offline version was safe: offline tests exposed cleanup
defects before admission. Nor does it mean all observations were preserved;
r10 lost canary observations, as described below.

**Pins and preserved history made corrections reviewable.** Exact-byte checks
connected accepted client evidence to the promoted implementation. Failed
attempts and sealed records were retained rather than rewritten to make the
history appear cleaner. Restoring identical client binaries avoided substituting
an untested version.

**The final promotion was bounded.** Reusable tooling and accurate documentation
went upstream. Project material and the temporary campaign harness did not.
The last coverage-wording correction clarified what remained untested without
changing the exercised adapter.

## Where the process became inefficient

### Three objectives became one expanding effort

Finishing the pass, establishing a confined Codex client and creating a reusable
workflow became entangled. A correction could advance client engineering while
doing little to shorten the path to finishing the pass. That distinction was
not consistently reflected in decisions about scope and effort.

Switching clients was reasonable when quota pressure made continuation
difficult. The weakness was the absence of an explicit effort estimate and a
reassessment point once that switch became a separate engineering project.
Passing another review round was treated too readily as a reason to continue.

### Early tests encoded assumptions about the client

Configuration flags did not fully describe the model's offered tools. Synthetic
responses used formats that differed from live responses. Process-group
assumptions did not cover all descendants. The tests were useful, but some
initially confirmed the implementation's assumptions rather than the client's
actual behavior.

An earlier small native experiment covering a successful facts call, a forbidden
call, resume and termination could have exposed several of these issues
together. A scripted loopback server remained valuable for controlled tests,
but could not establish every format a subscription-backed provider would emit.

### Reviews examined deltas more reliably than the complete delivered task

The functional prompt required an `approve` probe while the implementer schema
excluded that operation. It also told the implementer to stop on missing
required operations and not to perform reviewer approval. The contradiction
survived several rounds because attention centered on diffs, tests and evidence
records rather than the full instructions received by the model.

This was detectable without inference. Comparing required operations with the
role's declaration and reading the complete prompt would have caught it.
The r14 prompt audit addressed that omission. A separate bridge role check
verified that an implementer-side `approve` request was refused without changing
editor state; that role check and the prompt audit served different purposes.

### Review scope expanded without enough prioritization

Some findings protected essential behavior over long sessions, compaction and
termination. Others were test gaps in correct code or diagnostic improvements.
Treating both categories as launch prerequisites increased the number of rounds.
More test volume and stronger seals did not compensate for the missed prompt
contradiction.

Responsibility was shared across implementation, coordination and review.
Review findings supplied much of the expanding work, while coordination did
not sufficiently challenge whether each addition served the immediate outcome.
The owner's intervention prompted a reassessment that the process should have
prompted earlier. The useful lesson concerns how decisions were made, not which
participant accumulated the most mistakes.

### Safe stops and proof failures were initially conflated

| Live attempt | Observed reason it stopped | What the result established |
| --- | --- | --- |
| r6 | The session recorded bare `exec`; the classifier expected a namespace-qualified spelling. | The call was refused and the client halted; the resolver's format assumption was wrong. |
| r10 | A live compaction item contained an additional metadata key absent from the synthetic fixture. | The unfamiliar checkpoint was rejected. Parsing also failed before canary observations were saved, so that phase had an evidence gap. |
| r11 | The monitor killed the client before refusal output reached the session file. | A strictly correlated router refusal existed in stderr, but the proof rule did not use it. |
| r13 | The model followed the missing-operation stop rule because of the `approve` contradiction. | Permitted facts calls worked, but the requested repair did not complete. This was a prompt defect. |
| r14 | All 17 phases completed successfully. | The final configuration met the reviewed preflight criteria. |

Immediate termination remained appropriate. The acceptance procedure needed to
distinguish a breach from unfamiliar evidence and an inconclusive observation.
A new classification should follow investigation, rather than automatically
widening an allow rule or weakening the required proof.

### Operational dependencies were discovered during the pass

Package upgrades removed the pinned client directories. The initial admission
check found the missing Claude binary and stopped before inference. Review then
found the replaced Codex binaries and the missing comparison with accepted
preflight hashes: `prepare()` recorded whatever binary was present at its path.
The accepted-hash comparison was added afterward.

A local rebase also disconnected the session's pinned base from the active
project history. Application correctly refused until ancestry was restored.
Deadlines expired during review and quota pauses. These were lifecycle
dependencies that had not been adequately accounted for at preparation.

### Experimental scaffolding became the operating workflow

Preparation, admission and campaign scripts under `tmp/` were useful evidence
tools, but accumulated into a separate manual operating path. The existing
review store and `agent_review.py watch --notify` interface already offered
much of the necessary orchestration.

Different client launches were justified by the access boundary. Recreating the
surrounding workflow was less justified. The later investigation found a much
smaller integration point in `agent_review_tmux.py`.

### Delivery friction was not escalated promptly enough

The first PR #179 run remained queued without creating jobs. Repeated status
checks supplied little new information. A manual run proved that both platform
suites passed, but did not satisfy the PR's required-check state. Closing and
reopening the PR finally triggered the required checks, which passed before
merge. The ordinary delivery path deserved the same attention to completion
that the preflight received.

## Suggested improvements for consideration

These suggestions emerged from the retrospective. They are inputs to later
scoping and policy decisions, not new mandatory procedures.

### Make detours visible as decisions

A short decision record before substantial integration work could identify:

- the outcome that would justify the work;
- the expected effort and the uncertainty in that estimate;
- the distinction between finishing the immediate task and building reusable
  infrastructure;
- the point at which the owner would be asked to reconsider the approach.

Three review rounds was suggested as a possible ceiling for the launcher work,
with earlier reassessment if a failure class recurs twice or a detour becomes
its own project. These are proposed triggers, not an approved time budget or an
automatic allowance to use all three rounds. Coordination would own the
checkpoint, and review could raise it earlier.

### Observe the real path early and review the complete inputs

Small experiments with the pinned client could establish the request, tool-call,
hook and process behavior before a large fixture suite is built around it.
Synthetic fixtures could then represent observed behavior while keeping
provider-specific uncertainties explicit.

For the proposed notifier, an early supervised smoke turn per role would test
the actual integration path. Reading each role's complete delivered input—base
prompt, handoff text and owner message—would complement the operation audit.
Successful individual components would not substitute for this combined check.

### Classify outcomes before choosing remedies

| Possible result category | Suggested interpretation |
| --- | --- |
| Completed turn with handoff | The orchestration can follow the service's next-actor state. |
| Normal return without handoff | Show unfinished work and offer explicit owner continuation. |
| Budget or deadline stop | Show the exhausted allowance and distinguish extension from recovery after a failure. |
| Containment breach | Stop execution and investigate the boundary before reuse. |
| Unfamiliar evidence | Stop the current run, preserve observations and determine whether the behavior fits the accepted contract. |
| Inconclusive evidence | Stop without claiming acceptance; decide whether another observation, revised experiment or narrower claim is justified. |

Stopping execution and requiring a code change are different decisions. An
unfamiliar result does not automatically authorize a wider classifier; an
inconclusive result does not automatically authorize a retry or relaxed proof.

### Focus review on promised operating conditions

A useful proposed blocker criterion is whether a defect would break the pass
under its promised conditions or make its evidence untrustworthy. This includes
long sessions, compaction and cleanup, even if the next short probe would pass.
Additional tests for correct code and diagnostic polish could remain visible
without becoming launch prerequisites by default.

### Reuse evidence within its actual scope

Routine launches could reuse accepted evidence through admission checks.
Unchanged client and adapter bytes are necessary but not sufficient: relevant
settings, model configuration, tool declaration and platform also matter.
Expected per-session path changes are different from changes to the access
contract.

A change could receive focused validation of the affected behavior rather than
automatically restarting the full campaign. The proposed per-turn message
change would need its changed functions disclosed, the offline adapter suite
rerun and a focused live smoke check. The old preflight would remain evidence
for the old bytes, with the new validation described separately.

### Reduce environmental fragility and reuse the existing launcher

Keeping accepted binaries available for the life of a pass, coordinating
package upgrades, and avoiding rebases while a live session pins ancestry would
reduce avoidable interruptions. Retaining binaries outside package-manager
version directories was suggested, but remains separate work.

The agreed direction for subsequent scoping is an opt-in structured mode in
the existing launcher: profile preparation and admission, a supervised notifier,
output panes, and explicit continuation and extension controls. The owner
prefers steering between supervised turns. This direction is not an
implementation specification or launch authorization.

## Reconciled follow-ups

The following is a snapshot for later assessment, not a work queue. Historical
friction should be checked against the current implementation before being
treated as an open defect. Statuses refer to master `e36aeacc5`.

| Item | Status at consolidation |
| --- | --- |
| `num_turns` overcharges budgets | Stale claim. Charging uses distinct assistant-message IDs; `num_turns` is diagnostic. |
| No writer for blob dispositions | Stale claim. The typed `blob_rows` route exists. |
| No edit route for `raw_ram_review.csv` | Too broad. Factual refresh exists; authored judgment fields remain intentionally unwritable through that route. |
| Comment-only repair batches refused | Current documentation says they are supported, and a lifecycle test covers them with required closeout operations. No fresh runtime reproduction was performed for this retrospective; a specific remaining failure needs its own evidence. |
| Oversized previews spill outside the workspace | Historical report not revalidated here. Bounded preview mechanisms exist; that alone does not prove every reported client-side behavior is resolved. |
| `REVIEW_NOT_READY` becomes `INTERNAL_SERVICE_ERROR` | Reported and reproduced in review; still open at the snapshot. |
| `FORBIDDEN_PATH` omits the path | Partly addressed. Changed-path refusals name paths; some per-operation refusals do not. |
| No structured writer for the shared project debt plan | Reported as still open in the reviewer's reconciliation. The owner-held follow-up remains separate. |
| Reference media and reviewer-side confinement evidence | Open scope, already distinguished from the accepted Codex implementer evidence. |
| r14 test gaps and performance refinements | Parked; no new failure has promoted them into blockers. |
| Project debt-plan update, visual pose-name deferrals and optional documentation/cosmetic changes | Separate local project follow-ups; none was required for acceptance of the completed pass. |
| Retaining pinned clients outside package-manager directories | Parked operational improvement. |

The broader documentation parking lot also contains transition-policy,
supported-but-impractical-operation and reference-organization observations.
Some documentation findings became stale after promotion: Step 2A status and
the missing Codex-client documentation were corrected. The remaining entries
need reconciliation rather than wholesale adoption as new requirements.

Merged feature branches and the promotion worktree were removed after delivery.
Historical pilot evidence and profiles were retained. Reviewer disposable copies
were authorized for later cleanup; this document does not claim they were all
removed.

## Sources and limits of this account

The timing and outcome figures were checked against retained local preflight,
takeover and application records. Those records remain outside the tracked
documentation and are not reproduced here. The review-entry counts and
approximate three-day engineering duration are attributed to Claude's supplied
retrospective; they are not a complete labor or token accounting.

The account incorporates the owner-relayed independent reviews, both agents'
retrospectives and their subsequent corrections. Existing sealed records were
not edited. No new provider calls or test campaigns were run to write this
document. Code and test references below describe inspection of the current
implementation, not fresh execution of those tests.

- [Codex client evidence and limitations](../structured-pass/CODEX_CLIENT.md#established-evidence-and-limits)
- [Service operations and paging](../structured-pass/README.md)
- [Rollout plan](../structured-pass/ROLLOUT_PLAN.md)
- [Step 2 coverage and remaining scope](../structured-pass/STEP_2_COVERAGE.md)
- [Response accounting](../../scripts/structured_pass/usage_budget.py)
- [Typed artifact and raw-RAM refresh rules](../../scripts/structured_pass/artifact_edits.py)
- [Comment-only and scorecard-only lifecycle tests](../../tests/structured_pass_workflow_test.py)
- [PR #178: review pagination](https://github.com/khansen/nesrev/pull/178)
- [PR #179: opt-in Codex client](https://github.com/khansen/nesrev/pull/179)
- [Successful required PR CI](https://github.com/khansen/nesrev/actions/runs/43254191579)
