# FG-1 launcher and client admission proposal

16 November 2026. **Proposed; implementation and provider calls are not
authorized.** This specializes the accepted [launcher decision](LAUNCHER_DECISION.md)
for the measured [first fresh-game corridor](FRESH_GAME_PASS_SCOPE.md). The
[friction-import retrospective](../retros/2026-11-16-structured-friction-import.md)
records the preceding milestone. Base implementation on master after the
reviewed [PR #196](https://github.com/khansen/nesrev/pull/196) merges.

## Outcome and choice

Provide one opt-in, supervised launch path for **Codex implementer and Claude
reviewer** on the exercised macOS arm64 platform. Deliver recorded tasks and
handoffs through existing adapters, expose authoritative progress and stops,
and preserve evidence for deliberate continuation. The deliverable is an admitted
launcher, not a completed game or unattended library-scale operation.

| Alternative | Effect on the selected pass |
| --- | --- |
| Integrate the existing launcher, adapters and watch protocol | Makes the tested service operations usable together. Recommended next slice. |
| Manually invoke each adapter and transfer handoffs | Can exercise the service, but keeps recurring coordinator work. Retain as a diagnostic fallback, not acceptance. |
| Another ordinary attended pass | Works today but does not test the selected structured process. |
| Generic workflow jobs, runtime workers or broad search first | These remain conditional dependencies, not requirements demonstrated for this corridor. Reopen only if the actual pass needs them. |

RAM judgments, compact evidence, declared inputs and friction import have
offline acceptance. Their live usability remains unproven. The earlier
[measurement](FRESH_GAME_PASS_MEASUREMENT.md#dependency-matrix) still governs
conditional stops for runtime evidence, policy writes or new job requirements.

## Reuse and bounded changes

| Area | Existing implementation and proposed change |
| --- | --- |
| Launcher | Add opt-in structured routing to `agent_review_tmux.py`; retain ordinary behavior. Tmux displays supervised headless output and explicit idle/stopped states. |
| Handoff | Reuse `agent_review.py watch` and its notifier contract. Watch the structured session's `handoff` store, never the main checkout's saved review. No second review-state machine. |
| Per-turn input | Deliver the exact recorded notifier message. Claude already accepts a per-turn prompt. Extend only the Codex message-selection/identity seam needed for same-thread handoffs; retain its tool, sandbox, audit and termination behavior. Name the changed functions at checkpoint. |
| Preparation | Use existing preparation, declared-input assembly and isolated profiles. Record the operator-selected corridor and two analogues as manual setup, not agent discoveries. |
| Admission | Verify actual client/package hashes, explicit model/effort, service code, full tool declarations, complete role inputs and media. Prepare fresh profiles; retain old seals. Re-pin corridor and retained-review declarations and any verdict declaration actually offered. |
| Workspace | Refuse a checkout or ancestor Git repository in either client workspace. Only declared media may be present. Preserve isolated configuration/environment rules; do not inherit main-checkout memory or personal settings. |
| Stops and budgets | Recheck the recorded deadline immediately before each client starts, arm supervision first, and use the shared heavy-run lock. Classify from service state and observed client results, not exit zero. No automatic quota retry, extension or next pass. |
| Closeout/application | Use existing qualified closeout and trusted application, under recorded run authority and current approval. No coordinator content repairs, direct queue edits or automatic push. |

Before freezing declarations, replace the no-repeat addition in both roles with:

> Don't repeat observations from your earlier published candidates, rework
> responses or reports in this pass. Carry forward any from a candidate that
> did not publish.

Keep `LEARNING_CANDIDATE_GUIDANCE` as the shared source. Add the parked regression
that refuses two real Learning Candidates sections; a deliberately loosened
section-count check must fail it. Include an unpublished-candidate scenario in
the instruction audit. Do not change which generations import retains.

## First checkpoint: at two active hours

The driving agent reports these before extending integration:

1. Concrete launch/notify/adapter call graph, watch-store root and exact files
   needing changes. Demonstrate the smallest notifier-to-stub turn, including
   message bytes and recorded result.
2. Inventory of retained clients/packages and applicable evidence. Use the
   decision record's exact retained identities when available. Missing packages
   or changed clients require an explicit admission decision; do not choose the
   latest installation or quietly substitute a model.
3. Literal per-role model/effort choices from accepted profiles, with Opus 5.5
   for Claude, plus complete inputs and tool declarations. Verify identities
   offline; model availability is not established until live admission. No
   default-model fallback.
4. State/result table, shared allowance ownership, guard ordering and recovery
   instructions. Demonstrate unchanged-state return, expired deadline and
   notifier failure with stubs and no client invocation.
5. The smallest sealed live-smoke design and remaining estimate. A need for a
   new scheduler, transaction framework, worker boundary or broad client redesign
   stops the slice for a separate scope decision.

## Offline acceptance

Use focused adapter and launcher tests under the shared lock. Verify preparation
and ancestry refusals, supported pairing only, exact task/message hashes,
session-specific watch routing, no concurrent duplicate turn, recorded steering,
same-thread message selection and authoritative handoff classification.

A normal return without handoff remains visibly unfinished and requires owner
continuation. Deadline, quota, interruption, unfamiliar output and missing
evidence preserve raw records and stop. Extensions are explicit and cannot make
an uncertain prior run successful. Test cleanup with a child process and an
expired deadline that starts no client. Preserve both adapters' enforcement
tests and the public `REVIEW_NOT_READY` route check.

Read each complete assembled role input, including handoff and owner steering.
Historical intake evidence stays labeled and out of the active task; media stay
available on demand. Check workspace ancestors at launch, not just the immediate
contents. No arbitrary reference acquisition is added. Run affected suites after
final changes, required repository checks and CI. Carry forward unchanged pinned
evidence within its limits. Offline stubs do not admit real clients.

## Separately authorized client smoke

Request authorization only after the harness, prompts, pins, expected results,
response/invocation limits and stop procedure are concrete and reviewable.
Propose a 30-minute shared window with per-invocation bounds, zero retries and
login completed before the clock starts. The final request must specify exact
counts and budget records; this planning figure authorizes no usage.

The smallest real path must cover:

- Codex receiving an initial recorded message and a distinct handoff on the
  same thread, using admitted routes and preserving role enforcement.
- Claude receiving the actual notifier message and declared reference media;
  initialization and retained requests establish model/tool/input delivery.
- The reviewer's **independent second layer**: on synthetic protected fixtures,
  disable the PreToolUse hook and require restricted-client behavior to deny
  every protected read while sanctioned facts/media access still works. Record
  the absence of hook enforcement. A model refusal without a tool attempt is
  missing evidence, not confinement proof.
- Authoritative handoff or the deliberately selected typed stop, with raw
  output, usage categories, permission events, deadline behavior and cleanup.

Independent calls may reorder: validate required calls/results and genuine
dependencies, not arbitrary order. Hook-disabled access, an unsupported tool,
missing evidence, drift or failed cleanup stops acceptance. Do not widen access
or repair the fixture mid-run. Failure does not authorize another attempt;
bring the diagnosis and a bounded remedy back to the owner.

## Effort, stops and the actual pass

Proposed implementation/admission estimate: **8–16 active hours, hard bound 16**,
with the two-hour checkpoint, an eight-hour progress report and one implementation
review round plus a bounded correction re-check. This retains the earlier
estimate; it is not a forecast derived from the shorter service slices. Record
work, tests and coordination waits separately. Offline work can start on
approval; live stages require their own authorization and may pause it.

Stop for a new service/runtime requirement, a containment failure, a repeated
failure class after its bounded correction, missing client/admission evidence,
an exhausted allowance, or a subproblem becoming a separate integration project.
Unused time does not authorize retries or weaker acceptance.

After launcher acceptance, the existing **4–8 conditional engineering hours**
for final pass-readiness/integration remain separately scoped. Refresh
preparation from the corrected intake and verify the input/write/lifecycle
matrix. Request the unscripted pass's live window, owner-attention allowance and
usage limits. The owner authorizes that one pass independently; no automatic
pass 2 or maturity target follows.

The live pass must produce substantive corridor work, independent review,
qualified gates, archive, imported observations and local application without
coordinator content edits. Measure prompts, denials, incomplete evidence,
compact-RAM use, review/rework, usage and owner/coordinator actions. A necessary
trace or new policy writer stops for separate scoping. One successful pass does
not establish total game throughput or unattended operation.
