# One fresh-game pass: scoping proposal

15 November 2026. Status: proposed after the accepted
[early-pass admission milestone](EARLY_PASS_ADMISSION_IMPLEMENTATION.md) and its
[retrospective](../retros/2026-11-15-structured-early-pass-admission.md).
Tooling baseline: master `65704d7b0`. This document authorizes neither
implementation, intake nor provider calls.

## Outcome and concrete case

Demonstrate **one complete first semantic pass on a genuinely unstarted game**,
from an explicitly accepted intake baseline through independent structured
review, qualified closeout, retained evidence and application. Both roles use
the service and admitted reference inputs throughout. The result is evidence
that the process works on an unfamiliar input, not progress toward finishing
a validation game. The [manifesto](../MANIFESTO.md) governs the choice.

The proposed acceptance case is **FG-1, pass 1: a parity-preserving frame-service
and controller-input infrastructure corridor**. Its named game and selection
rationale are recorded in `CASE.json` in private packet
`fresh-game-pass-scope-20261115`; identities and supplied paths stay outside
master. The game has no project tree or registered reference-intake record in
the inspected checkout. The owner has not yet confirmed the selection or supplied
a pinned input set for this milestone. ROM identity, header validation, reference
hashes, intake commit and exact corridor anchor remain pending. This is a
concrete proposed case, not an admitted or launched one.

After intake, use native evidence to confirm one connected ownership corridor
and record its actual target, producers, consumers, reference scope and exclusions.
Do not assume the new game shares the trial's implementation. If frame service
and input are not one coherent corridor, return the proposed boundary to the
owner rather than force the architecture or select an easier task silently.
Follow the existing [first-pass architecture guidance](../../agent_playbook/NEW_PROJECT.md#first-three-pass-architecture).

The retained trial's first semantic pass is the dependency witness and a possible
offline rehearsal. It is **not** the acceptance game: reusing it would be cheaper
but would not test an unfamiliar input. Any such substitution needs an explicit
decision and a narrower claim. Possible model-training exposure remains unknown
even for a locally unstarted game.

## Entry and completion boundaries

Start with owner-authorized use of the existing
[intake workflow](../../agent_playbook/NEW_PROJECT.md#starting-a-new-project),
including recovery discovery, curated warnings, reference processing and the
intake/reference commits and review. `make project-intake` alone does not
complete those obligations. Record its operator time and failures separately;
do not hide coordinator semantic work in “setup.” No intake service is selected
by this proposal, and no project is scaffolded during this scoping work.

The structured segment begins at that frozen accepted baseline. Preparation
and its selected corridor are explicit trusted setup; autonomous pass selection
is not established by this first case. Completion requires a meaningful corridor
change, all required current-artifact updates, complete independent review,
resolution or explicit disposition of findings, successful closeout/application,
and readable retained evidence. A canned rename, a scorecard-only transaction,
green gates without semantic review, or coordinator shell repair during the pass
does not satisfy it. No pass 2 follows automatically.

## What the retained first pass establishes

The private selection pins the two segment-3 transcripts and archived pass-1
review. It includes C3-010 through C3-045 and R3-092 through R3-130, plus the
pass-1 archive portion of mixed call C3-046. The latter's next-pass request is
outside this case. These are 75 in-pass native requests and one mixed boundary
request, **not** a service-call forecast or coverage percentage. Earlier reference
reads from pass 0 were available to that reviewer; a fresh reviewer cannot be
credited with that context without delivering it.

The accepted review describes a static frame/input corridor and explicitly
skips captures because it makes no runtime claim. It nevertheless needed reads
of supplied references, broad comparison with prior projects, RAM judgments,
policy updates and a learning-candidate archive. Representative witnesses:

| Obligation | Retained evidence | Consequence for this proposal |
| --- | --- | --- |
| Select and record the corridor | C3-011 and C3-018 | Next-pass evidence and pass-start inputs must reach preparation. |
| Reference and analogue evidence | C3-014–016; R3-112–118 | Text, media, architecture guidance and comparison context are real dependencies. |
| Source and current docs | C3-024–028; R3-097–110 | Reuse typed edits and review pages; register every required document. |
| RAM judgments | C3-030 and R3-118 | Factual refresh alone cannot record the author's dispositions. |
| KPI and hardware-policy updates | C3-032, C3-035–036 | Candidate closure may require D6/D7, even for a static pass. |
| Independent checks and archive | R3-119–130; C3-045 and part of C3-046 | Retain the verdict, evidence and learning candidate through closeout. |

The source reads and semantic review are evidence of required *facts*, not a
requirement to reproduce shell spellings. For example, R3-122's custom ROM/object
comparison can potentially use complete generation-bound parity evidence. That
substitution must preserve the actual claim; it does not establish a general
authored-computation capability.

## Dependency decisions

“Needed” identifies an obligation, not necessarily new code. “Unknown” remains
a launch blocker until the chosen input resolves it. The historical witness
does not prove that the new game needs exactly the same operations.

| Component | Need for FG-1 | Existing support, gap and cheap next measurement |
| --- | --- | --- |
| Early-pass admission | Needed; delivered offline | [Policy and acceptance](EARLY_PASS_ADMISSION_IMPLEMENTATION.md) cover incomplete naming without waiving other checks. Run full preparation on FG-1; a different failure is a finding, not permission for another exception. |
| Workflow jobs: selection/start, gates and closeout | Needed; existing preparation subset | [`prepare.py`](../../scripts/structured_pass/prepare.py) already runs next-pass and pass-start for an operator-supplied selection; validation and closeout already run gates. For this one frozen corridor, do not automatically build the whole W1 job catalog. Confirm all generated facts requested by both roles are readable. |
| Additional standalone workflow jobs | Unknown | The historical reviewer skipped regeneration and hidden-code scans because recovery controls did not change. If FG-1 needs either, or needs findings unavailable in existing gate evidence, record the exact W1 job and paged output required. |
| Worker and runtime integration | Unknown; absent from the historical static outcome | No capture was needed for the retained pass. Media reads and parity corroboration are not emulator execution. Verify FG-1's evidence obligations after intake. A necessary trace, new decoder or authored analyzer stops this static proposal for a W2 decision; do not defer required evidence to manufacture success. The [feasibility result](FEASIBILITY_DECISION.md) is not service integration. |
| Guidance, references and analogues | Needed; partly available | [`guidance.py`](../../scripts/structured_pass/guidance.py) admits eight files, not the first-pass intake playbook. [`analogue_inputs.py`](../../scripts/structured_pass/analogue_inputs.py) pins at most two models with selected views, not corpus discovery or analogue documents. Inventory the actual required excerpts, source views and references, and prove delivery to each role. The historical review inspected at least three analogue sources. |
| Candidate writes | Needed; incomplete | Source edits, registered Markdown, rename ledger, scorecard and selected artifact rows exist. D3 RAM judgments, D6 measured KPI updates and D7 policy changes do not. Root-document and friction writes also need their proper authority. Enumerate FG-1's required write paths/fields before estimating; see below. |
| Search volume | Needed; partial practicality | The four admitted questions take 14, 9, 11 and 20 requests. Keep the eight-request criterion and 24 KiB ceiling. Measure the actual corridor's questions separately, with independent complete results. Any required overflow needs a bounded design decision before launch. |
| Structured launcher and client admission | Needed; not integrated | Use the [accepted launcher scope](LAUNCHER_DECISION.md), including per-turn messages, handoffs, continuation, public errors, deadlines and cleanup. Refresh admission for changed client/adapter bytes and test the reviewer's hook-disabled layer in the next authorized client smoke. |
| New intake service | Not needed for the proposed boundary | Owner-authorized existing intake is an explicit prerequisite. This does not demonstrate structured intake or remove its cost from the broader process. |

Candidate-write measurement must distinguish ordinary document registration
from missing writers. `MANUAL_TERMS.md` can be explicitly registered under
`docs/`; root `README.md` cannot be admitted by the current
[registry](../../scripts/structured_pass/ownership.py). The
[raw-RAM refresh](../../scripts/structured_pass/artifact_edits.py) deliberately
protects judgment columns. KPI files, allowlists and friction receipts have
separate owners; none is an unrestricted Markdown/CSV escape hatch.

If D7 is required, its [accepted contract](STEP_2_COVERAGE.md#documents-ledgers-and-trusted-writes)
includes gate/schema migration and reviewed legacy dispositions. It is not a
small text-file writer. Stop and price that dependency explicitly; do not change
names solely to evade a policy check, silently skip mandatory updates, or have
the coordinator make semantic edits outside the service.

Reference delivery also differs by role. The
[Codex adapter](CODEX_CLIENT.md#preparation) accepts pinned PNGs; PDF preparation
is separate. The reviewer feasibility smoke exercised PDF/PNG reads. Declare
the conversion/extraction and page identities, retain originals, and verify both
roles receive the necessary content. Text search does not implicitly admit an
extract, and a shared conversation is not a reference-delivery mechanism.

## Measure before estimating

This scoping pass is limited to **two active hours**, offline, using retained
evidence and code. It does not start intake, a service session, a capture or a
provider-backed client. Record actual effort. It ends with this dependency
assessment; the missing FG-1 inputs prevent a pass-specific implementation
estimate now. The old 80–176-hour subtotal is historical context, not the price
of this case.

Once the owner selects the game and authorizes ordinary intake, prepare a
separate bounded measurement packet before any integration estimate:

1. Pin ROM/reference hashes, parsed header, accepted intake commit, current
   tooling and actual first-pass corridor. Run full preparation in a disposable
   copy; include generated-only and native-certification checks. Tag failures
   as input/early-source properties, tooling/artifact drift, or environment/pins.
2. Inventory the corridor's evidence and write obligations against the table.
   Name the required W1 results, D3/D6/D7 fields, document registrations,
   reference pages/extracts and analogue inputs. Mark unsupported operations
   explicitly. Inspect both roles' complete prospective inputs.
3. Translate the actual search questions and count complete service requests,
   including selection/context. Compare with an independent native-fact oracle;
   no-match, unresolved operands and truncation remain distinct. Carry forward
   the four known overflow results as regression obligations, not as measurements
   on FG-1. Compare compact matches with selectively fetched context against
   grouped summaries only if needed; no redesign is authorized here.
4. Return a needed/not-needed/unknown matrix, ordered implementation slices,
   estimates and acceptance for each, plus the total and its uncertainty.
   Estimate from the measured dependencies, not from assuming all of 2B/2C is
   required or from optimistic reuse of the earlier subtotal.

Proposed allowance for that **post-intake offline measurement**: at most two
active hours, separately accepted with its inputs. Stop at the bound, on any
new capability dependency, failed preparation check, missing required evidence,
or an operation that would require widening authority. Preserve the observation
and return for a decision; no repairs or automatic extension. Known unsupported
rows are inventory items, not permission to implement them. The driving agent
owns the checkpoint, the reviewer may raise it, and the owner decides.

## Alternatives and order

| Choice | Benefit | Cost or limit |
| --- | --- | --- |
| Measure FG-1's complete contract, then build its missing slices | Tests generality and keeps every component tied to an accepted pass outcome. Recommended. | Requires supplied inputs and honest intake first; implementation estimate remains pending. |
| Launcher first | Makes an existing static structured loop usable sooner; accepted estimate is 8–16 active hours. | Does not supply the known missing candidate writes or input views. A live pass would stop on those gaps. Keep launcher work in the dependency path, not as a substitute for it. |
| Rehearse the retained first pass | Cheap, pinned evidence and known semantics for offline controls. | Useful as a proxy only; does not meet unfamiliar-game acceptance. |
| Build general workflow jobs or runtime first | Adds reusable capabilities and supports broader later passes. | Existing preparation may suffice for this static case; runtime was not required by its witness. Select only when the measured obligation warrants it. |
| Attended ordinary pass | Can perform the full work today. | Retains the measured supervision/permission problem; does not test the structured boundary. |

The leading known gap is **candidate closure and evidence access**, subject to
the fresh input measurement. No implementation order or total is approved by
this ranking. Per-session worktrees, article handling, parallel games, more
mappers and automatic quota recovery remain separate process capabilities.

## Live acceptance and limits

Before a later live request, every needed row must have offline evidence or an
explicitly declared existing route. Unknown does not count as covered. Pin the
approved client/model/effort configuration, including the owner's Claude Opus
5.5 preference, assembled prompts and actual inputs. Arm the guard before
launch and check the deadline immediately before starting clients. Runtime,
token/provider and owner-time allowances are new owner decisions.

Run one unscripted implementer/reviewer pair through the launcher. Record
completed evidence obligations, all prompts/denials and missing evidence,
coordinator and owner actions, review/rework, per-role usage, elapsed/active
time, stop classification and cleanup. Zero prompts with missing evidence is
failure. A real reviewer must choose usable service routes; a scripted replay
alone cannot establish that. Report normal rework separately from a capability
stop. Finish the approved pass and stop; do not chase maturity or consume unused
budget on another pass.

If this remains a static corridor, runtime and emulator integration remain
unproven. Owner-run intake, a fixed initial selection, declared comparison
inputs and one platform limit the claim. Automatic recovery, concurrency,
other mappers and comparative cost savings require their own evidence. The
deliverable is an accepted pass plus an honest process report recommending one
next improvement, or a preserved stop identifying the dependency that prevented
that outcome.
