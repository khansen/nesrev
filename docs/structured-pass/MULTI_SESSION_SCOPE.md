# Multi-session structured corridor: design scope

Status: the owner authorized the narrower implementation below, with a 24-hour
hard stop, checkpoints at 2 and 8 hours, and at most 10 credential-free loopback
invocations. Provider calls and a live pass remain unauthorized. The tooling
prerequisite, [PR #201](https://github.com/khansen/nesrev/pull/201), is merged.
The owner-approved [measured-format policy](MULTI_SESSION_RATE_POLICY.md)
governs capacity. The margin and reserves remain unchanged.
The [first implementation checkpoint](MULTI_SESSION_CHECKPOINT.md) records an
editor-price refusal and the components completed before integration stopped.
The owner subsequently authorized one native lean-edit projection and one reprice,
with the same edit envelope, startup, caps, reserves and margin. Its
[measured result](MULTI_SESSION_LEAN_EDIT.md) passes, so the narrower build may
continue toward the 8-hour checkpoint. No live attempt is authorized.
The [early integration checkpoint](MULTI_SESSION_INTEGRATION_CHECKPOINT.md)
records the native fresh-editor proof, complete assignment costs and the
remaining launcher work.
The [sequential launcher](MULTI_SESSION_EXECUTION.md) now binds phase profiles,
capacity reports, one-use invocation slots and finished-checkpoint recovery.
Its complete native recipe remains an acceptance requirement.

The [native checkpoint](MULTI_SESSION_NATIVE_CHECKPOINT.md) records the completed
eight-turn sequence and the write-rule stop before application. All ten
authorized native invocations are used; no replacement is authorized.

## Authorized first build

Build investigation partitions by whole roots or RAM ranges against one frozen
source, followed by one editing context using the existing edit, review, rework
and closeout steps. Keep the plan length data-driven. Defer subdividing a single
root or byte, renewing evidence after publication, and continuing editing or
review in a new context. The wider design below records those possibilities;
it does not authorize their implementation now.

The 2-hour checkpoint is a **go/no-go on the editor's complete price**: maximum
handoffs, decisive re-reads and full records/preimages for its edit envelope,
with the current rates, 48K lifecycle reserve and at least 10% margin. If that
does not fit one context, stop for a scope decision before launcher integration.
Do not silently reduce the corridor or reclaim the reserve. A passing price
keeps the deferred features deferred and supports a revised effort estimate.

## Outcome and decision

The outcome is one coherent corridor improved through structured operations,
independently reviewed, verified for ROM parity and applied with its required
documentation. Session count is an execution detail, not the pass outcome.

The [whole-corridor measurement](CORRIDOR_EVIDENCE.md) reduced investigation
responses from 1.32 MB to 200 KB, but the corrected estimate still misses the
required context margin by 3,307 tokens. Further tuning of that one-session
estimate is stopped. A larger corridor must not depend on fitting startup,
complete investigation, edits and closeout into one model context.

Use bounded, fresh model contexts linked by service-validated investigation
handoffs. This is controlled information transfer: a prose summary or the
client's automatic compaction is not an accepted checkpoint. Alternatives were
continuing through the ordinary workflow or adjusting the pricing rule again.
The owner selected this design to make the structured route reusable across
corridor sizes; the ordinary workflow remains an alternative if the added
coordination cannot be kept proportionate.

## Plan and partitions

Preparation freezes one corridor inventory and its native source/model/facts
identities. It constructs a finite, ordered session plan whose length is data,
not a hard-coded investigation/editing pair. Each entry declares its phase,
assigned coverage units, predecessor handoffs, source-generation binding, startup input
selection, capacity report and invocation allowance. Run entries sequentially
under the existing turn lock and supervision. There is no parallel worker pool
or general-purpose scheduling service in this slice.

Before edits, the binding is the exact frozen generation. A declared successor
entry may instead require the generation returned by a particular authorized
publication; its actual identity and renewed capacity report are recorded and
verified before invocation. It cannot select an arbitrary current checkout.

Investigation partitions follow roots or explicit RAM-address ranges. Source
blocks, helper interfaces, analogue routines, direct accesses and shared
indexed/indirect facts are all obligations from the parent inventory. A shared
fact has one identity and explicit byte membership; partitions cannot lose its
other members or turn a possible access into proof. Overlap is permitted and
declared. The union must cover the parent inventory, without substituting a
cheap scripted reading path for the complete workload.

An oversized partition can be subdivided again using the same format. Bounded
record/fact subsets may divide a large root or one byte's evidence; the parent
root or byte remains incomplete until all of its required subsets are covered.
This prevents an arbitrary leaf size from becoming an implicit session limit.
The plan schema supports any finite number of entries, while each grant names
the actual entries and finite ceilings. It never authorizes unlimited sessions.

Preparation records a coverage table mapping every obligation to its assigned
entries. The service checks the union and overlaps before launch and again
before editing. New essential evidence outside the inventory, or a partition
that still cannot fit after subdivision, stops for a scope decision. The model
cannot silently enlarge the corridor or mint a new funded session.

## Checkable handoff

Introduce one versioned, service-owned handoff format for every partition and
phase. It is separate from a project candidate, a quality verdict and pass
closeout. Investigation never publishes a fake candidate to save notes.

| Field group | Required meaning |
| --- | --- |
| Identity | Plan, pass, session and partition IDs; phase; parent handoff hashes; schema and tool versions |
| Evidence binding | Generation, source hash, native model/capture identity, facts-manifest hash and declared-input hashes |
| Coverage | Assigned, completed and remaining record/fact units; source blocks and byte memberships; service read receipts |
| Claims | Stable claim ID, statement, subject, confidence, supporting citations, contrary evidence and unresolved conditions |
| Decisions | Proposed names/edits or explicit deferrals, linked to claims; cross-partition dependencies and conflicts |
| Completion | `partial` or `complete` for the assigned partition; no inferred completion of the whole corridor |
| Integrity | Canonical payload hash, predecessor links and service acceptance receipt |

Native record IDs identify source statements. RAM facts need an unambiguous
identity beyond the instruction ID: a site can produce several categories,
pointer parts or byte memberships. Derive fact IDs from canonical full facts
and their evidence kind, bound to the native capture and the facts manifest.
Transport dictionaries, page offsets and array ordering are not fact identity.
The canonicalization includes certainty, alias proof and address membership;
changing any of them changes the cited fact. The source/model remains the
authority, following Tooling Rule One; no text parser is introduced.
Compute these identities for the parent inventory before partitioning, not
from each query's selected byte subset. Coverage tracks the required
fact-ID/address memberships, so sharing a fact does not implicitly complete
an unassigned byte's investigation.

Each citation names its evidence artifact, generation, record or fact ID and
content hash. Input-derived claims cite a fixed input ID, its capture hash and
the relevant bounded span. Negative claims such as an absent writer also cite
the complete searched set and its coverage receipt; one positive record cannot
prove absence. Free-text explanations are allowed, but every semantic claim
must have citations or be marked unknown with the missing evidence identified.

The worker submits a typed checkpoint through the facts service. Dispatch
checks its schema, source binding, citation resolution and assigned coverage;
the server fills identities and completion evidence rather than trusting agent
booleans. Read receipts establish which pages were delivered, not that the
model understood them. Acceptance checks structural integrity and coverage,
not semantic truth. Proposed names remain proposals until locally revalidated
and independently reviewed.

**Compaction voids earlier coverage.** Only pages actually delivered after that
session's last native compaction count. A call or page retained in replacement
history is not a new delivery. Check the final native audit at every handoff
and at the start of every consumer session. A compaction after checkpoint
submission invalidates its coverage; the investigator must re-read and submit
a new checkpoint within its existing allowance. Ordinary later calls that do
not compact the session do not invalidate an accepted checkpoint.

Generate the checkpoint argument shapes and identity sources from dispatch's
own tables, delivered through the paged operation reference. Show declaration
sizes and captures at admission; do not hide required fields or source mappings
in a coordinator-authored prompt.

Store accepted checkpoints as immutable, hashed captures using the existing
locking, atomic-write and retention machinery. A successor replaces its own
partition's authoritative pointer only after complete validation. An interrupted
write leaves the last accepted checkpoint or nothing; drafts cannot appear in
the completed catalog. A refusal cannot erase earlier accepted work.

## Session transitions and recovery

At the start of **every** consumer session, including editing, a service check
resolves all incoming citations against the pinned source and facts, checks
every parent hash and compares coverage with the plan. The model must receive
the resulting receipt before beginning its task. A changed source, fact,
generation or missing capture refuses that transition. The operation performs
the full check even when its response is a compact receipt.

Accepted handoffs are exposed through fixed-ID, paginated input records. A
paged index lists predecessor IDs and hashes; only the declared dependency set
is loaded. An arbitrarily long history must not become an arbitrarily large
startup prompt or exceed the existing catalog/item limits. Every fetched page
is charged. Handoff assembly is a deterministic, pinned service operation;
the coordinator does not summarize evidence by hand between sessions.

The investigation profile uses the existing implementer identity with a
read-only phase capability set. It can read evidence and submit checkpoints;
preview, confirm, validate, publish and application are refused in that phase.
The service enforces this boundary independently of the prompt or tool help.
The editing profile retains the ordinary candidate operations, and the
independent reviewer retains its verdict authority. Phase declarations and
native pins must be captured and reviewed; changed listings are not called
the previously admitted declaration.

The editor reads the handoff claims, uncertainties and verified coverage. It
fetches decisive local evidence for every proposed semantic change and full
records/preimages for the records it will edit. Hash validity alone does not
justify a name. Those reads and the handoff itself are in its capacity report.
Independent review checks the implementation and its evidence; an investigation
checkpoint is never a substitute for a review verdict.

The same handoff envelope also carries bounded editing/review continuations,
including current candidate/revision or review-ticket identities where needed.
Ordinary preview, validation, publication, review coverage and closeout rules
remain authoritative. A fresh context does not reset a candidate, approval
requirement, completed turn or retry allowance.

Publication changes the source generation. Earlier handoffs stay immutable
historical evidence and are not silently rebound. A successor session needs a
new checked handoff against the current generation: regenerate affected native
facts and explicitly reconfirm dependent claims. Unchanged facts may be reused
only after the service proves their full content unchanged and records the
new binding. Changed or ambiguous citations require investigation, not an ID
guess or a replay of an old preimage. If the frozen plan cannot authorize or
price that work, stop before starting another client.

A deliberate bounded stop may leave an accepted `partial` checkpoint listing
the exact completed units and remaining work. The next funded entry can
continue those units. A timeout, crash or malformed submission leaves only the
last accepted checkpoint, or nothing. Neither a successful client exit nor
the existence of a draft means completion. Terminal/integrity failures and
uncertain usage still require recovery; checkpoints preserve useful work but
do not authorize a retry. Conflicting claims block dependent edits until a
planned reconciliation step resolves them or the owner changes the plan.

## Capacity before each session

Extend the current capacity check to validate each partition against its parent
inventory and to price its complete delivered workload. Retain the current
measured format rates and explicit unmeasured-byte policy, at least 10% margin, the 48K
lifecycle reserve, observed unscripted overhead and a full next-response
reservation. **The investigation phase does not reclaim the lifecycle reserve.**

Each session loads only the startup inputs required by its phase and assigned
work. Preparation names those requirements against the playbook routing and
quality contracts, selects verbatim anchored sections, and retains full inputs
on demand. This requires an explicit phase-aware replacement for today's
unconditional startup selection check; it is not permission to omit inconvenient
instructions. Report the selected anchors, source hashes and delivered bytes.
An unmeasured composition must not borrow a favorable measured identity.

Price prompts, declarations, selected startup, handoffs/index pages, citation
validation receipts, decisive re-reads, source/RAM/analogue evidence and request
JSON. Charge shared facts again whenever another context must read them.
Charge editing and review continuations in the same way. Show both per-session
headroom and the total planned input volume, including repeated startup cost.
There is no claim that more sessions are cheaper.

Before a grant, all planned entries must have a passing price. Future handoff
text is not yet known: preparation therefore prices a schema-enforced maximum
handoff payload and its required citation reads, not a guessed short summary.
At runtime, validate the actual handoff/assembled inputs against that cap and
repeat the check before invoking the consumer. Oversize handoffs stop or use
an already priced subdivision; they cannot enlarge the allowance. A rate or
reserve change requires a separate decision made before seeing its result.

## One grant for a finite plan

Propose **one owner grant for the entire sealed session plan**, rather than one
approval per ordinary transition. It pins source/inventory, code, schemas,
phase declarations, input selections, templates, the ordered plan and capacity
reports, plus the reviewed rules for deriving later inputs. Runtime handoff
hashes cannot exist before investigation; they must be accepted service outputs
of those pinned rules, recorded before use. They cannot modify the grant.

The grant specifies a shared absolute deadline, per-invocation time limits,
total and per-phase invocation ceilings, a shared Claude response ceiling,
permitted continuation entries and whether final application is allowed.
Completed and failed invocations consume their slots. Waiting and validation
remain inside the shared deadline. Fresh profiles/contexts do not reset any
shared counter. Capacity limits are not a forecast of total provider usage;
the live grant must separately settle those limits. The current Codex adapter
reports tokens without enforcing a token cap. Preserve and disclose that policy;
adding a token-cap mechanism would need a separate reviewed change, not an
unenforceable promise in the grant.

Only listed transitions may run automatically. A changed corridor or toolchain,
exhausted plan, new subdivision beyond the grant, integrity failure, uncertain
usage or required reauthentication stops. An extension needs a fresh explicit
owner decision. This design does not inherit the previous five-invocation or
four-hour live grant, both of which are spent; the actual proposed live limits
come with the measured plan.

Keep one isolated credential home per provider for the plan and immutable
phase/session configurations outside it. Use each client's native login once
before the window, from the owner's terminal, and native logout after result
review. Do not copy credentials among profiles. Start a fresh native thread
for each planned context; verify its ID and absence of resumed conversation
items. Reusing login state must not deliver earlier transcripts to the model.
If the pinned clients cannot separate login reuse from fresh context/config
selection within their existing boundary, stop at the feasibility checkpoint.

At every transition recheck login status without inference, package and gate
tool hashes, service/source/input identities, predecessor receipts, workspace
ancestry, grant expiry, remaining counters and process cleanup. Never rewrite
an admitted profile in place. Keep the current strict credential/settings,
workspace, session and target write rules; unknown non-credential home changes
remain observations. Derive the new expected changes from the actual launcher
layout, including pre-window status and fresh-context transitions, then test a
valid run passing that check. Application still uses the existing journal,
independent approval and owner-state/preimage checks, once at final closeout.

## Acceptance in one review round

| Requirement | Positive evidence and discriminating refusal |
| --- | --- |
| Variable session count | Partition one neutral inventory into several roots/ranges, including a continued partial partition; union equals the inventory. Omitting a byte, helper, analogue or shared fact fails. |
| Checkable handoff | Expand citations from real native records/facts and restore captures without the original checkout. Changed source/fact/hash, wrong generation, unknown ID or prose-only claims fail. |
| Atomic coverage | Interrupt before/after checkpoint publication. The last accepted partial/complete record survives or none exists. A draft cannot satisfy coverage; conflicts and unvisited required pages fail. |
| Compaction coverage | Both observed native compaction paths discard earlier read coverage, including pages retained in replacement history. A compacted session cannot complete its partition or support an absence claim from those reads. Actual post-compaction re-delivery and a new checkpoint can restore coverage; late compaction before consumer admission still refuses. |
| Fresh consumer | Script a new native thread that receives only its declared inputs and accepted handoffs, rechecks them, and uses citations for an edit. Old context items or a skipped verification receipt fail. |
| Per-session capacity | Run the complete partition plan through the actual bridge; price startup, maximum handoffs, re-reads and reserves. Missing charges, an inflated allowance or a single oversized session fails. |
| Authority and lifecycle | Shared counters/deadline survive fresh contexts and failure. An unlisted transition, investigation-phase edit or early application fails; ordinary review/rework/closeout still gates one application. |
| Real launch layout | Credential-free scripted clients go through the production tmux launcher, watcher, supervision and application path. The observed write check accepts the valid run and fails when its tmux rule is removed. |

The offline native recipe should include three investigation contexts (one
partial continuation), then the existing five-turn edit/rework/review/closeout
shape, with no coordinator-authored semantic summary. It tests plumbing and
failure handling, not a real model's judgment. Capture every phase declaration
from the client request. The first separately granted live investigation then
measures the new reading formats and model-authored handoff; a failure is not
permission for another attempt or a quiet switch to the ordinary workflow.

## Proposed implementation bound and reassessment

Estimate **16–24 active hours**, including tests and one offline acceptance
round; propose a hard stop at **24 hours**. CI, review and owner waits are
recorded separately. The owner approved the bounds for the narrower first build;
this document does not authorize a live pass or promise semantic success.

- At **2 hours**, show the concrete handoff/fact-identity schema, the coverage
  partition for the retained corridor, initial per-session prices including
  maximum handoff sizes, and the exact fresh-context/login configuration seam.
  Establish that existing locks/captures can provide atomic publication. Apply
  the editor go/no-go in the authorized first-build section before integration.
- At **8 hours**, show a neutral interrupted-checkpoint/restart lifecycle and
  a fresh editor consuming checked citations, plus the current effort forecast.
- Proposed native allowance: **at most 10 credential-free loopback invocations**,
  including failed runs, with no automatic replacements and no provider calls.
  Eight are reserved for the full recipe above; two for the configuration seam.
  Read-only native login-status checks are separate from inference invocations
  but remain charged work. The owner approved this ceiling; it is not a target
  to spend when a capacity checkpoint has already stopped the slice.

Stop and reassess if the handoff or necessary re-reads recreate the original
capacity problem; a partition cannot fit; provenance or coverage needs a new
analysis engine; the clients require broader access or credential copying;
atomicity needs another transaction framework; orchestration needs a general
scheduler; the same failure class recurs; or the 24-hour bound is no longer
credible. Do not turn those findings into additional slices automatically.

Next: review the implementation checkpoints. After offline acceptance and CI,
prepare the finite live plan for review and a separate owner grant.
