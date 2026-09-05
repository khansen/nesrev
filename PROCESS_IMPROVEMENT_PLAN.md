# Process Improvement Plan

Status: PI-1, PI-2 policy evidence, PI-3, PI-4, and queue receipts merged.
Runtime-evidence activation is held; PI-5 is approved for landing.
Updated 2026-09-06.

This plan prioritizes reproducible tooling gaps found during friction-queue
review over repeated reports of already-fixed problems. It describes shared
contracts and acceptance criteria; corpus-specific evidence and progress
remain on the local-only corpus branch.

## Recommended order

Start with PI-1, then PI-2: both address checks that can pass without
examining the evidence their output appears to cover. Follow with PI-3
through PI-5. Triage decisions and routing can accompany these changes,
but queue pruning must wait for the receipt migration, receipt-aware
ingestion, and acceptance tests described below. Once that prerequisite is
complete, accepted items leave the queue when routed, without waiting for
their implementation.

To support incremental pruning, implement queue receipts after the PI-2
policy-evidence lane and before continuing with runtime evidence and PI-3
through PI-5. Do not prune during that prerequisite's implementation.

Each implementation should include a failing regression fixture, positive
controls, and representative cross-project checks. Follow the existing
[process-change review requirements](agent_playbook/REVIEW_AUDITS.md#process-change-review-sanity-checks),
including mutation tests in a disposable worktree and explicit checked,
skipped, and failed results. Do not convert uncertain heuristics into hard
gates merely to increase coverage.

## Delivery and tracking

Implement shared changes on feature branches from current `master`, using
separate worktrees. Shared changes, commit messages, and PR descriptions must
not name actual games or include corpus-specific symbols, paths, or review
references. Use synthetic fixtures and generic examples instead. Keep
game-specific evidence, migrations, and eventual queue pruning on the
local-only corpus branch; never push that branch or private ROM fixtures.
Each implementation branch updates this plan with its status and
reviewed commit or PR reference. Do not activate a gate on the corpus until
its required local migrations are ready and tested together with the tooling.

| Branch | Scope | Status |
|---|---|---|
| `fix/pi-1-checker-coverage` | Consumer parsing and PPU stream coverage | Merged [PR #98](https://github.com/khansen/nesrev/pull/98); reviewed `70e488a7f` |
| `feat/pi-2-policy-evidence` | Manifest membership and disposition checks | Merged [PR #100](https://github.com/khansen/nesrev/pull/100); reviewed `447b72477` with local activation migration |
| `feat/pi-2-runtime-evidence` | Runtime deferrals and executable evidence | Implementation `7b19459aa` independently approved; activation held, unmerged |
| `feat/pi-3-consumer-audits` | Reusable audit machinery | Merged [PR #102](https://github.com/khansen/nesrev/pull/102); reviewed `90fda2af3` with the local adapter migration |
| `feat/pi-4-review-bundles` | Complete evidence and gate reporting | Merged [PR #103](https://github.com/khansen/nesrev/pull/103); reviewed `eff6b00ab` |
| `fix/pi-5-intake-baselines` | Historical measurement protection | Independently approved `28427b0a4` with the receipt-only local migration; landing pending |
| `feat/process-queue-lifecycle` | Receipt migration and pruning-safe ingestion | Merged [PR #101](https://github.com/khansen/nesrev/pull/101); reviewed `8bafbf7f4`; local pruning active |

Use ordinary process/tooling branch review, including bad-direction tests
and representative corpus checks. Do not use the project-pass handoff state
machine for these branches. Remote publication and corpus rebases are separate
landing actions, not implicit consequences of creating a local commit.
The remaining execution is authorized: obtain review approval before each
PR, merge only after verification, then fetch and rebase the local corpus onto
updated `master`. Rerun affected CI after each merge; report pre-existing
unfinished-input failures separately and never relabel relaxed checks as
strict-CI success. Prune eligible queue entries incrementally once receipts
and their migration tests are in place.

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

The runtime implementation is held unmerged: independent activation review
found a legacy runtime classification without matching trace infrastructure.
Do not invent a manifest, substitute unrelated assets, or reclassify to restore
green. The supported local migration is prepared; unsupported evidence remains
explicit debt. Continue independent PI-3 through PI-5 work without activating
this gate or starting semantic passes or captures.

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
