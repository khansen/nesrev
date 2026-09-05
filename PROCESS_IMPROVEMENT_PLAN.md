# Process Improvement Plan

Status: PI-1 implementation, independent review, and local reference migration
complete. Other items and queue cleanup pending.
Corpus review snapshot: 2026-09-05, local `projects` head `dfa985afd`.

Corpus references below are local paths, not links into `master`: the
`projects/` tree and `PROJECT_MATURITY_DEBT_RETIREMENT_PLAN.md` exist only on
the local-only `projects` branch. Shared tooling and playbook links resolve
on `master`. Never push the corpus branch or private ROM fixtures.

This plan follows the review of all 20 project `PROCESS_FRICTION.md` files
after Golf and Tennis completed their maturity-debt work. It prioritizes
reproducible tooling gaps over repeated reports of already-fixed problems.
Project progress remains in
PROJECT_MATURITY_DEBT_RETIREMENT_PLAN.md (`PROJECT_MATURITY_DEBT_RETIREMENT_PLAN.md`).

## Recommended order

Start with PI-1, then PI-2: both address checks that can pass without
examining the evidence their output appears to cover. Follow with PI-3
through PI-5. Triage decisions and routing can accompany these changes,
but queue pruning must wait for the receipt migration, receipt-aware
ingestion, and acceptance tests described below. Once that prerequisite is
complete, accepted items leave the queue when routed, without waiting for
their implementation.

Each implementation should include a failing regression fixture, positive
controls, and representative cross-project checks. Follow the existing
[process-change review requirements](agent_playbook/REVIEW_AUDITS.md#process-change-review-sanity-checks),
including mutation tests in a disposable worktree and explicit checked,
skipped, and failed results. Do not convert uncertain heuristics into hard
gates merely to increase coverage.

## Delivery and tracking

The plan was committed as `683a22c64` on local `master` from
`docs/process-improvement-plan`. Implement shared changes on feature branches
from current `master`, using separate worktrees.
Keep game-specific migrations and eventual queue pruning on local-only
`projects`. Each implementation branch updates this plan with its status and
reviewed commit or PR reference. Do not activate a gate on the corpus until
its required local migrations are ready and tested together with the tooling.

| Branch | Scope | Status |
|---|---|---|
| `fix/pi-1-checker-coverage` | Consumer parsing and PPU stream coverage | Reviewed `70e488a7f`; migration `98358deda` verified |
| `feat/pi-2-policy-evidence` | Manifest membership and disposition checks | Pending |
| `feat/pi-2-runtime-evidence` | Runtime deferrals and executable evidence | Pending |
| `feat/pi-3-consumer-audits` | Reusable audit machinery | Pending |
| `feat/pi-4-review-bundles` | Complete evidence and gate reporting | Pending |
| `fix/pi-5-intake-baselines` | Historical measurement protection | Pending |
| `feat/process-queue-lifecycle` | Receipt migration and pruning-safe ingestion | Pending |

Use ordinary process/tooling branch review, including bad-direction tests
and representative corpus checks. Do not use the project-pass handoff state
machine for these branches. Remote publication and corpus rebases are separate
landing actions, not implicit consequences of creating a local commit.

## PI-1 — Make checker coverage explicit

Baseline evidence: Tennis has 197 `Used by` annotations, yet its check reported zero
parsed symbol-shaped claims. The
[parser](scripts/used_by_xref_check.py) accepts a bare consumer name but
ignores the same name in backticks. Separately,
[PPU packet checking](scripts/ppu_packet_line_check.py) requires a particular
label substring, excluding documented streams with other semantic names;
see Devil World pass 165 (`projects/devil_world/docs/reverse_engineering/reviews/pass-165.md`).

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
- Read-only fresh-xref scan of all 22 local projects completed. Tennis now
  checks 173 of 197 annotations, with 24 skipped and 6 partially checked;
  these counts do not assert semantic ownership. Devil World checks 16 packet
  declarations and explicitly skips 9 other formats, including grouped data.
  Duck Hunt checks 3 declarations and skips 2; its plural stream declaration
  describes multiple entries and must not claim coverage of only the first.
- In an isolated corpus worktree, `make project-ci PROJECT=tennis` and
  `make project-ci PROJECT=devil_world` both exit 0. Hogan's Alley strict CI
  exits 2 at its existing 159-unresolved-label gate. Its pass-time
  `project-verify ALLOW_UNRESOLVED_LXXXX=1`, `project-process-check`, and
  `project-docs-check` all exit 0; relaxed verification is not strict CI.

Initial independent review of `8ebf6fe10` approved the consumer changes and
identified PPU boundary gaps. Follow-up regressions cover grouped wording
after the canonical prefix, payload fields inside shared suffixes, and
annotated same-address aliases. All three fail against `8ebf6fe10` and pass
with the fixes. A further regression covers either field owner across three
chained aliases or suffixes, including unrelated-owner refusal; it fails
against `20c9069e4` and passes with shared ownership context. Both independent
reviewers in tmux panes `%0` and `%1` approved `70e488a7f` on 2026-09-05;
no material implementation findings remain. Approval does not activate the
gate on the corpus or authorize publication.

The five newly exposed stale consumer names were corrected in local-only
migration `98358deda` on `fix/pi-1-corpus-references`, using current
producer/consumer evidence:

| Project / declaration | Current declaration references |
|---|---|
| Golf / `CourseCollisionData` | `LoadCourseLayout`; nearby prose identifies the `CheckTerrainType` RAM-copy reader |
| Mario Bros. / `PowSpawnTileScript` | `UpdatePOWBlock` |
| Mario Bros. / `PowTriggerTileScript` | `UpdatePOWBlock`, `UpdateKickAnimationState`, `TryInitPlayerDeathFromCollision` |
| Popeye / `HudDigitPacketTemplate` | `QueueHudDigitPacket` |

The migration also corrects matching current memory-map references; historical
pass records remain unchanged. With the reviewed PI-1 checkers overlaid,
`project-verify` and full `project-ci` each pass for Golf, Mario Bros., and
Popeye. A fresh-xref scan of all 22 projects reports zero consumer hard errors;
unsupported annotations and ownership advisories are still reported, not
asserted correct. No assembly instructions or data bytes changed.

The scan also exposes two packet-layout advisories in Kung Fu and one in
Metroid; those are formatting debt, not new hard gates or gameplay bugs.
Friction queues remain unchanged. The user authorized pushing and merging
PI-1, then fetching and rebasing local-only `projects` onto `origin/master`.
Include the local reference migration before that rebase; never push the
corpus branch or its private fixtures. The migration commit reference above
is the pre-rebase snapshot, retained by its local branch.

## PI-2 — Validate evidence membership and runtime deferrals

Evidence: the [policy-baseline checker](scripts/policy_baseline_audit_check.py)
compares live totals with summary markers without validating the manifest's
actual membership and dispositions. The
[blob-disposition row validator](scripts/data_blob_dispositions_check.py)
accepts a `runtime_gated` row with no artifact when its prose fields are
populated. That row-level probe does not establish that every other project
gate can be bypassed. Review examples:
Tennis pass 54 (`projects/tennis/docs/reverse_engineering/reviews/pass-54.md`)
and pass 62 (`projects/tennis/docs/reverse_engineering/reviews/pass-62.md`).

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

## PI-3 — Reuse executable consumer-boundary audits

Evidence: Golf's documented 20-byte course tail was actually consumed as
32 bytes because a helper changes the index; see
pass 276 (`projects/golf/docs/reverse_engineering/reviews/pass-276.md`).
Tennis likewise needed caller-state and reader-boundary evidence, not merely
next-label extents; see its
contact-asset audit (`projects/tennis/docs/reverse_engineering/CONTACT_ASSET_AUDIT.md`).

Work:

- Reuse bounded techniques from Golf's
  course-payload (`projects/golf/scripts/audit_course_payload.py`) and
  terrain (`projects/golf/scripts/audit_terrain_classification.py`) audits and
  Tennis's contact-asset audit (`projects/tennis/scripts/audit_contact_assets.py`).
- Distinguish physical allocation, selected record, and actual read range.
  Account for carry, eight-bit wrap, helper side effects, overlapping tails,
  and multi-channel timing where the consumer requires them.
- Tie checks to fresh source/listing evidence. State which caller invariants
  remain manually proved; an enumerator is not a general control-flow proof.

Done when: regression fixtures reject the old incorrect bounds/models,
including relevant wrap and helper effects, while the correct models pass.
Keep game-specific semantics local; extract shared machinery only where the
same contract genuinely recurs. Do not attempt a general 6502 proof engine.

## PI-4 — Make review bundles self-contained and reproducible

Evidence: the [review-packet wrapper](scripts/project_pass_review_packet.sh)
labels a project-filtered history section “Complete Commit List And
Diffstat,” omitting root-level changes such as the maturity dashboard. See
Tennis pass 63 (`projects/tennis/docs/reverse_engineering/reviews/pass-63.md`)
and Donkey Kong pass 262 (`projects/donkey_kong/docs/reverse_engineering/reviews/pass-262.md`).
Separate reviews document a
cold coverage cache (`projects/donkey_kong/docs/reverse_engineering/reviews/pass-265.md`),
a missing private ROM fixture (`projects/mario_bros/docs/reverse_engineering/reviews/pass-302.md`),
and different assembler binaries reporting the same version (`projects/hogans_alley/docs/reverse_engineering/reviews/pass-13.md`).

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

## PI-5 — Separate intake snapshots from historical baselines

Evidence: [project intake](scripts/project_intake.sh) synchronizes pass 0
after expensive checks. Tennis lacked that legacy row; Golf had historical
measurements that intake silently replaced. Both cases are recorded in
Tennis pass 64 (`projects/tennis/docs/reverse_engineering/reviews/pass-64.md`).

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
not protect untracked notes; the currently untracked Duck Hunt friction file
needs particular care. Preserve unique useful evidence and its disposition
in the appropriate durable destination before removing its sole copy.
Check the relevant content, not just whether an archive file exists:
`learning_artifacts` in [review ingestion](scripts/agent_review.py) imports
implementation notes as well as reviews and responses, while `render_archive`
retains only reviews and responses. Implementation-note candidates therefore
need the same content-preservation check, even when their linked review is
already archived.

### Queue cleanup and ingestion follow-up

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
scoped-owner snapshot issues, Hogan's Alley items already recorded as
disposed, and superseded blanket worked-example requirements. Do not revive
these without a fresh reproducer. Likewise, a rejected or false-positive
heuristic is not a pending hard-gate requirement merely because it appears
in an older review.

This document records the proposed work and lifecycle. It does not itself
change tooling, playbooks, review archives, or existing friction queues.
