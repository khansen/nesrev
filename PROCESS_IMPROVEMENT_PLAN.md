# Process Improvement Plan

Status: PI-1 through PI-5 and queue receipts are merged, including PI-2 runtime
delivery in [PR #105](https://github.com/khansen/nesrev/pull/105). PI-6 is merged
in [PR #141](https://github.com/khansen/nesrev/pull/141); PI-7 is merged in
[PR #142](https://github.com/khansen/nesrev/pull/142). PI-8 is merged in
[PR #143](https://github.com/khansen/nesrev/pull/143).
The first observation window has preliminary findings; its final review still
needs follow-up. [PI-9](#pi-9-historical-provenance) is implemented locally for
review, followed by a separate provenance-restoration batch after integration.
The observation assessment and other investigations below are
not implementation or additional-pass authorization.
Updated 2026-10-03.

This plan prioritizes reproducible tooling gaps found during friction-queue
review over repeated reports of already-fixed problems. It describes shared
contracts and acceptance criteria; corpus-specific evidence and progress
remain on the local-only corpus branch.

<a id="recommended-order"></a>
## Recommended order

1. Complete the final review follow-up and close the first
   [observation assessment](#observation-initial-assessment). A recorded approval
   made during a usage-limit grace period does not establish that the remaining
   review work was completed. Preserve the existing archive and document the
   follow-up outcome; do not start another pass automatically.
2. Review and land [PI-9: Historical provenance](#pi-9-historical-provenance),
   the bounded tooling and playbook change. It responds to blocked
   semantic renames and loss of historical attribution. Land that contract
   before the separately reviewed project-history repairs; integrate and repair
   at project pass boundaries.
3. Assess [interrupted-review completion](#interrupted-review-candidate) using
   the observed handoff, then decide whether a small prompt/harness change is
   needed. Distinguish an incomplete review from a completed review that relies
   on valid packet evidence; do not require duplicate builds merely to add work.
4. Investigate [inline-dispatch boundary coverage](#dispatch-boundary-candidate)
   with a small reproducer. The observed source repair is complete; an automatic
   detector's scope and confidence still need design.
5. Finish independent review of the separately authorized
   [bounded embedded-pointer feasibility audit](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#embedded-pointer-audit)
   before deciding on migration. Its synthetic results were reproduced, but
   fixture classifications and coverage claims needed correction; corpus joins,
   producer/consumer feasibility and acceptance criteria remain under review.
   That plan owns its scope. Production implementation remains a separate
   decision, with no demonstrated corpus-coverage gain or xasm extension need.

These are next-work priorities; review already underway can finish independently.
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

Status: the first five-pass window has a preliminary assessment below; the final
pass's review requires follow-up before closing the window. PI-6 through PI-8
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
### Preliminary assessment and follow-up decisions

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
| Approval issued during usage-limit grace period | Formal approval and archive exist, but the reviewer disclosed a skipped check only in chat | Finish review follow-up and assess interruption handling; do not infer review completeness from state alone |
| PI-6 reconciliation | Normal closeout and read-only handoff paths exercised with accepted final packets; no after-fix recurrence established | Refusal paths remain unexercised in this window |
| PI-7 deferrals | Valid capture and saved-corridor fallback exercised; a malformed explicit entry was rejected by preflight | Other refusal/context paths remain unexercised |
| PI-8 portability | All affected-scope decisions were `not-required`; no analyzer/fixture work triggered execution | No claim of production effectiveness from this window |

The receipt blocker is not an after-fix recurrence of PI-6, PI-7 or PI-8:
those repairs address different paths. Count review rounds from canonical
metadata, but leave the last pass's final round total and assessment open until
follow-up ends. Recorded rework mixes self-review corrections and rejected
commands; it is not a count of human interventions or measured elapsed cost.
Changes in round counts across different corridors do not establish a causal
productivity gain from the repairs.

Do not activate the monitor or experiment specs, add per-pass measurements, or
implement the rename-coverage candidate on the strength of this assessment.
Use existing logs for the pending follow-ups. This plan update changes priorities
and proposed contracts only; it changes no running session, gate or review state.

<a id="interrupted-review-candidate"></a>
### Candidate: preserve incomplete review at a usage limit

Status: first observed in this window; assess the completed follow-up before
choosing a prompt/harness implementation. A limit warning was followed by a
formal approval during the grace allowance; the implementer then archived it.
The reviewer disclosed the skipped independent build in chat; the durable review
did not retain that limitation. This demonstrates a reporting/completion risk,
not that the semantic
verdict was necessarily wrong or that packet-based parity evidence was invalid.

The bounded contract to evaluate is:

- If required review work remains, preserve pending review and save checked,
  unchecked and remaining work at the exact reviewed head. Do not issue an
  approval merely to end a turn, or request changes solely to encode a pause.
- If review is complete using valid supplied evidence, approval may stand;
  state clearly what was rerun, inspected or not checked. A duplicate scratch
  build is not universally required by this candidate.
- Automatic client continuation must not be treated as proof that a recorded
  approval will be reopened. Follow-up after approval is explicit and preserves
  the original verdict and archive, with a linked supplementary outcome.
- Before proposing a new state or provider-specific integration, test whether
  existing pending-state behavior and generated prompts can preserve this
  boundary. Any implementation needs an interrupted-review negative control and
  an honestly completed-review positive control; unrelated admissions and the
  authorized pass limit must remain unchanged.

<a id="dispatch-boundary-candidate"></a>
### Candidate: surface incomplete inline-dispatch boundaries

Status: bounded investigation proposed after a silent, consequential source
classification miss. A dispatch table's known entries ended before its actual
tail; warning-baselined raw bytes contained additional handler pointers. The
warning explanation asserted a symbolization limitation that a scratch parity
probe disproved. The source correction does not establish a general detector.

Start with synthetic complete, truncated and deliberately mixed code/data
tails. Use existing listing, instruction, xref and recovery-control facts to
ask whether an explicit dispatch can consume words beyond its declared extent.
Require evidence for selector bounds, target instruction boundaries and bank
selection. Numeric resemblance to executable addresses is insufficient, and
missing bank/extent proof must remain an explicit uncertainty. Include valid
non-pointer trailing data so the investigation cannot simply flag every tail.
Record whether the defect is covered by an existing check before designing an
advisory. Do not silently extend table extents, rewrite sources, add an xasm
schema, or promote an uncertain result to a hard gate.

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
New observation follow-ups below are planning items; updating this plan does not
start their implementation, publish a PR, or rebase an active project checkout.

<a id="pi-9-historical-receipt-residue"></a>
<a id="pi-9-historical-provenance"></a>
## PI-9 — Preserve historical provenance during symbol renames

Status: phase A implemented locally on `fix/pi-9-historical-provenance`, pending
independent review and landing. Phase B remains a separate audit/restoration
batch after local integration. This section specifies both; no separate spec is
required. The live corpus and agent session have not been changed.

Closeout's [residue sweep](scripts/project_pass_residue_check.sh) treats old
symbols in canonical friction receipts and earlier scorecard rows as current
references. The [preflight rule](agent_playbook/PASS_WORKFLOW.md#completion-checklist)
explicitly tells agents to paraphrase historical mentions to satisfy that sweep.
The [docs symbol check](scripts/check_docs.sh) and
[reference rules](agent_playbook/DOCUMENTATION.md#reference-document-use) also
require scorecard symbols to resolve against current assembly. Fixing only
receipt input selection would leave these other pressures to erase attribution.

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
and genuinely missing symbols. Hosts without such a locale explicitly skip
that fixture. Three scratch mutations reject the sort mismatch, eager no-rename
document reads, and unhandled decode errors. The supported `make -C` invocation
from outside the repository also passes; direct helper invocation outside the
repository root is not newly supported. Full shell/Java suites and timing were
not rerun for this follow-up. The old timing receipts did not record locale
and do not establish performance across locales.

<a id="pi-9-provenance-restoration"></a>
### Phase B — Audit and restore existing project provenance

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
is limited to the checks affected by each resulting change. Phase A's tooling
branch restores no project records; phase B needs separately reviewed repairs.

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
