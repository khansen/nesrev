# PASS_WORKFLOW Playbook

This playbook is the canonical home for the operational pass lifecycle — resume/warm-up, `project-pass-prep`/`-next-pass`/`-pass-start`, current-pass plan handling, scorecard synchronization, raw-RAM review queue operation, closeout and verification, generated cache vs. authored artifact distinctions, batching/rework/commit boundaries, and RAM-symbolization prioritization. Naming and structured-field conventions stay in [`ASM_STYLE.md`](ASM_STYLE.md).

## Ownership

This playbook owns the operational pass lifecycle:

- resume/warm-up sequence
- `project-pass-prep`, `project-next-pass`, `project-pass-start`
- candidate-evidence framing, operator-selected corridor objective,
  pass-versus-commit, and the low-yield strategy checkpoint
- current-pass plan handling
- scorecard synchronization
- raw-RAM review queue operation
- closeout and verification sequence
- generated cache vs. authored artifact distinctions
- batching, rework, and commit boundaries
- RAM symbolization prioritization, provenance review, queue status,
  repeated-deferral handling, and strategy switching (symbol-prefix and
  other naming conventions live at
  [ASM_STYLE.md#naming-conventions](ASM_STYLE.md#naming-conventions);
  structured-field offsets at
  [ASM_STYLE.md#structured-field-offsets](ASM_STYLE.md#structured-field-offsets);
  packed-state promotion at
  [ASM_STYLE.md#state-action-constants](ASM_STYLE.md#state-action-constants))

The root `AGENTS.md` retains the mandatory lifecycle summary; this file holds
the operational detail.

## Playbook Sections

<a id="session-resume"></a>
## Session Resume and Warm-Up

The universal session-start rule —
[Always start a session by identifying the current goal and project
status](../AGENTS.md#session-orientation) — applies to both new and
resumed projects.

When resuming an existing project, run the wrappers in this order:

1. **Identify the active project.** Check `projects/` for the slug or
   ask the user if multiple candidates exist.
2. **Prepare pass artifacts** — see [#pass-prep](#pass-prep).
3. **Read the status brief** — see [#next-pass](#next-pass).
4. **Read working notes if present.** If
   `docs/reverse_engineering/WORKING_NOTES.md` exists for the project,
   read it before substantial edits. Use it only for durable
   project-specific insights, invariants, heuristics, and other
   agent-facing facts that are likely to help future passes and do not
   fit the systems doc, memory map, or scorecard.
5. **Select the corridor objective.** Treat the generated briefing as
   candidate evidence and choose the corridor per
   [#corridor-objective](#corridor-objective) (interpret "high-value" via
   [AGENTS.md#guiding-pass-philosophy](../AGENTS.md#guiding-pass-philosophy)).
   If the briefing has no strong corridor, apply the
   [AGENTS.md#reviewer-simulation-checklist](../AGENTS.md#reviewer-simulation-checklist)
   before deciding that only doc closure remains.
6. **Persist the pass plan** — record the choice via
   `make project-pass-start PROJECT=<slug> TARGET=<corridor_anchor_or_notes_plan>`;
   see [#pass-start](#pass-start).

The closeout half of the lifecycle (`project-pass-closeout`,
`project-ci`, scorecard sync, gates) lives at
[#pass-closeout](#pass-closeout).

### Wrapper-first evidence rule

Treat the generated pass artifacts as the primary evidence source for
target selection and structural analysis. Do not fall back to broad
asm greps, ad-hoc counting scripts, or manual KPI re-derivation unless
the needed fact is absent from the prep outputs.
### Owner-field rule

When `xref_with_data.json` is available, prefer the emitted
`owner_routine` / `owner_routine_addr` fields over re-deriving lexical
owners from raw symbol definitions.
<a id="pass-prep"></a>
## Pass Prep

`make project-pass-prep PROJECT=<slug>` is the de facto start-of-pass
command. It refreshes inventories and generates the machine-readable
pass inputs under
`docs/reverse_engineering/inventory/pass/` —
see [#generated-vs-authored-artifacts](#generated-vs-authored-artifacts)
for the cache-vs-source-of-truth contract.
`project-pass-prep` refreshes inventories; do not manually re-derive
the same pass inputs unless the prep artifacts are missing or stale.
For the full project gate, use `make project-ci PROJECT=<slug>` only
when the complete CI sequence is needed — not as the default warm-up
command.
<a id="next-pass"></a>
## Next Pass Selection

`make project-next-pass PROJECT=<slug>` emits evidence buckets. It ranks
hotspots, not strategy; select the corridor objective
([#corridor-objective](#corridor-objective)).
Its persisted output (`next_pass.json`) may include:

- `recommended_pass` — compatibility key for the top evidence bucket;
  accept, broaden, or reject it
- `operator_guidance` and `operator_signals` — process reminders plus recent
  scorecard / notes signals
- `selection_strategy` describing the current pass-selection workflow
- `cluster_candidates` grouped by owner corridor or subsystem
- `data_anchor_hints` for `kind=data` targets
- `ram_provenance` for RAM-heavy corridors
- `raw_ram_symbolization` candidates and unnamed raw-RAM provenance
  once `LXXXX=0` but strict raw low-address operands remain
<a id="pass-start"></a>
## Pass Start

`make project-pass-start PROJECT=<slug>` records the selected objective.
Pass `TARGET=<corridor_anchor_or_notes_plan>` (optional
`PASS=<id>`) to record the operator's choice
([#corridor-objective](#corridor-objective)); without `TARGET` the wrapper
warns and uses the first evidence bucket only as a mechanical fallback.
Generated and notes-driven corridors are accepted. Treat
`current_pass_plan.json` / `.md` as the compaction resume point.

<a id="corridor-objective"></a>
## Corridor Objective (Mandatory)

`project-next-pass` is candidate evidence, not an authoritative
recommender: it ranks what is visible, not what is strategically best.
Before substantial edits the operator must select and record a corridor
objective stating:

- **selected corridor** — the subsystem slice being owned now
- **why now** — the maturity gap or evidence that makes it worth opening
- **expected boundaries** — owning routines, data, RAM/ZP, interfaces
- **generated evidence** — which candidates support this corridor
- **explicitly out of scope** — candidates ignored or deferred this pass

A generated local anchor (one routine, table, raw byte, or branch
cluster) is not a pass. Broaden it into a corridor or explicitly reject
it. Persist the objective with `project-pass-start` — the fields are
written to `current_pass_plan.json`/`.md`; omitted fields warn but do not
fail:

```sh
make project-pass-start PROJECT=<slug> TARGET=<corridor_anchor> \
  CORRIDOR="..." WHY_NOW="..." BOUNDARIES="..." EVIDENCE="..." OUT_OF_SCOPE="..."
```

Keep rationale in `WORKING_NOTES.md`, not chat.

<a id="low-yield-checkpoint"></a>
## Low-Yield Strategy Checkpoint

If recent passes are low-yield, stop. Pick a broader corridor, switch to a
readability sweep, run the
[static debt audit](REVIEW_AUDITS.md#static-readability-debt-audit), or record
the plan in `WORKING_NOTES.md`. Do not accept generated buckets repeatedly; static
exhaustion requires audit dispositions.
<a id="current-pass-plan"></a>
## Current Pass Plan

`current_pass_plan.json` and `current_pass_plan.md` are the persisted
corridor-selection briefing written by `project-pass-start`. It is
one-pass-scoped and overwritten by the next `pass-start`; use it to
resume the operator's corridor objective (the `corridor_objective`
fields), selected anchor, open range, corridor members, scope barriers,
and localization candidates after context compaction. It is not an
authored work log or gate ledger.

Completed work and decisions persist through `renames.csv` and the
`PROGRESS_SCORECARD.md` row written by `project-pass-closeout`, not
through `current_pass_plan.md`. Contrast with `WORKING_NOTES.md`,
which is the durable cross-pass research log; `current_pass_plan.md`
is generated cache.
<a id="scorecard-sync"></a>
## Scorecard Synchronization

`PROGRESS_SCORECARD.md` tracks per-pass throughput and quality
signals. `project-pass-closeout` auto-syncs most KPI cells in the
latest pass row — see [#pass-closeout](#pass-closeout). Metrics:

`project-process-check` enforces basic ledger integrity: pass IDs must be
unique and strictly increasing in file order; historical rows must not leave
`verify` or `docs_check` blank/`pending`; the latest row may stay pending while
`project-pass-finish` is still running. Notes cells must also avoid raw `|`
characters because Markdown treats them as column delimiters; write pipe-shaped
formats such as `bank|$addr` in prose form (`bank 1 $A64C`) instead.

1. **Pass count.** Mature project target: `<= 12` major passes to
   the quality bar. Count meaningful edit/verify passes.
2. **Rework rate.** Target `< 15%` late fixes per pass. If exceeded,
   add preventive checklist items.
3. **Verification cadence.** `100%` of edit batches run parity
   verification — mechanics live at
   [AGENTS.md#safety-rules](../AGENTS.md#safety-rules).
4. **Interaction efficiency.** Front-load mandatory sweeps to
   reduce repeated reviewer prompts.
5. **Context efficiency.** Use inventories under
   `docs/reverse_engineering/inventory/` instead of repeated
   whole-file rescans.
6. **Constantization burn-down.** Track via
   `MAX_ACTIVE_MAGIC_IMMEDIATES` in `inventory/kpis.conf`. Trend to
   `0`.
7. **Confidence burn-down.** Track via `MAX_INFERRED_ANNOTATIONS`
   and `MAX_PLACEHOLDER_COMMENTS`. Inferred tags trend down;
   placeholder comments stay at `0`.
8. **Data-label doc coverage.** Track via
   `MAX_UNDOCUMENTED_DATA_LABELS` in `inventory/kpis.conf`. Target
   `0` noncompliant data labels.
9. **KPI calibration timing (mandatory).** Never set `MAX_*` values
   while known undecoded `.DB` blobs exist. Complete pointer/blob
   recovery first; mark provisional baselines explicitly.
10. **KPI anti-gaming (mandatory).** KPI reduction is a measurement
    outcome, not an objective. Every scorecard row must state a
    readability or semantic gain.

<a id="legacy-retrofit-scorecard-artifact"></a>
### Legacy Retrofit

Legacy refresh uses a scorecard `notes` marker
`legacy-retrofit-audit:` with fields `semantic_claims`, `procedures`,
`global_code_labels`, `retained_headerless`, and `action`. Denominators are
live detail-line counts; `0/0` is complete; zero undocumented headers are not
required. Validate with
`make project-legacy-retrofit-check PROJECT=<slug> REQUIRE=1`.

<a id="raw-ram-prioritization"></a>
## Raw-RAM Symbolization Prioritization

When the next corridor is raw-RAM work, rank candidates this way:

- **High-fanout first within a coherent ownership corridor.** Rank
  raw RAM bytes by active executable usage (exclude `.DB` blobs) and
  pick the highest-fanout byte *within a single subsystem corridor*.
  Cross-subsystem fanout is a mixed-role warning — likely scratch or
  overlay storage — and should route through
  [#raw-ram-queue](#raw-ram-queue) (contextual overlay aliases,
  mixed-overlay stop rule) rather than getting a global semantic name.
  Confirm active usage before naming. Use neutral names when semantics
  are partial. Recompute ranking after each major pass.
- **Cluster first.** Symbolize tightly-coupled byte clusters in one
  pass (audio cursors + timers + state, packet writer cursor + style
  + queue, etc.). Define the cluster boundary from active code.
  Replace all callsites in the same batch.
- **Role-based sweep order.** Prioritize by subsystem impact, not
  address range. Order: high-fanout packet/buffer windows, sprite/
  object shadows, subsystem state clusters, then ZP scratch. Require
  active-code confirmation; exclude `.DB`-blob-only bytes until
  classified.
Symbol prefixes and other naming conventions live at
[ASM_STYLE.md#naming-conventions](ASM_STYLE.md#naming-conventions);
structured-field offsets live at
[ASM_STYLE.md#structured-field-offsets](ASM_STYLE.md#structured-field-offsets);
packed-state promotion rules live at
[ASM_STYLE.md#state-action-constants](ASM_STYLE.md#state-action-constants).
This section governs which bytes to attack next, not how to spell
them.
<a id="raw-ram-queue"></a>
## Raw-RAM Review Queue

Use `docs/reverse_engineering/inventory/raw_ram_review.csv` as the
persistent review queue for unnamed raw RAM bytes and windows. It is
a working ledger (not cache); `project-next-pass` refreshes factual
owner/count fields while preserving review fields.
**Status values:** `candidate`, `unreviewed`, `deferred`, `revisit`,
`not_semantic_yet`, `symbolized`.
**Immediate flush.** As soon as you inspect a byte and reach a
judgment, flush via
`make project-raw-ram-review PROJECT=<slug> ADDR=<addr> STATUS=<...>`
(optional: `SYMBOL`, `NOTES`, `PASS`). Record both positive and
negative results immediately.
**Repeated-deferral escape.** If a candidate corridor has been
deferred recently and still spans incompatible roles, narrow or
switch corridors. Do not re-triage the same dead end pass after
pass.
**Strategy-switch rule.** Apply the high-value-pass philosophy to
queue work too. If mixed-byte / overlay analysis is producing
low-yield micro-passes, switch strategies without waiting for user
intervention. Prefer broader, mechanical but readability-positive
sweeps such as:

- canonicalizing already-proven scratch-window operands to the
  existing `ZP_Scratch*` names
- sweeping residual raw sites for an existing symbol family
- taking a larger consumer family or helper bundle instead of another
  single-byte overlay
**Overlay restraint.** Existing overlays may remain, but any new
overlay must still clear the high-value bar from
[AGENTS.md#guiding-pass-philosophy](../AGENTS.md#guiding-pass-philosophy)
and [AGENTS.md#high-value-pass-contract](../AGENTS.md#high-value-pass-contract).
**Existing-symbol cleanup priority.** Before attacking ambiguous raw
bytes, clean residual raw operand sites for proven symbols first;
work methodically from the queue using a durable corridor plan in
`WORKING_NOTES.md` rather than repeatedly sampling isolated hottest
operands.
**Structured-field validation.** Before naming a queue entry,
identify at least one writer and one reader. If the byte lies inside
a known structured block or mirrored record, test whether it is an
instance of an existing field offset before inventing a new symbol.
Prefer mirrored or base-plus-field names when supported.
**Contextual overlay aliases.** When a byte is globally mixed but
has one high-confidence local role, prefer a scoped overlay alias
rather than forcing a global name. Record the ledger row with
`confidence=scoped-overlay`; closeout treats it as a partial alias.
**Mixed-overlay stop rule.** If only a live subrange or cadence is
proven and the scan crosses later declarations or incompatible
roles, stop short of inventing a full split. Document the proven
window and cadence, keep the blob unsplit, and move on until
stronger evidence appears.
**Exact-offset note convention.** For unsplittable mixed blobs,
record proven windows as relative offsets or ranges (for example
`+$0E..+$D8`, `3-byte cadence`) in `WORKING_NOTES.md`. Add the same
fact at the declaration only when a reader working at the blob needs it;
do not duplicate it mechanically or add fake labels with no stable consumer.
Symbol-prefix families, structured-field naming conventions, and
overlay alias spelling are documented in
[ASM_STYLE.md#naming-conventions](ASM_STYLE.md#naming-conventions)
and [ASM_STYLE.md#structured-field-offsets](ASM_STYLE.md#structured-field-offsets);
this section governs queue review and overlay introduction.
<a id="pass-closeout"></a>
## Pass Closeout and Verification

`make project-pass-closeout PROJECT=<slug>` (optional `PASS=<id>`) is the
residue/materialization gate: it must confirm project changes and a scorecard
row. Run it after the edit batch; sequencing lives at
[#batching-and-commit-boundaries](#batching-and-commit-boundaries).

`make project-pass-finish PROJECT=<slug>` is the preferred full-closeout
wrapper. It materializes the scorecard row, refreshes inventory, runs
closeout, docs/process checks, verification (`VERIFY_MODE=strict|relaxed`),
updates `verify` / `docs_check`, and reruns docs check. Closeout remains the
residue gate.

The scorecard row summarizes closed and remaining work. Closeout
echoes `current_pass_plan.json` and warns if the objective is
incomplete, stale, or missing. It auto-syncs derived KPI cells in the highest
numeric `pass_id` row; do not hand-type them. Current-pass `raw_$NNNN` renames
must have no remaining executable numeric operands; scoped overlays are reported
without forcing unrelated uses of the same byte to change.
Parity verification mechanics (run `make project-verify`
sequentially after every batch; never run assemble and parity
compare concurrently; mandatory verification gate after every
symbolic shift) stay canonical at
[AGENTS.md#safety-rules](../AGENTS.md#safety-rules); this section
does not restate them.

<a id="hardware-drift"></a>
### Canonical hardware-constant drift (advisory)

`project-process-check` warns when a project `.EQU` uses a canonical hardware
prefix (`PPUCTRL_`, `PPUMASK_`, `PPUSTATUS_`, `PAD_`, `OAM_`, `APU_`, `JOY1_`,
`JOY2_`) but is not a canonical name from
[ASM_STYLE.md#hardware-constants](ASM_STYLE.md#hardware-constants). It is
advisory — the gate still passes. Resolve each: rename to a canonical constant,
promote it to the canonical table if globally reusable, or allowlist a
project-local composite/encoding in
`docs/reverse_engineering/inventory/hardware_local_allowlist.txt` (one symbol
per line; `#` comments and blank lines ignored; a missing file means none).

### Pre-close relocation safety gate
Before closing a pass, audit:
- no avoidable `JSR/JMP $XXXX` to known labels
- no raw pointer-byte loads where `#<Label`/`#>Label` works
- record/header pointers symbolized
- loop bounds use `Start/End` math
- major blobs have `...End` labels
- a data table the pass named or created that a consumer indexes with a
  **masked or fixed-count** index (`AND #mask` / `CPX #count` before
  `LDA Table,Y`) has an `expected_size` row in `data_extent_assertions.csv`
  pinning its span — e.g. a four-entry default table read via
  `AND #$03 / TAY / LDA Table,Y` must assert size 4, or a later edit can
  silently let the index run past the table. The masked/counted index is the
  bound proof; see [QUALITY_REVIEW.md](QUALITY_REVIEW.md)
- touched opaque data/blob containers have an internal-structure disposition
  per [REVIEW_AUDITS.md#static-readability-debt-audit](REVIEW_AUDITS.md#static-readability-debt-audit)
- every remaining semantic literal is symbolized, structurally derived, or
  dispositioned through the canonical allowlist/parity-bug rules; an inline
  comment is not a substitute for any of those outcomes

### Pre-verify change impact checklist

Before running verify, preempt the known failure modes in one pass:

- **After any rename:** grep for the stale old label in asm and
  docs; update `renames.csv` (`old_name,new_name,reason,confidence,pass_id`).
  Use `mechanical` confidence for non-semantic aliases.
- **Pointer-table edits:** scan for `BaseLabel+$NN` in pointer
  tables; convert to dedicated target labels. Verify packet-format
  alignment if applicable.
- **New global label:** localize it when it is only internal control flow.
  If it is a real public code entry, add a useful contract/entry-role header
  only when it passes
  [DOCUMENTATION.md#comment-quality](DOCUMENTATION.md#comment-quality).
  For nontrivial data, add the minimal `Format:` / `Used by:` block. Never add
  a tautological header solely to lower a documentation KPI. Remove
  the entry from `WARNING_BASELINE.txt` if it was previously
  baselined as unreferenced (after the symbol has a real
  assembler-visible reference — see
  [NEW_PROJECT.md#warning-baseline-bootstrap](NEW_PROJECT.md#warning-baseline-bootstrap)
  for the resolution order).
- **New reference to a previously unreferenced label:** remove the
  baseline entry before first verify.
- **Opaque data/blob label touched:** trace the consumer and run the
  internal-structure check from the static readability debt audit; split proven
  substructures and relocate proven pointer fields before closeout.
- **Blob decode (`.DB` -> instructions):** complete the
  [AGENTS.md#blob-decode-kpi-pre-assessment](../AGENTS.md#blob-decode-kpi-pre-assessment)
  checklist before verify.
- **Docs edited:** run
  `make project-docs-check PROJECT=<slug>` before
  `make project-ci PROJECT=<slug>`.
<a id="semantic-pass-verification"></a>
### Verification mode while semantic naming remains incomplete

Every semantic pass must preserve binary identity. While unresolved
`LXXXX` labels remain, run:

```sh
ALLOW_UNRESOLVED_LXXXX=1 make project-verify PROJECT=<slug>
```

`project-intake` sets this mode automatically. An early corridor may
close this way only when unresolved labels are the sole strict failure.
Record the result explicitly in the scorecard, for example
`pass (LXXXX gate suppressed; strict verify blocked by N labels)`.
Do not call it strict-green.

Run without the override before closing semantic coverage, final
gold-standard assessment, or any strict completion claim. The strict
gate is a project-maturity condition, not a first-pass requirement.
<a id="project-maturity-dimensions"></a>
### Project Maturity Dimensions

Project maturity is measured across four concurrent dimensions, not as
sequential project phases. Every corridor pass advances the dimensions it
touches; project-wide assessment runs against all four at maturity.

- **Mechanical integrity:** parity, `strict_active_raw_lowaddr=0`,
  `strict_active_raw_absrom=0`, `pointer_targets.csv` and
  `branch_literal_sites.csv` synced, dynamic length/counter rewrites,
  `ZP_Tmp*` / `RAM_Tmp*` audited, warning-baseline hygiene, no
  placeholder alias churn.
- **Semantic coverage:** no unresolved `LXXXX` procedure labels, high-use
  RAM/ZP owners named consistently, procedure and data naming, pointer
  targets named, hardware aliases applied where touched.
- **Documentation quality:** procedure/global-label reports reviewed as
  inventories, retained comments earn their
  place under the minimality rule, no generic/filler data-label docs, system
  docs, memory map, and crosswalk current, stale prose cleaned up, one-blank-line
  procedure spacing, and `WORKING_NOTES.md` pruned/promoted under its maturity
  budget. Do not define maturity by driving comment-count metrics to zero.
- **Confidence closure:** inferred KPI at target, uncertain points scoped,
  scorecard refreshed, no half-populated rows, no indefinite `TBD` debt.

Semantic-claims maturity (`SEMANTIC_CLAIMS.md`) is a gold-closeout artifact, not
per-pass work: `project-maturity-check` runs `project-semantic-claims-check`
(strict on `SEMANTIC_CLAIMS_REQUIRED=1`, advisory for legacy). Update claims only
when a pass matures a subsystem — model and checker at
[QUALITY_REVIEW.md#semantic-claims](QUALITY_REVIEW.md#semantic-claims).

Framing rules:

- All applicable dimensions advance together within each corridor; do
  not run a dedicated repository-wide semantic, doc, or confidence pass.
- Targeted residual audits at project maturity are owned by
  [QUALITY_REVIEW.md](QUALITY_REVIEW.md). They may discover a new coherent
  corridor; they do not authorize blind repository-wide replacement.
- Pointer-byte consolidation: corridor-local trigger and recipes —
  [DATA_RECOVERY.md#computed-pointer-recovery](DATA_RECOVERY.md#computed-pointer-recovery);
  project-wide residual audit —
  [REVIEW_AUDITS.md#pointer-byte-consolidation-audit](REVIEW_AUDITS.md#pointer-byte-consolidation-audit).
- Do not leave placeholder inventory stubs in
  `docs/reverse_engineering/inventory/` after active work. The closeout
  helper sweeps authored ledgers (`raw_ram_review.csv`, `WORKING_NOTES.md`,
  scorecard rows) only for stale symbol references derived from the current
  pass's `renames.csv` rows; it does not detect generic placeholder stubs
  that were never tied to a renamed symbol. Check those manually as part of
  corridor closeout.
<a id="runtime-evidence-workflow"></a>
### Runtime evidence workflow

**Purpose.** Runtime analysis exists to improve the semantic names in the asm —
not to accumulate traces for their own sake. A capture is not finished when the
log is analyzed; it is finished when the confirmed finding is written back into
the disassembly. The trace/identity docs hold the evidence and confidence; the
asm must carry the conclusion. **Resolved identities or semantic conclusions
left docs-only are unfinished.**

**Feed the finding back by renaming, not by confidence comments.** Prefer
renaming the owning symbol to carry the identity (`UpdateWalkThrowActorState` ->
`UpdateKnifeThrowerState`, plus its `ACTOR_STATE_*` constant) over adding a
`; trace-confirmed` suffix comment. The rename ledger and trace docs carry
confidence and evidence; the asm should carry the semantic name.
Rename the actor's own handler/constant and leave shared machinery
(`PlayerActionContact*`, mechanism/system helpers) alone. Use a comment only
where there is no ownable symbol to rename (e.g. a boss name on a shared
`FLOOR_BOSS_ACTOR_STATE_*` constant). Keep medium-confidence or
behavior-specific detail in the trace docs.

When static analysis plateaus, create trace plan/runbook/scenario docs under
`docs/reverse_engineering/` with producers/consumers, signal, and promotion
criteria. If tooling is missing, adapt
`agent_playbook/templates/trace/` into project-local runner/logger/analyzer
files. Validate analyzers with a synthetic fixture before naming from captures.

Raw logs stay untracked; commit reduced evidence summaries and any resulting
semantic pass. Promote only after the analyzer accepts the scenario gate. See
[TOOLING.md#runtime-trace-tooling](TOOLING.md#runtime-trace-tooling) for the
trace tooling contract,
[QUALITY_REVIEW.md#static-vs-runtime-gaps](QUALITY_REVIEW.md#static-vs-runtime-gaps)
for promotion criteria, and
[REVIEW_AUDITS.md#deep-confidence-passes](REVIEW_AUDITS.md#deep-confidence-passes)
for the broader deep-confidence-pass framing.
<a id="completion-checklist"></a>
## Completion Checklist

### Pre-closeout requirements

Both items must be satisfied **before** running
`project-pass-closeout`, because the closeout helper reads
`renames.csv` to derive the set of old symbol names, then scans the
current on-disk authored docs for any remaining reference to them.

1. **Rename-ledger sync.** Every rename in the pass must have a
   matching row in `renames.csv`. Do not write placeholder rows when
   nothing was renamed. (Closeout's stale-symbol sweep is driven by
   these rows; missing entries mean missed stale references.)
2. **Raw-RAM rename closure.** For every `raw_$NNNN` row renamed in this
   pass, replace all executable numeric operands for that address with the new
   symbol or an approved scoped overlay. If mixed ownership blocks a complete
   sweep, leave the queue row unresolved with its evidence gap; do not record
   the rename as complete. Closeout enforces both; use `old_name=raw_$NNNN`.
3. **Docs stale-symbol preflight.** Grep authored docs for every
   old name listed in this pass's `renames.csv` rows and remove or
   rewrite each occurrence. The closeout sweep matches both
   backticked tokens (`` `OldName` ``) and bare-word occurrences
   (whole-word match), so historical mentions in plain text are
   flagged too — paraphrase the prose to avoid naming the old
   symbol, or restate the change in terms of the new name plus a
   pointer to the scorecard row.
### Post-closeout selection rule

After closeout succeeds, use this to pick the shape of the next pass:

4. **Select the next corridor from current maturity gaps.** Inspect
   project-wide maturity-dimension counters (semantic coverage,
   documentation quality, confidence closure, mechanical integrity) and
   pick a corridor whose closure advances the weakest dimension.
   Selection is by present maturity gap, not by a global project-phase
   transition.
<a id="generated-vs-authored-artifacts"></a>
## Generated Cache vs. Authored Artifacts

`make project-pass-prep PROJECT=<slug>` generates machine-readable
pass inputs under `docs/reverse_engineering/inventory/pass/`. These
files are generated cache, not authored documentation. They exist to
drive the next-pass briefing and reduce manual warm-up work.
Regenerate them whenever you start or resume a pass; do not treat
them as reviewable project artifacts or source-of-truth
documentation.
Cache contents and consumer guidance:

- `xref_with_data.json` is owner-enriched by default
  (`--xref-include-owner=true`); the owner-field consumer rule lives
  at [#session-resume → Owner-field rule](#session-resume).
- `next_pass.json` is the persisted output of the most recent
  `make project-next-pass PROJECT=<slug>` run — see
  [#next-pass](#next-pass) for its field shape.
- `current_pass_plan.json` / `current_pass_plan.md` are the persisted
  execution plan written by `make project-pass-start` — see
  [#current-pass-plan](#current-pass-plan) for the plan's structure
  and lifecycle.
<a id="pass-vs-commit"></a>
## Pass Versus Commit

A pass is a corridor outcome, not a commit. One corridor pass may span
several commits or edit batches when they serve the same corridor and keep
verification risk manageable. The `PROGRESS_SCORECARD.md` row records the
corridor result; it does not force every small mechanical commit into a
separate conceptual pass.

<a id="batching-and-commit-boundaries"></a>
## Batching, Rework, and Commit Boundaries

Define each batch by a coherent, parity-verifiable boundary — one
corridor, or one symbol/consumer family contained within one coherent
ownership corridor — sized so that `make project-verify` can run after
it. Rebuild and compare after each batch. Prioritize high-confidence
semantic transforms first (procedure or data ownership, behavior names,
necessary semantic contracts/invariants). Use mechanical transforms only when they directly
improve readability or unlock immediate semantic naming. Prefer a
semantic-first two-step flow within the batch:
1. semantic naming / pre-write comment admission / pre-existing prose cleanup / docs sweep
2. targeted mechanical normalization explicitly tied to semantic
   clarity

Corridor-scope caveats:

- Shared spelling or numeric value alone does not establish a corridor.
- A single script may implement a globally invariant token/value
  mapping, but execution, diff review, and parity verification must
  remain partitioned by ownership corridor — apply the mapping one
  corridor batch at a time and verify after each.
- Unrelated findings become separate plans or durable notes in
  `WORKING_NOTES.md`; they do not extend the current batch.

Do not defer obvious mechanical fixes to later ad-hoc passes.
### End-of-Batch Protocol

Every batch must conclude with:

1. **Unused-symbol closure gate** (unknowns and warnings closure):
   curate `WARNING_BASELINE.txt` so its intentional set matches the
   current build, then confirm `QUICK_REFERENCE.md`'s Assembler
   Warnings section still points at `WARNING_BASELINE.txt` as the
   single per-symbol registry — do not duplicate the symbol list
   into the quick reference. The unused-`.EQU` check
   (`--Werror=unused-equ`) is already invoked by
   `make project-verify`; do not run a separate xasm command.
   Do not keep or baseline a label whose only role is naming anonymous payload
   such as an inline return table consumed by `DispatchInlineJumpTable` or
   terminal CPU vector words. Remove the label and let the real owner be the
   callsite or fixed ROM address.
2. **Parity verification** (`make project-verify PROJECT=<slug>`).
3. **Inventory refresh** (`make project-inventory PROJECT=<slug>`).
4. **Scorecard update** (`PROGRESS_SCORECARD.md`).
5. **Reviewer simulation and readability self-audit** on the touched
   corridor. Apply
   [AGENTS.md#reviewer-simulation-checklist](../AGENTS.md#reviewer-simulation-checklist)
   and
   [REVIEW_AUDITS.md#readability-self-audit](REVIEW_AUDITS.md#readability-self-audit)
   before calling the pass complete. The scorecard row must name the
   corridor-level readability or semantic gain, not just KPI movement.
   Apply the comment admission test before writing each new comment; do not
   generate prose for later pruning. At closeout, confirm no newly authored
   comment bypassed that gate and review pre-existing touched comments for
   staleness. This is a safety net, not an authoring strategy. Documentation
   coverage gains do not justify filler.
6. **Related documentation updates** — terminology crosswalk, memory
   map, inventories, proven format docs, or `WORKING_NOTES.md`; see
   [DOCUMENTATION.md](DOCUMENTATION.md). Do not update `*_DX_Systems.md`
   merely because the pass touched a subsystem. Promote or revise that overview
   only when the subsystem clears
   [DOCUMENTATION.md#dx-systems-scope](DOCUMENTATION.md#dx-systems-scope).
7. **Closeout residue / lint gate**
   (`make project-pass-closeout PROJECT=<slug>`, optional `PASS=<id>`). Treat
   this as the authoritative stale-symbol sweep for authored ledgers
   too (`raw_ram_review.csv`, `WORKING_NOTES.md`, scorecard rows),
   not just Markdown docs.
8. **Final docs and process gates:**
   - `make project-docs-check PROJECT=<slug>`
   - `make project-process-check PROJECT=<slug>`
   - Ordinary batches stop here. Approaching **full project maturity**
     (every applicable dimension at
     [#project-maturity-dimensions](#project-maturity-dimensions)
     closed) additionally runs
     `make project-maturity-check PROJECT=<slug>`. The script is a
    hard-gate subset: it enforces zero raw-address debt
    (`strict_active_raw_lowaddr`, `strict_active_raw_absrom`), zero
    noncompliant data labels, and any reviewed table-span assertions in
    `data_extent_assertions.csv`. It reports no comment-quality conclusion;
     procedure/global-label coverage remains a human review inventory because
     a zero target rewards filler. It does not check `LXXXX`, parity, warning
     baseline, reviewer simulation, or confidence closure — those remain owned
     by earlier closeout steps and by
     [QUALITY_REVIEW.md](QUALITY_REVIEW.md). Full project maturity is
     the conjunction of all preceding closeout gates, this hard-gate
     subset, the static debt audit, and the QUALITY_REVIEW maturity assessment. The
     full combined gate (everything CI runs) is
     `make project-ci PROJECT=<slug>` — use it before merging or
     when a project-maturity exit + docs/process sequence is needed
     in one invocation.

For ordinary semantic passes, steps 7 and 8 may be replaced by
`make project-pass-finish PROJECT=<slug> PASS=<id> VERIFY_MODE=relaxed
FOCUS=<text> NOTES=<text>` while unresolved `LXXXX` labels remain. Use
`VERIFY_MODE=strict` once the project is ready for strict verification.
### Mass symbolization decision tree

**Corridor prerequisite.** Mass replacement is allowed only when the
replacement sites fall inside one coherent ownership corridor with a
proven single-domain mapping. Shared spelling or numeric value alone does
not authorize a repository-wide sweep. If the sites span unrelated
subsystems, split into separate corridor batches and record the
continuation plan in `WORKING_NOTES.md`.

When a batch faces many similar replacement sites inside one corridor,
choose the editing mode by the shape of the work:

- **Use individual edits when:**
  - the symbol is overloaded across unrelated meanings;
  - the touched sites are few enough to inspect one-by-one;
  - the pass includes nearby semantic cleanup and manual review is
    part of the point.
- **Use Perl-driven replacement when:**
  - the replacement is broad textual normalization across many
    instruction sites;
  - the old token has one meaning in the intended corridor;
  - the pass would otherwise be dominated by repetitive edit churn.
- **Perl is mandatory for large same-token replacement sweeps once
  the mapping is stable**, especially: raw-address-to-symbol
  replacement, repeated literal-to-constant replacement, and broad
  legacy-label rename sweeps.
- **Individual edits are mandatory when the same raw token/byte has
  multiple meanings** and no safe textual filter exists.

After any scripted replacement: inspect the diff, rerun parity, and
rerun the affected docs/inventory gates. The replacement mechanics
(Perl word-boundary patterns, leading-zero handling, `.EQU`
exclusion, replacement-impact gate, single-quoted `$` literals) live
at [TOOLING.md#script-hygiene](TOOLING.md#script-hygiene).
### Rename-only batch protocol

If a batch only renames existing labels / callsites / comments and
does not (a) add or remove symbols, (b) split tables or blobs, (c)
change pointer ownership, or (d) alter inventory-affecting structure,
the minimum required closeout is:

1. parity verification (`make project-verify`)
2. `renames.csv` update
3. `PROGRESS_SCORECARD.md` update
4. `make project-pass-closeout PROJECT=<slug>` (optional `PASS=<id>`)
5. `make project-docs-check PROJECT=<slug>`
6. `make project-process-check PROJECT=<slug>`

In this narrow case, `make project-inventory` is optional rather than
mandatory.
Exception: if generated inventory artifacts would otherwise retain
stale symbol names (for example `constants_catalog.csv` or other
name-bearing ledgers), run `make project-inventory PROJECT=<slug>`
before closing the batch even when the change was otherwise
rename-only.
### Review-fix commit protocol

When addressing reviewer findings after a closed pass, keep the fix
commit scoped to the finding unless the finding itself requires a
derived-artifact refresh. If you run `make project-inventory`,
`project-pass-prep`, `project-next-pass`, or any helper that rewrites
bulk inventory while making a targeted review fix, inspect the
generated diff and choose one of two outcomes: include the refresh only
when it is necessary to make the reviewed state accurate, and mention it
in the commit message; otherwise revert the unrelated generated drift
and land the reviewer fix alone. Rerun `project-pass-closeout`,
`project-docs-check`, and `project-process-check` after the final
review-fix edit, not before.
### Scorecard metric accuracy

Do not write estimated KPI counts in new scorecard rows. After the
pass is verified, recompute current counts and record the actual
end-state values for the batch. If counts are temporarily unknown
mid-edit, leave the scorecard update until after the verification
gate rather than guessing.
### Scorecard row hygiene

The new scorecard row for a pass must use only final symbol names
from that pass. Let `project-pass-closeout` rewrite supported derived
KPI cells rather than hand-entering counts from memory.
### Real-change reporting gate

Before reporting a pass as complete, confirm all are true:

1. authored project files changed in the target project (not only
   generated inventory artifacts)
2. the latest scorecard row exists for the reported `PASS`
3. the reported symbols are new work from that pass, not a
   restatement of the previous batch

Use `make project-pass-closeout PROJECT=<slug> PASS=<id>` as the
authoritative check for this gate. If the closeout helper does not
confirm materialized changes, do not describe the pass as completed.

Do not mention the old symbol name in the new row text; the row is a
forward-facing change summary, not a rename diff. If a semantic
correction replaces an earlier wrong name, rewrite the row using only
the final symbol name and behavior description.
