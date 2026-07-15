# QUALITY_REVIEW Playbook

This playbook is the canonical home for the review *criteria*: the review quality
bar, gold-standard assessment, KPI interpretation, the semantic-claims ledger, the
parity bug registry, and static-versus-runtime gap classification. The concrete
audit *procedures* those criteria invoke live in
[REVIEW_AUDITS.md](REVIEW_AUDITS.md). The root `AGENTS.md` keeps the short
Reviewer Simulation Checklist.

## Ownership

This playbook owns post-pass and project-level review criteria:

- review quality bar and success-evaluation criteria
- gold-standard assessment
- KPI interpretation and limitations
- semantic-claims ledger (maturity/gold-closeout evidence model)
- parity bug registry
- static-versus-runtime-gated gap classification

The audit procedures those criteria invoke (readability self-audit, reviewer
simulation, stale-placeholder / symbol-family / residual-magic / global-label
audits, static readability debt audit, pointer-byte consolidation, deep-confidence
passes) live in [REVIEW_AUDITS.md](REVIEW_AUDITS.md). Quality checks may link to
rules in other playbooks but do not redefine them.

## Playbook Sections

<a id="quality-review"></a>
## Review Quality Bar (Overview)

Completion semantics are strict. Green process gates mean the
project is mechanically mature; they do not mean the project is
done. Do not describe a project as "done" unless the gold-standard
checklist at [#gold-standard-assessment](#gold-standard-assessment)
has been explicitly audited after the final edit batch, or unless
remaining gaps are documented and the user has chosen to move on.
A project round is successful when both are true:
1. **Technical completeness.** The gold-standard checklist at
   [#gold-standard-assessment](#gold-standard-assessment) is
   satisfied; `make project-verify PROJECT=<slug>` and
   `make project-docs-check PROJECT=<slug>` pass; the readability
   self-audit at [#readability-self-audit](REVIEW_AUDITS.md#readability-self-audit)
   has been completed on touched regions.
2. **Process efficiency.** The execution scorecard at
   [PASS_WORKFLOW.md#scorecard-sync](PASS_WORKFLOW.md#scorecard-sync)
   is updated; pass count and rework rate are within target, or
   deviations are explained with corrective action; at least one
   new preventive rule or check is added when recurring misses are
   discovered.

<a id="gold-standard-assessment"></a>
## Gold-Standard Assessment

The checklist below is the standing definition of "gold standard"
for a finished project round. Items are grouped by what enforces
them so the reviewer knows where to look first.

### Machine-checkable gates

These items have process gates that fail loudly when violated. A
green `make project-verify` only proves that *configured* KPI
ceilings are met, which on permissive projects (`MAX_* = 999999`)
can hide substantial debt. Use `make project-maturity-check
PROJECT=<slug>` (project-wide only) for the raw-address and
data-label hard-gate subset, and read other KPI output as review
inventory rather than assuming every count should be zero.

1. **No remaining opaque `LXXXX` procedure labels.** Verified by
   `make project-verify PROJECT=<slug>` with
   `ALLOW_UNRESOLVED_LXXXX` unset — this is the only gate that
   covers `LXXXX`. `project-maturity-check` does not inspect
   `LXXXX` and must not be used as the confirmation here.
2. **Build passes and binary identity preserved** for
   refactor/doc passes — `make project-verify PROJECT=<slug>`.
3. **Data-label doc coverage actually zero.** The KPI is tracked
   by `data_label_doc_kpi.sh` (`MAX_UNDOCUMENTED_DATA_LABELS` —
   see [PASS_WORKFLOW.md#scorecard-sync](PASS_WORKFLOW.md#scorecard-sync)),
   but for the gold-standard floor, require the underlying
   `strict_data_labels_noncompliant` count to equal zero — exactly
   what `project-maturity-check` enforces.
### Human-review items

These items have only partial KPI coverage or none at all; the
reviewer must inspect the touched regions and ledgers.

4. **Callable/global code-label reports are reviewed, not mechanically
   driven to zero.** Use `procedure_doc_kpi.sh` and
   `global_code_label_doc_kpi.sh` to find review candidates. Localize
   internal labels, improve weak names, and add a header only when it
   preserves a useful non-obvious contract or public-entry role. A
   self-documenting retained public label may remain headerless; the count is
   an inventory, not a quality score. **Near gold, zero documented code
   contracts is a process failure unless the scorecard records the audit.**
   New projects opt into `PROCEDURE_CONTRACTS_REQUIRED=1` for this tripwire.
   Legacy gold predating these tripwires is stale until a scorecard row records
   the marker in
   [PASS_WORKFLOW.md#legacy-retrofit-scorecard-artifact](PASS_WORKFLOW.md#legacy-retrofit-scorecard-artifact);
   zero-undocumented retrofit is not required.
5. **Comment quality beats coverage.** No line-by-line narration, literal
   translations, raw-address prose, or tautological headers were added to make
   a KPI green. Review the changed comments manually against
   [DOCUMENTATION.md#comment-quality](DOCUMENTATION.md#comment-quality).
6. **No remaining placeholder `Data_XXXX` labels** (unless
   intentionally unresolved and explicitly documented). No KPI
   script currently flags placeholder data-label names, so grep
   the inventory and asm manually.
7. **High-impact runtime routines expose useful contracts where needed.**
   Comments are not required when semantic names and callers already make the
   contract clear. Any retained header must add non-obvious purpose, side
   effects, inputs/outputs, ordering, or public-entry semantics; walkthroughs
   and KPI filler fail this item. Review high-fanout callables and public
   jump/dispatch targets from `xref_summary_all.json`; localize,
   rename/structure, add a concise header, or record why none is needed.
8. **Major data regions have dedicated format coverage.** Inline `Format:`
   comments are not enough for core editable systems. If the game has
   levels/stages/rooms/maps, objects/actors/enemies/hazards,
   items/pickups, projectiles, metasprites/animation, PPU packet/update
   streams, music, SFX, or shared audio cue/channel formats, those families
   must have dedicated `*_FORMAT.md` docs or one clearly scoped shared doc
   such as `AUDIO_FORMAT.md` that explicitly covers both music and SFX.
   If a family is absent or not yet statically understood, record that
   disposition instead of leaving the silence ambiguous. New projects record
   these dispositions in `inventory/data_format_targets.csv`; the maturity
   check rejects undispositioned or still-queued rows. When a review proves
   a bounded indexed-table span that ordinary coverage cannot infer, record it
   in `data_extent_assertions.csv` so `project-verify` and
   `project-maturity-check` can catch later drift.
9. **Onboarding docs are complete and cross-linked**
   (`ONBOARDING.md`, `QUICK_REFERENCE.md`, `MEMORY_MAP.md`,
   dedicated format/state-machine docs, and promoted subsystem
   `*_DX_Systems.md`). A not-yet-promoted systems
   scaffold is acceptable while semantic work remains; speculative expansion
   is not. New projects opt into a maturity budget for `WORKING_NOTES.md`; if
   the file is over budget, promote stable facts to canonical docs/source, act
   on queued findings, and prune it before claiming maturity. A larger
   configured budget is acceptable only with a scorecard rationale that the
   remaining notes are active forward-pass hazards or unresolved evidence gaps.
10. **Known parity-preserved bugs are documented both inline and in
    docs.** Inline-comment format at
    [DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments);
    registry at [#parity-bug-registry](#parity-bug-registry).
11. **If `PARITY_GAPS.md` exists, it reflects the actual next
    highest-value item.** No stale completed priorities.
12. **No avoidable hardcoded pointer low/high literals** where
    `#<Symbol` / `#>Symbol` would work.
13. **No avoidable hardcoded indirect-address operands** where
    symbolic pointer names exist.
14. **No avoidable raw structured-field offsets** in executable
    logic when pointer shape is known (`LDY #$NN` near slot/record
    pointers, adjacent `INY` field walks without field-name comments,
    etc.). Prefer symbolic fields and readable structure; when byte-saving
    `INY` replaces a symbolic `LDY`, comment the field reached after each
    meaningful increment because the instruction has no symbolic operand.
15. **No stale raw-address comments** when a stable symbol exists.
    Prefer symbol names over raw-address prose unless the numeric address
    itself is the semantic fact; canonical examples live at
    [DOCUMENTATION.md#raw-address-prohibition](DOCUMENTATION.md#raw-address-prohibition).
16. **No address-coded or value-coded placeholder labels** when a
    semantic name is known. Names like `...Page0480...`,
    `...AddrC000...`, or `...Field10...` are acceptable only when
    the address/value identity is the durable meaning or the
    placeholder is explicitly recorded as future debt.
17. **No obvious derivable counts/bounds or table offsets**
    remain raw when label math is clearer. This includes selector/request
    `.DB $NN` offsets to known labels; use `TargetLabel-BaseLabel`.
18. **Systems-overview promotion and abstraction are correct.**
    `*_DX_Systems.md` remains minimal until stable names, ownership, control
    flow, and format boundaries exist. A promoted overview contains no
    unresolved `LXXXX`, raw RAM/ZP inventory, boot-step walkthrough,
    helper-by-helper narration, hypotheses, or future-pass planning. Route
    provisional material to `WORKING_NOTES.md` or process artifacts and link
    detailed formats/state machines instead of embedding them. For games
    that have levels/stages/rooms, objects/actors/enemies, items/pickups,
    projectiles, rendering packet streams, music, or SFX, the overview must
    mention those systems at the architectural level and link the relevant
    dedicated format docs or an explicit not-applicable/disposition note.
### Final readability sweep

19. Run a final readability audit using targeted searches plus
    local review of surrounding code, not only generated KPI
    output. Source the project config first so `${ASM_FILE}` and
    `${DOC_ROOT}` resolve to the active project:

```sh
# Load ASM_FILE / DOC_ROOT for the active project
source scripts/project_common.sh && load_project_conf <slug>

# Hardcoded LDY # operand sites that may need field-name math
rg -n "LDY #\\$[0-9A-F]{2}" "${ASM_FILE}"

# Stale raw-address citations in code and project docs
rg -n "slot\\+\\$|\\[\\$|\\$[0-9A-F]{4} page" "${ASM_FILE}" "${DOC_ROOT}"

# Address- or value-coded placeholder labels
rg -n "Page[0-9A-F]{2,4}|Addr[0-9A-F]{4}|Field[0-9A-F]{2}" "${ASM_FILE}" "${DOC_ROOT}"
```

    Treat findings as cleanup candidates, not automatic
    replacements.

20. Before any gold claim, run the positive procedure-contract audit: use
    `project-pass-prep`, inspect `xref_summary_all.json` high-fanout callables
    and jump targets, and compare with the procedure/global-label KPI reports.
    If no mature-project headers result, the scorecard must name what was
    reviewed and why names/callers were sufficient.
21. Before any claim that static work is "done" or exhausted, run the
    [core data-format coverage audit](REVIEW_AUDITS.md#core-data-format-coverage-audit)
    and
    [static readability debt audit](REVIEW_AUDITS.md#static-readability-debt-audit),
    then record dispositions in the scorecard. A green gate set without these
    audits is a mechanical-maturity statement only, not a static-quality
    conclusion.

<a id="semantic-claims"></a>
## Semantic Claims Ledger

`docs/reverse_engineering/SEMANTIC_CLAIMS.md` is a maturity-time ledger of major
evidence-backed semantic conclusions. Its purpose is cross-run comparison: two
clean-room projects can both pass KPI gates yet make different semantic claims
(wrong RAM owner, misread state value, wrong producer/consumer), and this ledger
makes that difference auditable by meaning rather than symbol spelling.

It is a gold-closeout artifact, not per-pass ceremony — a pass updates claims
only when it matures a subsystem; most passes touch nothing here. It does not
replace [DOCUMENTATION.md#memory-map](DOCUMENTATION.md#memory-map), data-format
docs, `raw_ram_review.csv`, `renames.csv`, or `*_DX_Systems.md`; those stay
canonical for navigation, layout, queue status, and overview.

**Claim shape.** Each claim is a stable review unit headed `## Claim: <slug>`
(a semantic slug, not a symbol name, so renames do not break comparison) with
fields `Subject`, `Kind`, `Subsystem`, `Claim`, `Confidence`, `Evidence`,
`Caveats`, `Canonical docs`. `Kind` is one of: RAM/ZP field, scoped overlay,
state machine, state value, data format, pointer table, routine contract,
subsystem, other. `Confidence` is one of: high, medium, inferred, mechanical.

**Scope.** Claim the major, contested, or likely-to-vary conclusions: RAM/ZP
ownership families, nontrivial scoped overlays, state bytes and their values,
data formats / packet streams / pointer tables / record families, and subsystem
entry points. Exclude purely mechanical write-only aliases and still-`unreviewed`
/ `deferred` raw-RAM rows; record a non-ownership decision in the ledger that
owns it (`raw_ram_review.csv` or `WORKING_NOTES.md`), not as a full claim. Use
`Confidence: mechanical` only to justify such an explicit exclusion.

**Validation.** `make project-semantic-claims-check PROJECT=<slug>` validates
structure and links only: unique headings, required fields, allowed Kind and
Confidence, real (or `External/reference-only`) subjects, and resolving local
doc links. It does not prove claims; evidence quality stays reviewer judgment.
The pass-time check allows a sparse (zero-claim) ledger. `project-maturity-check`
runs it in maturity mode for opted-in projects (`SEMANTIC_CLAIMS_REQUIRED=1`),
which additionally requires at least one claim at gold closeout; legacy projects
are advisory.
<a id="kpi-interpretation"></a>
## KPI Interpretation and Limitations

KPI gates measure mechanical compliance; they do not measure how
the file reads. Even with every machine gate green, additional
passes routinely surface real readability debt the gates cannot
see: stale prose, verbose declaration comments, partially
symbolized state machines, self-naming `.EQU` headers. Treat the
KPI suite as a floor, not a ceiling.
- A green `make project-verify` is necessary but not sufficient.
- KPI burn-down (MAX_ACTIVE_MAGIC_IMMEDIATES,
  MAX_INFERRED_ANNOTATIONS, MAX_PLACEHOLDER_COMMENTS,
  MAX_UNDOCUMENTED_DATA_LABELS) is a measurement outcome, not a
  pass objective.
- Specific KPI definitions and burn-down targets live at
  [PASS_WORKFLOW.md#scorecard-sync](PASS_WORKFLOW.md#scorecard-sync);
  this section governs how to interpret them, not how to track
  them.
- The human-review items above and the readability self-audit
  below catch what the KPI suite cannot.
Calibration: never set `MAX_*` values while known undecoded `.DB`
blobs exist; complete code-pointer recovery and blob decode first.
Normalize hex widths before calibrating. Mark provisional baselines
explicitly so they don't masquerade as a true gold-standard floor.

<a id="parity-bug-registry"></a>
## Parity Bug Registry

When the project preserves ROM bugs for binary identity, keep a short
running registry of those bugs in `QUICK_REFERENCE.md`. Each entry
should name the owning symbol (routine, label, or data table) and
summarize the defect in one line; the detailed explanation belongs to
the inline parity-bug comment at the code site, not to the registry.
The inline-comment format lives at
[DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments);
the code-site expression encoding lives at
[DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination).

### Registry review

Walk `QUICK_REFERENCE.md`'s parity-bug section at every closeout
covered by [#reviewer-simulation](REVIEW_AUDITS.md#reviewer-simulation):

- Confirm each registry entry still resolves to a live code-site
  comment using the new symbol name. `project-pass-closeout`
  recursively scans authored docs under `${DOC_ROOT}` (which
  includes `QUICK_REFERENCE.md`) and catches old symbol names
  drifting in registry text from the current pass's renames, but
  it cannot validate the registry's semantics or whether each
  entry still links to the right inline comment — that part is
  this review.
- Promote entries whose root cause has been proven (the parity
  preservation stays, but the "unknown why" qualifier comes off).
  See [#static-vs-runtime-gaps](#static-vs-runtime-gaps) for the
  confidence-promotion workflow.
- Retire entries whose underlying defect was fixed by a
  non-parity-preserving change (the registry is for parity-held
  bugs, not historical anecdotes).
<a id="static-vs-runtime-gaps"></a>
## Static vs. Runtime-Gated Gap Classification

Static analysis eventually plateaus. Classify each residual uncertainty,
schedule the right capture, and promote confidence only after evidence lands.

### Confidence promotion criteria
- `high confidence (static)` = control/data flow proves correctness.
- `high confidence (runtime)` = repeated trace evidence.
- If runtime frequency unknown, document as "statically reachable; runtime
  frequency pending."

The root [AGENTS.md#confidence-protocol](../AGENTS.md#confidence-protocol)
defines the `high` / `medium` / `inferred` semantics; the
(static)/(runtime) qualifier above scopes the evidence channel.

### Operational classification procedure

For each unresolved item (`inferred`, `WORKING_NOTES.md`, incomplete symbol
family, or unknown-root parity bug):
1. **Identify the gap source.** Check remaining `inferred` annotations
   (`rg -n 'inferred' "${ASM_FILE}" "${DOC_ROOT}"`), `WORKING_NOTES.md`, and
   parity-bug registry entries whose root cause is unknown.
2. **Classify the gap as static or runtime.**
   - **Static-resolvable.** Required control/data-flow evidence exists in asm
     (call tracing, pointer-table resolution, structured-field offset proof).
     Keep it in `WORKING_NOTES.md` for the next
     [#reviewer-simulation](REVIEW_AUDITS.md#reviewer-simulation) pass.
   - **Runtime-gated.** The value depends on live input, RNG, timing, scenario
     state, or external emulator-visible state. Move it from `WORKING_NOTES.md`
     into a trace plan.
3. **Schedule the evidence capture.** For runtime-gated gaps,
   author a trace plan under
   `docs/reverse_engineering/` (capture runbook + scenario + the
   producer/consumer label pair under observation) per
   [PASS_WORKFLOW.md#pass-closeout → Runtime evidence workflow](PASS_WORKFLOW.md#pass-closeout).
   Each trace plan names the expected signal and promotion criteria. If no
   harness exists, create one from
   [TOOLING.md#runtime-trace-tooling](TOOLING.md#runtime-trace-tooling)
   and `agent_playbook/templates/trace/`: project-local runner, Lua
   logger, analyzer, synthetic fixture, and quick-reference command.
   If reaching the scenario is itself the bottleneck, use a
   [trace helper ROM](TOOLING.md#trace-helper-roms) to shorten setup while
   preserving the tested path. Raw captures and local helper mods stay
   untracked unless curated; commit the reduced transition/result summary.
4. **Promote confidence on capture.** Once evidence lands, apply
   the [Confidence Protocol](../AGENTS.md#confidence-protocol)
   promotion sweep: revisit prior `inferred` annotations, drop
   the tag where the evidence now proves the role, preserve any
   explanatory comment (drop the uncertainty marker, not the
   documentation). The analyzer must explicitly accept the scenario
   gate/milestones before the capture can justify names. A single
   capture only supports the level warranted: one agreeing trace can justify
   `medium confidence (runtime)`; `high confidence (runtime)` requires repeated
   traces across scenarios. Do not promote before capture.
5. **Close the loop.** Move the captured item out of
   `WORKING_NOTES.md` and into the canonical home:
   - parity-preserved bugs with root cause now known →
     [#parity-bug-registry](#parity-bug-registry) (registry
     entry) + [DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments)
     (inline);
   - symbol-family members now identified → asm renames via the
     [PASS_WORKFLOW.md#batching-and-commit-boundaries](PASS_WORKFLOW.md#batching-and-commit-boundaries)
     End-of-Batch Protocol;
   - state-machine transition matrices → a dedicated subsystem
     state-machine document under `docs/reverse_engineering/`,
     not the `*_DX_Systems.md` overview. Per
     [DOCUMENTATION.md#dx-systems-scope](DOCUMENTATION.md#dx-systems-scope),
     DX Systems retains only subsystem-level summaries; major
     state machines belong in dedicated docs.
