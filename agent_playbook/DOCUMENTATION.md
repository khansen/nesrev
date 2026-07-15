# DOCUMENTATION Playbook

This playbook is the canonical home for code-comment, system-documentation, and machine-readable documentation rules. The root `AGENTS.md` keeps only the high-level orchestration that triggers a doc sweep; the sections below carry the full rule text and cross-link to neighboring playbooks where another file owns a related rule.

## Ownership

This playbook owns prose, comments, and authored documentation artifacts:

- target-audience and onboarding scope
- comment quality and minimality
- declaration and procedure comments
- raw-address prose prohibition
- documentation artifact boundaries
- `*_DX_Systems.md` abstraction level
- `MEMORY_MAP.md`
- terminology crosswalk
- data-label format and usage comments
- data format documentation (canonical packed-format specification)
- `WORKING_NOTES.md` inclusion and pruning rules
- optional support-document rules
- reference-document use

Canonical ownership decisions:

- DX Systems scope lives only here.
- Comment rules live only here.
- [QUALITY_REVIEW.md](QUALITY_REVIEW.md) checks these rules but does not
  restate them.

## Playbook Sections

<a id="audience-contract"></a>
## Target Audience and Onboarding Scope

Assume the reader is a competent 6502 assembly programmer familiar with NES
CPU, PPU, APU, OAM, interrupt vectors, addressing modes, and common assembly
idioms. The codebase and its inline comments are not a 6502 or NES tutorial.

Onboard that programmer to this game: subsystem architecture, ownership,
control flow, invariants, project-specific hardware use, state machines, data
formats, and safe modification points. Explain standard platform behavior only
when this game uses it in a non-obvious, timing-sensitive, or unusual way.

Do not explain facts an experienced NES programmer can read directly from the
instructions and symbols. Examples that normally require no prose include what
`LDA`/`STA`/branches do, polling `PPUSTATUS` for VBlank, the fixed interrupt
vector order, ordinary OAM DMA page setup, and standard PPU/APU register
semantics. Prefer a semantic table/routine/field name over tutorial commentary.

<a id="comment-quality"></a>
## Comment Quality and Minimality

### Comment minimality rule (mandatory)

Comments are maintenance liabilities. The default is **do not write one**.
Apply this admission test before authoring any comment:

1. State the exact non-obvious, durable fact the comment would preserve.
2. Confirm that a semantic name, constant, label, data shape, or clearer code
   structure cannot express that fact.
3. Confirm that the fact matters at this code site rather than in a format doc,
   systems doc, ledger, or `WORKING_NOTES.md`.
4. Confirm that it teaches something project-specific rather than general
   6502/NES knowledge covered by [#audience-contract](#audience-contract).
5. Write only the shortest form that preserves that fact.

If any answer fails, do not write or generate the comment, even temporarily.
Improve names, symbolize literals/addresses, clarify structure before
deciding whether any comment remains necessary.

Useful comments preserve a non-obvious invariant, reason, interface contract,
side effect, hardware/timing constraint, parity oddity, alias ambiguity, or
locally important uncertainty.

Structural navigation is also useful when the instruction cannot carry the
symbol itself. For example, `INY ; SLOT_FIELD_POS_Y` identifies the field
reached by an adjacent-field walk; `INY` alone does not express that fact.
This is semantic structure, not narration of the increment.

Never author comments that:

- restate names, assignments, branches, loops, instruction sequences, source
  order, register moves, wrappers, addressing modes, or literal values
- cite an address/page/offset/mask/state that should be symbolic
- compensate for weak naming, incomplete symbolization, or KPI pressure
- annotate readable lines or basic blocks without adding a durable fact

If the proposed comment and code say the same thing, do not write it. If the
proposed comment explains a literal or address, symbolize the code instead.
When in doubt, do not write a comment.

### Existing-comment cleanup

The admission test governs new prose. Separately, when a pass encounters
pre-existing comments, remove or rewrite those that fail the same standard or
became stale after symbolization. This cleanup duty is not permission to
generate low-value comments during the current pass.

For procedure headers, keep only:

- a purpose not already clear from the procedure name
- important side effects or ordering constraints
- important inputs/outputs or calling constraints that callers cannot infer

For `.EQU` / declaration-site headers, keep only:

- the symbol's *role* (what it represents semantically — not what type of byte/word it is)
- overlay relationships when one address has multiple aliases serving different routines
- producer/consumer pointers when xref alone doesn't make them obvious
- constraints/invariants the symbol depends on

Common declaration failures are self-naming preambles, caller instruction
lists, addressing-mode paraphrases, mnemonic restatements, and tautological
`holds current ...` prose. If the name says it clearly, use no comment.

### General comment style

- Pseudo-code narration is not a default. Use it only for a genuinely
  non-obvious algorithm that clearer names and structure cannot make readable.
- Prefer one concise contract/invariant comment over line-by-line explanation.
- Do not write redundant summaries that repeat the procedure name.
- Keep one empty line between procedures; preserve inter-procedure spacing when normalizing comment blocks.
- Do not insert cosmetic blank lines before labels that are still part of active control flow (for example, branch targets/fallthrough labels). Only insert procedure-separator blank lines at true routine boundaries.
- Never leave placeholder documentation text (for example, "documented in brief" / "refine later"). If meaning is partial, write a concrete scoped comment and mark uncertainty with `inferred`.
<a id="declaration-comments"></a>
## Declaration Comments

### Declaration-Site Documentation Rule (Mandatory)

A semantic rename does not automatically permit or require a comment. Apply
[#comment-quality](#comment-quality) to public symbols and locals alike.

- For procedures: add a short contract header only when purpose, side effects,
  inputs/outputs, ordering, or public-entry role are not clear from the name
  and callers. Do not summarize the body.
- For nontrivial data tables/streams: add the minimal `Format:` / `Used by:`
  block required by [#data-label-format](#data-label-format). Scalars,
  self-explanatory constants, and obvious flat tables do not need prose merely
  because they were renamed.
- If a useful claim is partial, state only the proven subset and mark the
  uncertain semantic claim `inferred`. Otherwise leave documentation debt and
  record durable evidence gaps in `WORKING_NOTES.md`.

Procedure/global-label documentation KPIs measure header coverage, not quality.
Never add a tautological header to lower them. Prefer a nonzero count while
improving names, localization, or evidence.


### Caller-verified interface rule

When a declaration comment describes a routine's return value, output register, or flag contract, verify the claim against at least one caller site before committing the comment. Internal implementation details (e.g. a carry flag used mid-routine) may not match the actual interface callers depend on.
### Hygienic provenance comments

Declaration-site comments (e.g., `Used by:`) must not cite unresolved `LXXXX` labels as provenance. Use neutral subsystem descriptions or symbolic names only.
<a id="procedure-comments"></a>
## Procedure Comments

### Global code-label documentation

For every global label that introduces executable code:

- localize it if it is only a branch/fallthrough target inside one routine;
- add a useful concise contract/entry-role header when the retained public
  entry has a non-obvious contract; or
- leave it headerless when its semantic name and callers already convey the
  complete public role.

Localization is the default for branch-only labels. Before adding a comment solely to satisfy the global-code-label KPI, prove the label cannot be local: outside-scope branch, `JSR`/external `JMP`, jump/dispatch table target, BIT-overlay entry, scope barrier, or other real public entry role.
This includes reset/NMI/IRQ handlers, dispatch-table targets, externally jumped labels, and public branch targets that are intentionally kept global.

The global-code-label KPI complements the callable-procedure KPI. It catches code labels that are real public entry points but are not reached by `JSR`.

Do not satisfy this gate with restatements of the label name. If no useful public-role comment can be written, that is evidence the label should probably be local.
Comments such as "shared return", "done", "loop", "fallthrough", or "branch target" are not useful public-role comments. They are acceptable only when a scope barrier forces the label to remain global and the comment names the concrete parent/consumer relationship.

One header covers the procedure; do not narrate its body. Keep insufficiently
understood entries as explicit documentation debt. A deliberately headerless,
self-documenting public entry is not quality debt even when the KPI reports it.
<a id="raw-address-prohibition"></a>
## Raw-Address Prose Prohibition

Do not write raw RAM/ZP/ROM addresses, page values, field offsets, masks,
states, or counts in code comments when a semantic symbol can express them.
Prose such as `OAM DMA source page = $0200` or `flush when $52 != $53`
indicates incomplete symbolization.

Symbolize the operand, field, constant, range endpoint, or derived length
instead of authoring prose about the raw value. For pre-existing comments,
remove the raw-value narration unless it still carries a non-obvious invariant
or reason. Numeric text is appropriate only when numeric identity is the subject:
memory maps, hardware specs, format examples, parity encodings, or
address-sensitive behavior.

This rule is broader than `project-comment-audit`; that gate catches only
selected loud patterns. Human review must reject softer forms such as `at
$06`, `byte $19`, `[$E0/$E1]`, `slot+$10`, and `$04xx page`.

<a id="parity-bug-comments"></a>
## Parity-Preserved Bug Comments

When the disassembly preserves a ROM bug for binary parity, add an
inline comment at the code site that states:

1. **What is wrong** — the observable defect (off-by-one, wrong base
   address, swapped channels, etc.).
2. **Expected correct behavior** — what the routine should have done.
3. **Why current behavior is kept** — "preserved for ROM identity"
   (or similar parity language).
For the symbolic-expression encoding of the buggy value itself, see
[DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination).
For the registry expectation, see
[QUALITY_REVIEW.md#parity-bug-registry](QUALITY_REVIEW.md#parity-bug-registry).

<a id="documentation-artifacts"></a>
## Documentation Artifact Boundaries

### Required artifacts (core authored reverse-engineering documents)

Every active project must produce and maintain these core authored
reverse-engineering documents. The full canonical-artifacts list
(including build inputs, ledgers, and the terminology crosswalk) lives
at [AGENTS.md#canonical-artifacts](../AGENTS.md#canonical-artifacts).
1. **`<slug>_DX_Systems.md`** — a required path whose content is intentionally
   minimal until stable subsystem understanding exists. After promotion, it
   summarizes subsystem architecture, ownership, frame lifecycle, and links to
   mature format/state-machine docs. See [#dx-systems-scope](#dx-systems-scope).
2. **`docs/reverse_engineering/ONBOARDING.md`** — recommended learning path/curriculum; where to start, what to trace first.
3. **`docs/reverse_engineering/MEMORY_MAP.md`** — subsystem-grouped RAM/ZP map; see [#memory-map](#memory-map).
4. **`docs/reverse_engineering/QUICK_REFERENCE.md`** — single-page index of top labels/commands/docs.
5. **`docs/reverse_engineering/PROGRESS_SCORECARD.md`** — pass history, current KPI state, and high-signal pass outcomes.
6. **`docs/crosswalk/TERMINOLOGY_CROSSWALK.md`** — reference-vocabulary-to-asm-symbol mapping; created at intake, kept current. See [#terminology-crosswalk](#terminology-crosswalk).

### Maturity-time semantic-claims ledger

`SEMANTIC_CLAIMS.md` records final evidence-backed semantic conclusions for
gold-closeout cross-run comparison. `MEMORY_MAP.md` and data-format docs stay
canonical for navigation/layout; `*_DX_Systems.md` may link claims but must not
duplicate evidence; mechanical/write-only aliases are excluded unless they
explain a non-ownership decision. Model, scope, and checker:
[QUALITY_REVIEW.md#semantic-claims](QUALITY_REVIEW.md#semantic-claims).

### Optional support docs

Useful only when they add current workflow value:

- `ACTOR_ENUMS.md` (or equivalent): keep only when it documents a real state, action, or enum family better than declaration comments/systems docs.
- `PARITY_GAPS.md`: see [#support-documents → Priority file freshness](#support-documents) for retention rules.
- Trace plans/runbooks/scenarios: keep when unresolved work is genuinely runtime-gated and the docs define capture steps and promotion criteria.
- Reduced trace evidence docs: keep when a capture has promoted or rejected a
  semantic claim. Raw logs remain untracked unless curated as analyzer fixtures.
- Trace tooling docs: retain project-local runner/analyzer commands while they
  are useful for reproducing evidence or extending captures; prune stale
  capture-pending plans after their questions are resolved and the result has
  moved to the canonical state-machine, memory-map, scorecard, or semantic-claims
  home.

<a id="dx-systems-scope"></a>
## DX_Systems Abstraction Scope

System-level prose docs (`<slug>_DX_Systems.md` and dedicated format/state-machine
docs) capture *why*, *how*, and *how to use it*. Code labels and inline
comments capture *what*. The two are different deliverables — system-level
docs are not a byproduct of labeling.

### Promotion gate (mandatory)

Do not expand `*_DX_Systems.md` during intake or early semantic passes merely
because a corridor was touched. Keep the scaffolded file minimal until all of
the following are true for the subsystem being added:

- public routine/data names and RAM/ZP ownership are stable enough that the
  overview will not be rewritten by ordinary later symbolization;
- no unresolved `LXXXX` labels or raw RAM/ZP addresses are needed to explain it;
- producer/consumer boundaries and high-level control flow are proven;
- major data formats/state machines are understood enough to summarize or link
  to their dedicated docs; and
- the material is durable onboarding information, not a hypothesis, pass
  result, investigation trail, or next-pass plan.

Before promotion, route facts deliberately:

- pass result/provenance/KPI movement → `PROGRESS_SCORECARD.md` or inventories;
- stable RAM/ZP ownership → `MEMORY_MAP.md`;
- terminology mapping → `TERMINOLOGY_CROSSWALK.md`;
- proven packed format → declaration plus dedicated format doc;
- durable hypothesis, unresolved consumer, likely entry point, or future
  corridor → `WORKING_NOTES.md`.

Deferring the systems overview is the expected behavior until this gate is
met. Do not create speculative prose now with the expectation of cleaning it
up after later passes.

### Prioritization

1. **Prioritize documentation of moddable systems.** Any system where a user
   might edit data, create content, or modify behavior deserves standalone
   prose: levels/rooms/maps, object/actor/enemy behavior, item tables,
   music/SFX streams, sprites/metasprites/tiles, and PPU packet streams.

2. **Each major data format gets its own doc.** Do not bury format
   specifications inside `<slug>_DX_Systems.md`. Create files such as
   `ROOM_FORMAT.md`, `OBJECT_ACTOR_FORMAT.md`, `ENEMY_FORMAT.md`,
   `ITEM_FORMAT.md`, `METASPRITE_FORMAT.md`, `MUSIC_FORMAT.md`,
   `SFX_FORMAT.md`, or a shared `AUDIO_FORMAT.md` when one driver covers
   both music and SFX. The content checklist lives at
   [#data-format-documentation](#data-format-documentation). Add, when
   applicable:
   - Architecture overview (how the system's layers relate)
   - Data catalog (all segments/entries/patterns enumerated with purpose)
   - Tile/value ID reference table
   Audio is mandatory: document music/jingles and SFX/cues, including shared
   channel, instrument, envelope, or copied-state formats. If one cue/stream
   system covers both, say so explicitly.
3. **Core gameplay data families require disposition.** Before maturity, each
   present family needs a linked `*_FORMAT.md` doc or an explicit
   absent/unknown note: levels/rooms/maps; object/actor/enemy/hazard/
   projectile/item definitions; behavior/state/movement/animation streams;
   graphics/PPU formats; music and SFX cue/channel/instrument/effect-state
   formats. Closely coupled formats may share one doc, but every existing
   core family must be findable from the systems overview. New projects carry
   this as `docs/reverse_engineering/inventory/data_format_targets.csv`; keep
   that worklist current as families become documented, absent/not applicable,
   runtime-gated, or queued for a static pass. Maturity must not leave
   `not_yet_reviewed` or `queued_static_pass` rows.
4. **Each major state machine gets its own doc.** Create dedicated files (e.g., `RIDER_STATE_MACHINE.md`, `ENEMY_AI.md`) with:
   - State diagram (entry/exit conditions, per-frame behavior for each state)
   - Key variable reference table (address, name, purpose)
   - For scripted AI: command stream format, opcode catalog, worked example
5. **Include a modding guide for actionable formats.** If a format is user-editable (level data, character stats, track layouts), include step-by-step instructions for:
   - Editing existing ROM data (which bytes to change, what they mean)
   - Using in-game editors to create content and extracting it via RAM dump
   - Hand-composing new content from scratch using the format spec

6. **Keep the systems scaffold honest.** Before promotion, retain only a short
   statement that the overview is intentionally deferred pending stable
   subsystem understanding. Do not fill it incrementally. Once the promotion
   gate is met, replace that statement with a concise durable overview.

### Abstraction checklist (mandatory)

Use `*_DX_Systems.md` for stable subsystem understanding, not pass narration
and not helper-by-helper inventory.

Every mature systems doc should cover or explicitly mark not applicable:

- frame lifecycle / NMI ownership
- high-level gameplay control flow (what the per-frame gameplay updater owns)
- major subsystems: player/control, levels/rooms, objects/actors/enemies/
  hazards, items, projectiles/collision, rendering/PPU, audio, scoring/HUD,
  and setup flow
- music and SFX ownership: frame entries, request/cue flow, channel ownership,
  and links to music/SFX or shared audio format docs
- links to dedicated docs for present core formats: levels/rooms,
  objects/actors/enemies, items, projectiles, metasprites, animation,
  PPU streams, music, and SFX

Abstraction rules:

- do not cite unresolved `LXXXX` labels or use raw RAM/ZP addresses as a
  substitute for stable ownership names
- omit ordinary boot/reset mechanics, standard NES hardware sequences, and
  helper-level enable/disable wrappers unless they establish a project-specific
  architectural constraint
- do not include hypotheses, likely entry points, unresolved consumers,
  investigation status, future-pass plans, or queued work; those belong in
  `WORKING_NOTES.md`, the scorecard, or inventories
- prefer subsystem sections over narrow helper-family sections when several helpers are all parts of one larger flow
- keep routine names as anchors/examples, but do not turn the systems doc into a routine-by-routine changelog
- include enough data-format detail to make the subsystem editable, but move large or heavily modded formats into their own dedicated docs when they would overwhelm the systems overview
- if a section mostly says "routine X calls helper Y which calls helper Z", it is too low-level and should be compressed upward
- if a reader cannot tell the overall frame/update flow from the doc, it is too vague and needs one broader control-flow section

### Cross-reference between docs

System overview docs should link to detailed format/state-machine docs and
vice versa. Use relative markdown links (e.g.,
`[TRACK_DATA_FORMAT.md](TRACK_DATA_FORMAT.md)`).

<a id="machine-readable-doc-hygiene"></a>
## Machine-Readable Doc Hygiene

Prevents process regressions and "off-by-one" data-mapping errors when
authoring inventory ledgers, scorecard rows, and similar machine-readable
documentation.

### Safe multiline document edits

For `renames.csv`, markdown bullets, and scorecard rows:

- Do not use shell-constructed strings containing literal `\n` or variables.
- Do not use shell interpolation for text containing `$`.
- Prefer native file-edit tools (like `replace` or `write_file`) or `patch`.
- Rationale: shell expansion can mangle hex addresses (e.g., `$0203` becoming `bash203`) and literal newlines can corrupt CSV/Markdown structures.

`renames.csv` rule:

- Keep every ledger row to exactly 5 CSV fields:
  `old_name,new_name,reason,confidence,pass_id`
- If `reason` text contains commas, rewrite the prose or quote it correctly so the CSV shape stays valid.
- `old_name` must be symbol-shaped: an actual prior symbol, an `LXXXX`
  label, an `@@local` label, a `raw_$NN` / `raw_$NNNN` address key, or a
  specific synthetic `raw_*` key such as `raw_interrupt_vector_table`.
  Do not use plain lowercase prose words such as `vectors`; closeout treats
  old names as stale-symbol search keys.
- For partial overlay aliases, use `confidence=scoped-overlay`: unrelated raw
  operands may remain and the `raw_ram_review.csv` row stays active.
### Warning registry wording rule

In `QUICK_REFERENCE.md` under `## Intentional Assembler Warnings`, each
bullet must have exactly one leading warning symbol in backticks,
followed by plain-text rationale.
- Do not backtick unrelated symbol names later in the same warning bullet.
- Rationale: warning-registry sync treats the leading bullet symbol as the canonical warning entry; extra backticked symbols in the rationale create false drift.
### Cross-references for related machine-readable rules

- **Structured-listing requirement** (use `xasm --listing-format=json`, never parse text listings) lives at [TOOLING.md#xasm-options](TOOLING.md#xasm-options) — it's a tooling rule about how to use xasm output, not a documentation rule.
- **Verification claim semantics** — [Claimed-green verification rule](../AGENTS.md#safety-rules); per-batch closeout procedure at [PASS_WORKFLOW.md#pass-closeout](PASS_WORKFLOW.md#pass-closeout).
- **PPU packet header naming** (use raw hex `.DB $20, $70` for PPU address bytes; symbolic constants only for control-byte flags) lives at [DATA_RECOVERY.md#ppu-packet-streams](DATA_RECOVERY.md#ppu-packet-streams).

<a id="memory-map"></a>
## MEMORY_MAP.md

A living subsystem-grouped catalog of named RAM/ZP symbols.

- Update whenever new ZP/RAM symbols are named.
- Organize by subsystem (not by address order) so readers can find "all rider state" or "all audio variables" in one place.
- Each entry: symbol name, address, subsystem, role/semantics, and any overlay relationships.
- Describe what the symbol *is*, not which routines touch it (xref data goes in inventory snapshots, not the memory map).
<a id="terminology-crosswalk"></a>
## Terminology Crosswalk

`docs/crosswalk/TERMINOLOGY_CROSSWALK.md` maps reference-document
vocabulary (manuals, FAQs, design notes) to the project's asm symbol
names. It is created during intake, before any semantic renaming, and
kept current as the project matures.

Use these columns:

| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|

`Mapping confidence` rates the term-to-code mapping, not source
vocabulary. Before code evidence, leave symbols blank and use
`reference-only`; use `unmapped` when the concept boundary is unclear.
Reserve confidence levels for evidence-backed mappings, and consolidate
aliases for one concept into one row.

### Mandatory game-reference intake (project start gate)
- Before naming, review external sources in `docs/game_reference/`.
- Keep that tree external-only; authored extraction belongs in
  `docs/crosswalk/MANUAL_TERMS.md`.
- Create/update `docs/crosswalk/TERMINOLOGY_CROSSWALK.md` with canonical vocabulary and naming policy for the project.
- Do not start semantic renaming until this crosswalk exists (unless no reference docs are available; in that case record that explicitly in crosswalk notes).
- Confirm `make project-process-check PROJECT=<slug>` passes before the first semantic naming pass.

### Crosswalk synchronization protocol (mandatory)
Update `TERMINOLOGY_CROSSWALK.md` when:

- a manual/reference term gets a stable code mapping
- a project-specific code term replaces a generic placeholder
- an old unresolved terminology gap is now answered by current asm labels

Remove or rewrite stale `Open Terminology Gaps` entries once the code now
answers them. Do not leave resolved questions hanging as historical clutter.
Keep the crosswalk aligned with current asm and docs:

- reference concrete labels when a term is settled
- use `high` / `medium` / `inferred` in `Mapping confidence` only when
  code evidence supports the mapping
- prefer one current mapping over append-only history
If a term is still unresolved, say exactly what is missing (for example
"behavior exists but no dedicated enum name yet") instead of generic TODO
wording.

<a id="data-format-documentation"></a>
## Data Format Documentation

Canonical specification for packed data formats (stage blobs, audio
streams, PPU packets, scripted-AI command streams, etc.). The at-symbol
declaration pattern lives at [#data-label-format](#data-label-format);
the dedicated subsystem doc requirements live at
[#dx-systems-scope](#dx-systems-scope). This section defines what every
documented packed format must cover; the other two anchors point here
for the content checklist.

Every documented packed format must address each of the five items
below. When an item genuinely does not apply (for example a
fixed-size lookup table has no terminator, or an inert data table has
no parser routine), state `not applicable` and the one-line reason
rather than omitting the item.

1. **Exact byte order** — record/stream layout proven against producer
   and consumer, including endianness for multi-byte fields.
2. **Terminators and sentinels** — explicit byte values that end a
   record, list, or stream, plus any zero-record or zero-pointer
   conventions. Mark `not applicable` for fixed-size tables and
   constant-length records that are indexed rather than walked.
3. **Parser / decoder / indexing consumer** — the routine(s) that walk,
   decode, or index the bytes, plus the consumer routine(s) that act on
   the parsed values. Use the term that fits the access pattern
   (stream parser, packet decoder, table indexer).
4. **Constraints and failure modes** — observed bounds (max records,
   max stream length, value ranges) and assumed invariants. Describe
   failure behavior only when the code actually implements it; if the
   code is silent on out-of-range or truncated input, say so explicitly
   rather than inventing failure semantics.
5. **Worked byte-level example** — at least one real byte sequence from
   the ROM, annotated field-by-field, showing how the consumer
   interprets it.

For formats whose semantics are still partially open, document the
proven subset and mark only the unresolved clauses with `inferred`. Do
not defer a format doc to a later pass once the corridor has proven the
above — the format doc closes with the corridor that opens it; see
[High-Value Pass Contract](../AGENTS.md#high-value-pass-contract).

<a id="data-label-format"></a>
## Data-Label Format and Usage Comments

Declaration-site pattern for data labels (the at-symbol view of the
canonical specification at [#data-format-documentation](#data-format-documentation)):

```asm
; Format: 4-byte records [ppu_hi, ppu_lo, control, flags].
; Used by: QueueHudPacketByIndex, DrawPhaseHud.
HudPacketDescriptorTable:
```

Rules:

- `Format:` must state the minimal self-contained record/stream shape that is actually proven — record width, field order, and any sentinel/terminator the reader needs to scan the bytes locally.
- `Used by:` must name the consumer routine(s). `Consumer:` is also acceptable.
- `Used by: X through <dispatcher>` may name an indirect dispatcher (jump/pointer table or ZP pointer). The static xref cannot follow that indirection, so a missing direct reference is advisory, not a failure (hard only under `--strict`); a named consumer that is not a real symbol still hard-fails.
- If part of the format is still unresolved, document the proven subset and mark only the uncertain clause with `inferred`.
- Do not use filler text like "packed byte data block" or "used by gameplay/render/audio routines".
- When the same format also has a dedicated subsystem or format doc, keep the minimal shape inline and link out only for detailed semantics, constraints/failure modes, value catalogs, and worked examples. Do not replace the shape itself with a link.
<a id="working-notes"></a>
## WORKING_NOTES.md Inclusion and Pruning

`docs/reverse_engineering/WORKING_NOTES.md` is a durable project
scratchpad for reusable insights that should survive context compaction
but do not belong in `<slug>_DX_Systems.md`, `MEMORY_MAP.md`, or
`PROGRESS_SCORECARD.md`.
### Allowed content

- normalized record/base families and their aligned instances
- project-specific edit heuristics or "do not forget" notes
- durable analysis insights that may be useful in later passes
- tentative but useful working hypotheses, as long as they are labeled clearly
- likely subsystem entry points, unresolved consumers, and future-corridor
  hypotheses that are too provisional for `*_DX_Systems.md`

### Allowed properties

- editable and reorganizable when the notes materially improve future work
- compact, high-signal notes rather than polished end-user docs
- may contain both proven facts and clearly marked hypotheses
- reserved for notes that are likely to help later symbolization, constantization, data-format closure, or similar future analysis work
### Not allowed

Do not use `WORKING_NOTES.md` as a pass log, TODO dump, or substitute
for the systems doc. See
[Guiding Pass Philosophy](../AGENTS.md#guiding-pass-philosophy) for the
intended role.

Do not update it for routine micro-steps, pass-by-pass churn, or facts
that are already captured adequately in canonical docs or inventories.

### Next-pass plan override

When `WORKING_NOTES.md` contains a durable next-pass plan, it may
override the generated `project-next-pass` corridor scan. Persist that
choice explicitly with `project-pass-start`; do not rely on the
override living only in ad-hoc chat context.
### Pruning rule

- Remove or rewrite notes when they are no longer useful, have been superseded, or are now captured adequately in canonical docs/symbols.
- Do not treat `WORKING_NOTES.md` as an append-only history file.
- Prefer keeping a short current note over preserving stale context.
- New projects opt into a maturity-time `WORKING_NOTES.md` line budget enforced
  by `project-maturity-check`. If the gate trips, do not pad the budget first:
  promote stable facts to source, memory map, systems docs, semantic claims, or
  dedicated format docs; act on queued findings; then prune the notes to live
  forward-pass hazards and unresolved evidence gaps. Raise
  `MAX_MATURITY_WORKING_NOTES_LINES` only when the remaining notes are genuinely
  active and the scorecard explains why the larger budget is still needed.
<a id="support-documents"></a>
## Optional Support Documents

### Stub-doc lifecycle criteria (mandatory)

Keep a support doc only if at least one of these is true:
- it documents a live subsystem, enum family, debug workflow, or edit checklist that a contributor can use now
- another canonical doc meaningfully links to it for current project work
- it captures project-specific reference material that does not belong in systems/memory docs

Delete the file if it is only:

- a title plus one-line scaffold text
- a dormant TODO bucket with no current workflow value
- a duplicate of content already captured better elsewhere

For optional docs such as `ACTOR_ENUMS.md` or `WORKING_NOTES.md`:

- real content or deletion; no empty shells
For required docs such as `ONBOARDING.md`:

- replace scaffold text early with project-specific content
- docs-check should stay green against placeholder-doc detection
For optional support docs such as `PARITY_GAPS.md`:

- keep them only if they contain real current workflow value
- delete them when onboarding, systems docs, and working notes already cover the same ground better

For `CURIOSITIES.md` specifically:

- include only genuinely project-specific oddities such as ROM bugs,
  easter eggs/signatures, unreachable or apparently dead live-ROM code,
  unusual overlap/packing traps, or other behavior that would surprise an
  experienced NES programmer working on this game
- do not include ordinary platform idioms, common disassembly techniques,
  normal scoped overlays, inline jump tables, standard Zapper light sensing, or
  semantic gaps whose only issue is missing runtime/reference evidence
- if no entries meet that bar, omit the file

### Stale scaffold-era language

Stale scaffold-era wording is itself a failure state, even when the file
is no longer a one-line stub. Replace generic intake text (`fresh
scaffold`, `starter state`, generic "replace this later" guidance) as
soon as the project matures past intake.
### Priority file freshness
If `PARITY_GAPS.md` exists, keep it current. After completing a top item,
immediately update rankings. Remove resolved priorities. Distinguish
static vs runtime-pending semantics. Delete the file instead of
maintaining it if it no longer adds distinct value.

<a id="reference-document-use"></a>
## Reference-Document Use

### Active use of reference documentation (Critical)

- Game reference docs (manuals, guides, flyers) are mandatory inputs at project start, not optional. Review and crosswalk before semantic naming.
- Prefer canonical in-game/manual terms for symbol naming. Align names with documented terms unless code evidence contradicts.
- Log terminology-driven renames in crosswalk docs with confidence tags.
- Keep source material (`docs/game_reference/`), RE findings (`docs/reverse_engineering/`), and crosswalk (`docs/crosswalk/`) separated but linked.
- Resolve ambiguous labels by cross-checking both code behavior and reference docs.
### Reference stability

1. Prefer label-based references over line numbers in markdown docs.
   - Good: `RunAudioFrameMacros`
   - Avoid: `RunAudioFrameMacros` at line 8464
2. If a warning/quirk is tracked, include the symbol name and rationale, not only a line offset.
3. If line numbers are temporarily used during review, remove or refresh them before finalizing docs.
4. Avoid backticked stale/legacy symbol names after renames.
   - `project-docs-check` validates backticked symbols against current asm labels.
   - For historical notes, use plain text like `legacy LC94B` (not `` `LC94B` ``) unless the symbol still exists.
5. Avoid symbol-shaped placeholders in docs, even when not backticked.
   - Tokens like `LFCxx`, `LF??`, or `LCxxx` can be interpreted as unresolved symbol references by tooling/reviewers.
   - Prefer plain-language phrasing such as `legacy LFC-series flow labels`.
6. Backtick only concrete symbol names that exist in asm.
   - Do not backtick wildcard/suffix shorthand like `` `ZP_FOO_*` `` or `` `BASE_X/Y` ``.
   - If shorthand is needed, keep it plain text; reserve backticks for fully-resolvable symbol names.
7. Do not backtick config keys/tool variables in symbol-checked docs.
   - Examples: `MAX_UNDOCUMENTED_PROCEDURES`, `BRANCH_SITES_FILE`, `POINTER_TARGETS_FILE`.
   - Keep these as plain text unless they intentionally refer to asm symbols.
8. Scorecard/changelog entries follow the same symbol-check rules.
   - `PROGRESS_SCORECARD.md` and related pass-log docs are symbol-checked inputs.
   - Backtick only symbols that currently exist in asm.
   - Keep wildcard/pattern examples and legacy/removed names as plain text.
