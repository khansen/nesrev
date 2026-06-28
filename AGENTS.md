<a id="preamble"></a>
# Disassembly Documentation Playbook (Reusable)

This file defines a repeatable process for taking a raw NES 6502 disassembly and turning it into a high-confidence, developer-friendly codebase with solid onboarding docs.


<a id="mandatory-routing-table"></a>
## Mandatory Routing Table

Authoritative bundle map. Load the listed playbooks before substantial work. Cross-task contracts live at root — Mission, Non-Negotiable Safety Rules, Guiding Pass Philosophy, High-Value Pass Contract, Reviewer Simulation Checklist, Prior-Project Reuse Gate, Session Orientation, Naming Conventions, Confidence Protocol, Corridor Execution Contract, and Output Philosophy. Everything else lives in the playbooks under `agent_playbook/`; the [Specialized Rule Index](#specialized-rule-index) at the bottom maps topic-specific rules to their canonical home.
| Task | Mandatory playbooks |
|---|---|
| Start a new project | `NEW_PROJECT.md`, `PASS_WORKFLOW.md`, `DATA_RECOVERY.md`, `ASM_STYLE.md`, `DOCUMENTATION.md` |
| Resume or perform a semantic pass | `PASS_WORKFLOW.md`, `ASM_STYLE.md`, `QUALITY_REVIEW.md` |
| Recover hidden code or dispatch | `DATA_RECOVERY.md`, `TOOLING.md`, `ASM_STYLE.md` |
| Reformat or interpret data tables/streams | `DATA_RECOVERY.md`, `ASM_STYLE.md`, `DOCUMENTATION.md` |
| Symbolize RAM/ZP or state machines | `PASS_WORKFLOW.md`, `ASM_STYLE.md`, `DOCUMENTATION.md` |
| Constantize magic numbers, offsets, bounds, or hardware masks | `ASM_STYLE.md`, `DATA_RECOVERY.md`, `DOCUMENTATION.md` |
| Review or rewrite comments/docs | `DOCUMENTATION.md`, `QUALITY_REVIEW.md` |
| Assess gold-standard maturity | `QUALITY_REVIEW.md`, `DOCUMENTATION.md`, `ASM_STYLE.md` |
| Change NESrev, xasm, wrappers, or quality gates | `TOOLING.md`, `QUALITY_REVIEW.md` |
| Create or review a mod | `ASM_STYLE.md`, `PASS_WORKFLOW.md`, `TOOLING.md` |

Subsystem-specific playbooks discovered during a task must also be loaded — e.g. a semantic pass that opens a structured PPU packet stream must additionally load [`DATA_RECOVERY.md`](agent_playbook/DATA_RECOVERY.md).
<a id="guiding-pass-philosophy"></a>
## Guiding Pass Philosophy

Keep these principles in mind for every project and every pass:

- **Optimize for gold-standard quality in as few passes as possible.** Prefer broader, coherent passes that close a real subsystem slice over narrow busy-work passes.
- **Perfect is the enemy of good.** If a name is high-confidence and not misleading, use it now. Refine later only when new evidence materially improves it.
- **Placeholder names must stay traceable.** If you temporarily use an address-bearing or similarly structural placeholder name because semantics are not closed yet, record in `WORKING_NOTES.md` that it is a placeholder and should be revisited later. Do not let temporary naming silently fossilize. Expanded rule — [ASM_STYLE.md#placeholder-policy](agent_playbook/ASM_STYLE.md#placeholder-policy).
- **Reuse established NESrev knowledge aggressively.** Bring forward proven patterns from earlier projects: common NMI/layout structure, PPU packet formats, audio/data stream conventions, actor/update families, and known Nintendo naming idioms. Do not rediscover familiar patterns from scratch unless the new project contradicts them.
- **Do semantic cleanup opportunistically in the same pass.** If a label pass also proves nearby RAM/ZP roles, constants, pointer targets, or local label scopes, clean them up immediately instead of deferring obvious follow-up debt.
- **Semantic-first naming priority (mandatory).** High-confidence semantic changes come before mechanical KPI-only edits. Do not run broad placeholder alias sweeps (e.g. `ZP_XX`, `RAM_XXXX`) whose primary purpose is lowering KPI counts. Mechanical symbolization is allowed only when it immediately enables semantic naming in the same pass or a specifically linked next pass whose continuation is recorded in the current pass plan or `WORKING_NOTES.md`. Address-bearing names are short-term structural placeholders only; durable revisit notes go in `WORKING_NOTES.md`. Expanded rule — [ASM_STYLE.md#placeholder-policy](agent_playbook/ASM_STYLE.md#placeholder-policy).
- **Symbolize hardware semantics immediately when touched.** When a pass touches NES I/O register usage or their shadow/control bitmasks, replace raw hardware addresses and raw bitmasks with the canonical aliases in the same pass instead of leaving easy hardware cleanup behind.
- **Do not over-name shared scratch from local evidence alone.** A locally obvious helper role does not automatically justify a stable global `ZP_*` / `RAM_*` name. Prefer broader ownership proof, existing family alignment, or a durable `WORKING_NOTES.md` note over premature symbol churn.
- **Close known data formats while the blob is open.** If a data blob's structure is known, document the format and reflow the bytes into logical record-sized `.DB` / `.DW` lines in the same pass. Do not leave long byte runs once record, row, packet, pointer, or sentinel boundaries are known. If the structure is not yet known well enough to justify reformatting, leave the bytes parity-preserved and record a durable revisit note in `WORKING_NOTES.md` rather than silently walking away.
- **Localize when scope is clear.** Do not leave helper-internal labels global unless shared control flow really requires it. Avoid spending later passes on avoidable localization cleanup.
- **Use `WORKING_NOTES.md` as durable memory, not a work log.** Capture reusable discoveries, corridor-level theories, and future-pass hints there when they are worth preserving, and prune stale notes promptly.
- **Defer systems-doc promotion until understanding is stable.** Early and mid-pass findings belong in the scorecard, ledgers, `MEMORY_MAP.md`, crosswalk, dedicated proven-format docs, or `WORKING_NOTES.md`. Keep `*_DX_Systems.md` minimal until the subsystem's public names, ownership, control flow, and major formats are stable enough to survive later passes. Then write only the durable subsystem overview; never use it for unresolved labels, raw-address inventories, helper walkthroughs, boot-step narration, hypotheses, or future-pass plans. Canonical maturity and scope rule — [DOCUMENTATION.md#dx-systems-scope](agent_playbook/DOCUMENTATION.md#dx-systems-scope).
- **Write for an experienced NES programmer.** Audience and onboarding scope — [DOCUMENTATION.md#audience-contract](agent_playbook/DOCUMENTATION.md#audience-contract).
- **KPIs measure mechanical maturity, not readability.** Every KPI gate (raw-address audit, doc-coverage, LXXXX count, comment-quality, etc.) can be green while a region still reads badly: verbose declaration comments that restate the symbol being defined, prose that paraphrases addressing modes, stale raw-address citations next to newly symbolized names, partially symbolized state machines that name half the values, generic placeholder text that satisfies the gate's regex but tells the reader nothing. Treat green gates as a floor, not a finish line. After each pass, read the touched region as a stranger would and ask "does this read better than before, or just compliantly?" See [Readability Self-Audit](#readability-self-audit).
- **Comments require pre-approval by value.** Before writing any comment, identify the exact non-obvious fact it preserves and why symbols or structure cannot express it. If that answer is absent, do not write the comment, even temporarily. Never generate narration for later cleanup or comment instead of symbolizing. Documentation KPI debt is preferable to filler. Canonical rule — [DOCUMENTATION.md#comment-quality](agent_playbook/DOCUMENTATION.md#comment-quality).
- **Symbolization triggers a prose sweep in the same pass.** Any pass that introduces, renames, or promotes a `ZP_*` / `RAM_*` / `OBJECT_SLOT_FIELD_*` / `*_STATE_*` / hardware-mask symbol must, in the same edit batch, grep nearby comments and docs for stale raw-address prose matching the canonical examples in [DOCUMENTATION.md#raw-address-prohibition](agent_playbook/DOCUMENTATION.md#raw-address-prohibition) and rewrite it to use the new symbol or delete it. Deferring this sweep to a later pass is the recurring failure mode that produces stale prose around recently symbolized addresses.
- **State-machine symbolization is per-value.** A state byte that takes N values is N separate naming decisions, not one. Symbolize values that have one proven writer AND one proven reader each. Stop at the first value that is overloaded across families (e.g., the same byte written by both a seeded-from-table path and a runtime transition path with conflicting semantics). Record unresolved values in `WORKING_NOTES.md` with the specific writer/reader gap and what evidence would close it. Do not invent generic `STATE_VALUE_3` / `STATE_VALUE_8` placeholders to make the family "complete."


<a id="high-value-pass-contract"></a>
## High-Value Pass Contract (Mandatory)

The normal pass unit is a coherent subsystem corridor, not a fixed number of
labels, a KPI bucket, or a single reviewer nit. A pass is high-value only if it
materially improves how a future reader understands or edits one connected
piece of the game.

For each non-final semantic pass, try to close the whole corridor in one edit
batch:
- semantic names for the main routines, tables, RAM/ZP fields, constants, and
  pointer targets touched by the corridor
- data-format documentation and `.DB` / `.DW` reflow for every proven table or
  stream opened by the corridor
- local-label cleanup for every safe internal branch target in the opened
  routines
- hardware/OAM/joypad/PPU/audio aliases and bitmasks when the corridor touches
  those domains
- stale prose cleanup in nearby comments and docs
- scorecard, crosswalk, memory map, working notes, and inventory sync as
  applicable; update the systems overview only when the subsystem clears the
  promotion gate at [DOCUMENTATION.md#dx-systems-scope](agent_playbook/DOCUMENTATION.md#dx-systems-scope)

Do not close a pass that only documents, renames, or constantizes one or two
isolated sites unless all broader static work is exhausted and the scorecard
states why it is final-tail cleanup.

A pass is a corridor outcome, not a commit count: one corridor pass may span
multiple commits or edit batches, and the scorecard records the corridor
result, not each commit — [PASS_WORKFLOW.md#pass-vs-commit](agent_playbook/PASS_WORKFLOW.md#pass-vs-commit).


<a id="reviewer-simulation-checklist"></a>
### Reviewer Simulation Checklist (Mandatory)

Before verification/closeout, review the touched region as if submitting a
code review to the user. Fix or explicitly defer each issue found:
- any global executable label that is only a branch/fallthrough target and can
  be localized
- labels or constants with placeholder/value/address vocabulary such as
  `StateNN`, `ModeNN`, `FieldNN`, `armN`, `PageNN`, `AddrNNNN`, `GroupNNNN`, or
  raw hex suffixes where semantics are now known
- hardcoded offsets, pointer bytes, or table sizes that can be expressed with
  field symbols, labels, or label math
- raw hardware-register operands or bitmasks left in touched routines despite
  an available canonical alias
- long `.DB` rows whose record/packet/stream structure is known
- comments that restate symbol names, instruction sequences, addressing modes,
  or raw addresses now covered by symbols
- any newly authored comment that did not pass the pre-write value test; these
  must not enter the patch in the first place
- pre-existing comments where symbolization, a named constant, or clearer
  structure now carries the meaning
- any `*_DX_Systems.md` edit made before the subsystem clears its
  [promotion gate](agent_playbook/DOCUMENTATION.md#dx-systems-scope), or that
  contains unresolved labels/addresses, helper walkthroughs, hypotheses, or
  future-pass plans; revert or route that material to the proper current-state
  artifact
- optional docs or working notes that are now duplicate, stale, or lower value
  than canonical docs

If generated pass artifacts report only generic `doc_closure` or no strong
corridor, do not stop there. Run this reviewer simulation against the project:
remaining `WORKING_NOTES.md`, optional support docs, long data rows,
global-code-label reports, address/value-coded names, raw-offset searches, and
obvious prior-project analogue gaps. Only then conclude that static work is
exhausted.


<a id="prior-project-reuse-gate"></a>
### Prior-Project Reuse Gate (Mandatory)

Before naming or documenting common NES subsystems, inspect analogous completed
projects and reuse their vocabulary, data-format descriptions, and field
families unless the new game contradicts them. Required comparison domains:
- audio drivers, music/SFX command streams, note/period tables
- PPU packet streams and nametable/attribute update queues
- OAM shadow, metasprite descriptors, sprite-strip records
- joypad polling and input edge/held masks
- actor/object slot layouts, state machines, collision boxes, motion streams
- score/HUD packet and BCD pipelines

If a subsystem appears Nintendo-common or already solved elsewhere, a pass is
incomplete until the comparison is either applied or the scorecard states why
the pattern does not fit.


<a id="session-orientation"></a>
## Session Orientation (Starting or Resuming)

Always start a session by identifying the current goal and project status.
Starting a new project routes to
[agent_playbook/NEW_PROJECT.md](agent_playbook/NEW_PROJECT.md);
resuming an existing one routes to
[agent_playbook/PASS_WORKFLOW.md](agent_playbook/PASS_WORKFLOW.md).


<a id="starting-a-new-project"></a>
### Starting a New Project

The full intake flow lives at
[agent_playbook/NEW_PROJECT.md#starting-a-new-project](agent_playbook/NEW_PROJECT.md#starting-a-new-project).
Two universal constraints stay at root:

- ROMs, manuals, and reference docs come from the user outside
  git-tracked source; the agent does not source or download commercial
  material itself.
- Mapper, PRG/CHR size, ROM container length, code-pointer state, and
  prior-project analogue are derived from the iNES header and existing
  artifacts during intake, not from the user.
<a id="resuming-an-existing-project"></a>
### Resuming an Existing Project

The resume sequence (`project-pass-prep` → `project-next-pass` →
working-notes review → `project-pass-start`), the wrapper-first
evidence rule, and the owner-field rule live at
[agent_playbook/PASS_WORKFLOW.md#session-resume](agent_playbook/PASS_WORKFLOW.md#session-resume).
Closeout (`project-pass-closeout`, scorecard sync, gates) lives at
[agent_playbook/PASS_WORKFLOW.md#pass-closeout](agent_playbook/PASS_WORKFLOW.md#pass-closeout).



<a id="canonical-artifacts"></a>
### Canonical Project Artifacts (Mandatory)

Every active project uses this fixed set; process gates validate it.

| Path | Role |
|---|---|
| `docs/crosswalk/TERMINOLOGY_CROSSWALK.md` | terminology + naming policy |
| `docs/reverse_engineering/ONBOARDING.md` | project entry point |
| `docs/reverse_engineering/QUICK_REFERENCE.md` | command index + warning registry pointer |
| `docs/reverse_engineering/PROGRESS_SCORECARD.md` | per-pass throughput + KPI ledger |
| `docs/reverse_engineering/MEMORY_MAP.md` | RAM/ZP ownership by subsystem |
| `docs/reverse_engineering/*_DX_Systems.md` | per-subsystem stable behavior docs |
| `docs/reverse_engineering/SEMANTIC_CLAIMS.md` | maturity-time semantic-claims ledger ([QUALITY_REVIEW.md#semantic-claims](agent_playbook/QUALITY_REVIEW.md#semantic-claims); validated by `project-maturity-check`) |
| `docs/reverse_engineering/inventory/renames.csv` | rename ledger (closeout reads this) |
| `docs/reverse_engineering/inventory/raw_ram_review.csv` | raw-RAM review queue (once project enters raw-RAM mode) |
Optional support docs: `WORKING_NOTES.md` (rules at
[DOCUMENTATION.md#working-notes](agent_playbook/DOCUMENTATION.md#working-notes)),
`PARITY_GAPS.md`, `ACTOR_ENUMS.md` or equivalent enum docs, trace
plans/runbooks, dedicated subsystem format/state-machine docs.
Retention criteria for optional support docs live at
[DOCUMENTATION.md#support-documents](agent_playbook/DOCUMENTATION.md#support-documents).


<a id="mission"></a>
## Mission

Given `Game.asm` (disassembly) and `GameReference.nes` (reference ROM in iNES format), produce a high-readability, maintainable, modifiable disassembly:

- **Primary:** maximize readability and maintainability.
- **Secondary:** maximize relocatability/editability by removing hardcoded addresses, embedded raw pointers, and hardcoded table/counter sizes wherever symbols or expressions work.
- **Semantic priority:** high-confidence semantic naming over mechanical KPI reduction. Do not perform placeholder alias sweeps whose main effect is KPI score movement without readability gain.
- **Parity:** preserve binary identity for refactor/documentation passes unless a non-parity change is explicitly requested.
- **Docs:** produce implementation-linked docs so a new developer can modify gameplay confidently.


<a id="safety-rules"></a>
## Non-Negotiable Safety Rules

1. **Claimed-green verification rule (canonical).** Do not report a check as green unless that exact check was rerun after the final edit that could affect it. The scorecard verify column must reflect the canonical wrapper's actual exit status; do not write any variant of "pass" when the wrapper fails, even if binary identity is preserved. Verify after every edit batch:
```sh
make project-verify PROJECT=<slug>
```
  - Run multiple verification commands sequentially, not in parallel.
  - **Mandatory Verification Gate:** Execute the project-specific verification command after every "symbolic shift" (renaming a block of definitions and their call sites). Do not defer verification until the end of a session.
  - If a follow-up fix changes docs, warnings, inventory, or scorecard content, rerun the affected checks before reporting green.
  - Semantic-pass verification modes while unresolved `LXXXX` labels remain — [PASS_WORKFLOW.md#semantic-pass-verification](agent_playbook/PASS_WORKFLOW.md#semantic-pass-verification).
2. Never merge a refactor/comment/naming batch unless binary identity passes.
3. If meaning is uncertain, keep behavior unchanged. Add an `inferred` note only when the uncertainty itself matters to a future reader; otherwise record the evidence gap in `WORKING_NOTES.md` rather than adding speculative code commentary.
4. Do not duplicate format specifications across multiple documents. Format-documentation requirements — [DOCUMENTATION.md#data-format-documentation](agent_playbook/DOCUMENTATION.md#data-format-documentation).
5. **Concurrent Documentation Rule (Mandatory):** Update the appropriate current-state artifacts (`PROGRESS_SCORECARD.md`, `TERMINOLOGY_CROSSWALK.md`, `MEMORY_MAP.md`, inventories, proven format docs, or `WORKING_NOTES.md`) in the same turn as code changes. Do not force every finding into every document. In particular, defer `*_DX_Systems.md` until the subsystem clears the promotion gate at [DOCUMENTATION.md#dx-systems-scope](agent_playbook/DOCUMENTATION.md#dx-systems-scope); early-pass deferral is correct synchronization, not missing documentation.
6. **Comment Hygiene Rule (Mandatory):** Apply the comment admission test before authoring prose; do not generate speculative, narrating, or KPI-filler comments for later pruning. Canonical rule — [DOCUMENTATION.md#comment-quality](agent_playbook/DOCUMENTATION.md#comment-quality).
  - When a RAM/ZP/hardware address has a stable symbol, nearby comments must not use the raw address unless the numeric address itself is the semantic fact.
  - `make project-verify PROJECT=<slug>` runs `project-comment-audit` as a hard gate for high-confidence stale raw-address comments. Use `make project-comment-audit PROJECT=<slug> FORMAT=text` directly when reviewing comment-only sweeps.
  - The audit gate catches the loudest cases (`$XX`/`$XXXX` near operands), but softer prose patterns live at [DOCUMENTATION.md#raw-address-prohibition](agent_playbook/DOCUMENTATION.md#raw-address-prohibition). Symbolization passes must sweep these manually in the same batch — see the **Symbolization-triggers-prose-sweep** principle in **Guiding Pass Philosophy**. Recurring failure mode: a comment gets written referencing a raw address, then a later pass symbolizes that address but doesn't touch prose, leaving stale citations indefinitely.
7. **Document Role Boundary Rule (Mandatory):** Keep system/implementation documentation separate from reverse-engineering process documentation.
  - `*_DX_Systems.md` is a late-maturity subsystem overview, not a per-pass deliverable. It documents stable game behavior only: subsystem architecture, frame lifecycle, major ownership boundaries, and links to mature format/state-machine docs. Promotion and format-ownership boundaries — [DOCUMENTATION.md#dx-systems-scope](agent_playbook/DOCUMENTATION.md#dx-systems-scope).
  - `MEMORY_MAP.md` documents stable semantic RAM/ZP meanings grouped by subsystem.
  - `PROGRESS_SCORECARD.md` records pass history, change summaries, and KPI movement.
  - `renames.csv`, `raw_ram_review.csv`, and similar inventory files record naming rationale, review status, confidence, and deferred/revisit judgments.
  - Do **not** write reverse-engineering provenance into system docs. Avoid phrases such as `recovered`, `now explicit`, `warning-baselined`, `currently unreferenced because no live consumer is proven`, `proven in pass`, or similar pass/discovery narration in `*_DX_Systems.md`.
  - If provenance matters, put it in the scorecard, inventory ledgers, or code comments scoped to the uncertain site, not in the subsystem overview doc.
8. **Process-Gate Rule (Mandatory):** For project-level completion checks, use the current wrappers:
```sh
make project-intake PROJECT=<slug>
make project-process-check PROJECT=<slug>
make project-maturity-check PROJECT=<slug>
make project-ci PROJECT=<slug>
```
Treat these as the canonical process entry points; do not rely on remembered ad-hoc command sequences.

9. **Pass-Mechanism Rule (Mandatory):** For starting or resuming a pass, use:
```sh
make project-pass-prep PROJECT=<slug>
make project-next-pass PROJECT=<slug>
make project-pass-start PROJECT=<slug>
```
`project-next-pass` emits candidate evidence (hot labels, tables, raw bytes, red gates), not an authoritative pass choice; treat it as advisory. Before substantial edits the operator must select and record an explicit corridor objective — pass `TARGET=<corridor_anchor>` (optional `PASS=<id>`) to `project-pass-start`; without `TARGET` the wrapper warns and defaults to the first candidate. Objective fields live at [PASS_WORKFLOW.md#corridor-objective](agent_playbook/PASS_WORKFLOW.md#corridor-objective). Manual `rg`/`sed` rescans are fallback behavior, not the default pass-selection method.
If recent passes are low-yield, run the [strategy checkpoint](agent_playbook/PASS_WORKFLOW.md#low-yield-checkpoint) before continuing.

10. **Mod Commit Rule (Mandatory):** Treat `projects/*/mods/` as local experiment space. Do not commit mods, relocatability probes, or other mod artifacts unless the user explicitly asks for that mod to be committed.


<a id="work-order"></a>
## Corridor Execution Contract

The normal pass unit is one coherent subsystem corridor — see
[High-Value Pass Contract](#high-value-pass-contract). Within that corridor,
close every dimension the evidence supports — semantic names, RAM/ZP
ownership, constants, pointer targets, data formats, local labels, comment
cleanup, and project docs — in the same edit batch when verification risk
allows it.
This section defines how to execute one selected corridor. It is not a
sequence of repository-wide work types.

1. **Select one corridor.** Use generated pass artifacts, `WORKING_NOTES.md`,
   prior-project analogues, and the [High-Value Pass Contract](#high-value-pass-contract).
   Generated artifacts are candidate evidence, not the pass decision: state the
   corridor objective and either broaden a generated local anchor into a corridor
   or explicitly reject it — [PASS_WORKFLOW.md#corridor-objective](agent_playbook/PASS_WORKFLOW.md#corridor-objective).
   Game-reference intake and crosswalk seeding live at
   [DOCUMENTATION.md#terminology-crosswalk](agent_playbook/DOCUMENTATION.md#terminology-crosswalk);
   pass selection mechanics live at
   [PASS_WORKFLOW.md#session-resume](agent_playbook/PASS_WORKFLOW.md#session-resume).
2. **Establish the corridor boundary.** Identify owning routines, data
   producers/consumers, RAM/ZP fields, and external interfaces. Do not expand
   into unrelated subsystems merely because a token or literal matches.
3. **Close every proven dimension in the corridor.** Apply semantic routine
   and data names, safe local-label cleanup, RAM/ZP names, constants, pointer
   targets, known data formats, hardware aliases, justified comment additions
   plus cleanup of pre-existing stale prose, and necessary doc updates.
   Operational mechanics:
   - prefix families and verb-oriented procedure names —
     [ASM_STYLE.md#naming-conventions](agent_playbook/ASM_STYLE.md#naming-conventions);
   - structured-field offsets —
     [ASM_STYLE.md#structured-field-offsets](agent_playbook/ASM_STYLE.md#structured-field-offsets);
   - state-byte symbolization stop rule + init-loop trap —
     [ASM_STYLE.md#state-action-constants](agent_playbook/ASM_STYLE.md#state-action-constants);
   - raw-RAM corridor selection and queue operation —
     [PASS_WORKFLOW.md#raw-ram-prioritization](agent_playbook/PASS_WORKFLOW.md#raw-ram-prioritization)
     and
     [PASS_WORKFLOW.md#raw-ram-queue](agent_playbook/PASS_WORKFLOW.md#raw-ram-queue);
   - data-blob naming and reflow —
     [DATA_RECOVERY.md#data-blob-readability](agent_playbook/DATA_RECOVERY.md#data-blob-readability);
   - PPU packet-stream normalization —
     [DATA_RECOVERY.md#ppu-packet-streams](agent_playbook/DATA_RECOVERY.md#ppu-packet-streams);
   - declaration-site, procedure, and data-label comments —
     [DOCUMENTATION.md#declaration-comments](agent_playbook/DOCUMENTATION.md#declaration-comments),
     [DOCUMENTATION.md#procedure-comments](agent_playbook/DOCUMENTATION.md#procedure-comments),
     and
     [DOCUMENTATION.md#data-label-format](agent_playbook/DOCUMENTATION.md#data-label-format).
4. **Respect evidence limits.** Keep uncertain behavior unchanged, use narrow
   names or scoped aliases, and record only durable unresolved questions in
   `WORKING_NOTES.md`.
5. **Verify coherent batches.** Split the corridor only when verification
   risk requires it. Preserve a continuation plan when the corridor cannot
   close in one batch. Batching and mass-edit mechanics live at
   [PASS_WORKFLOW.md#batching-and-commit-boundaries](agent_playbook/PASS_WORKFLOW.md#batching-and-commit-boundaries)
   and [TOOLING.md#script-hygiene](agent_playbook/TOOLING.md#script-hygiene).
6. **Review and close out.** Run reviewer simulation, readability review,
   verification, ledgers, scorecard sync, unused-symbol closure, and the
   project-process and project-docs gates after the final edit. Closeout
   mechanics live at
   [PASS_WORKFLOW.md#pass-closeout](agent_playbook/PASS_WORKFLOW.md#pass-closeout);
   warning-baseline mechanics at
   [NEW_PROJECT.md#warning-baseline-bootstrap](agent_playbook/NEW_PROJECT.md#warning-baseline-bootstrap).

Genuine local dependencies inside the corridor:

- Establish procedure boundaries before localizing internal labels —
  [ASM_STYLE.md#naming-conventions](agent_playbook/ASM_STYLE.md#naming-conventions).
- Prove producer/consumer relationships before assigning stable RAM or data
  semantics.
- Admit new comments only when they pass the pre-write value test. Update or
  remove pre-existing comments made stale by symbols or formats; adding
  commentary is not a required dimension of a pass.
- Verification claim semantics — [Claimed-green verification rule](#safety-rules).

Cross-cutting rules:

- Corridor scope and closure — [High-Value Pass Contract](#high-value-pass-contract).
- Prior-project reuse — [Prior-Project Reuse Gate](#prior-project-reuse-gate).
- Semantic-first naming and mechanical-to-semantic linkage —
  [Guiding Pass Philosophy](#guiding-pass-philosophy).
- Low-yield reassessment —
  [Non-Negotiable Safety Rules](#safety-rules) (Pass-Mechanism Rule) and
  next-pass selection in
  [PASS_WORKFLOW.md#completion-checklist](agent_playbook/PASS_WORKFLOW.md#completion-checklist).
<a id="core-naming"></a>
## Naming Conventions

Always-needed naming rules (full conventions live in [ASM_STYLE.md#naming-conventions](agent_playbook/ASM_STYLE.md#naming-conventions)):

- Use semantic, role-oriented names; do not encode addresses or values in symbol names.
- Name zero-page and RAM symbols `ZP_<UpperCamelRole>` and
  `RAM_<UpperCamelRole>` with no additional underscores, for example
  `ZP_PpuCtrlShadow` and `RAM_OamShadowBase`.
- No address/value-coded placeholders unless explicitly tracked in `WORKING_NOTES.md` with a revisit note.
- Localize branch-only labels when scope permits; keep non-locals only when shared control flow requires.
- Use canonical cross-project vocabulary (registers, joypad masks, OAM fields, etc.) — see [hardware constants](agent_playbook/ASM_STYLE.md#hardware-constants).


<a id="confidence-protocol"></a>
## Confidence Protocol

Use confidence tags in comments/docs: `high confidence`, `medium confidence`, `inferred`.

Rules:

1. Do not guess silently. If a symbol is renamed by structural inference (e.g., `+8` array offset), say so inline.
2. Keep uncertain semantics explicit in docs so future contributors can refine safely.
3. Run a confidence-promotion sweep before declaring completion: revisit prior `inferred` annotations and drop the tag where confidence is now high; keep `inferred` only for genuinely unresolved semantics or intentionally overloaded aliases; preserve explanatory comments when removing `inferred` (drop the uncertainty marker, not the documentation).
4. Confidence labels apply to semantic claims only. Do not mark mechanical/non-semantic aliases as `high` or `medium confidence`; classify those as `mechanical` in ledgers and pair with a semantic follow-up plan.

Confidence decision rules (mandatory):

- **`high confidence`** — control or data flow directly proves the role; reader/writer evidence is concrete and consistent; no live contradictory usage is known.
- **`medium confidence`** — role is strongly suggested by structure and nearby consumers; evidence is coherent but one part of the chain is still indirect or not fully closed.
- **`inferred`** — best current explanation is plausible and useful, but at least one important semantic step is still unproven or potentially mixed.
- **Do not use `inferred` as a generic caution sticker.** If fully proven, drop it; if purely mechanical, use `mechanical` in ledgers and no confidence prose in docs.
- **Default when unsure:** prefer a narrower neutral name plus no confidence claim, or a scoped overlay alias plus a short `inferred` note.


<a id="intermediate-artifacts"></a>
## Intermediate Artifacts (Critical)

Lightweight machine-readable inventories live under
`docs/reverse_engineering/inventory/`. Schemas + refresh wrappers
live at
[agent_playbook/TOOLING.md#inventory-commands](agent_playbook/TOOLING.md#inventory-commands);
consumer guidance for the generated cache under
`docs/reverse_engineering/inventory/pass/` lives at
[agent_playbook/PASS_WORKFLOW.md#generated-vs-authored-artifacts](agent_playbook/PASS_WORKFLOW.md#generated-vs-authored-artifacts).

Files in the authored set: `renames.csv` (rename ledger),
`pointer_targets.csv` (pointer producer/consumer map),
`branch_literal_sites.csv` (parity-sensitive relative branch
literals), `constants_catalog.csv` (domain-separated constants),
`data_extent_assertions.csv` (reviewed table-span assertions checked by
`project-verify` and `project-maturity-check` when present),
`raw_ram_review.csv` (raw-RAM review queue — operation at
[#raw-ram-queue](agent_playbook/PASS_WORKFLOW.md#raw-ram-queue)),
`unknowns.md` (small clustered list of unresolved semantics).


<a id="supplementary-rules"></a>
<a id="specialized-rule-index"></a>
## Specialized Rule Index

Topic-specific and supplementary rules are indexed below by canonical home.

- <a id="machine-readable-analysis-documentation-hygiene"></a>**Machine-readable analysis & documentation hygiene** — safe multiline doc edits, warning registry wording, and hygienic provenance comments at [DOCUMENTATION.md#machine-readable-doc-hygiene](agent_playbook/DOCUMENTATION.md#machine-readable-doc-hygiene) and [DOCUMENTATION.md#declaration-comments](agent_playbook/DOCUMENTATION.md#declaration-comments); structured-listing requirement at [TOOLING.md#xasm-options](agent_playbook/TOOLING.md#xasm-options); PPU packet header naming at [DATA_RECOVERY.md#ppu-packet-streams](agent_playbook/DATA_RECOVERY.md#ppu-packet-streams); verification claim semantics at [Claimed-green verification rule](#safety-rules).
- <a id="system-level-prose-documentation"></a>**System-level prose documentation** — subsystem doc scope, format/state-machine doc requirements, abstraction checklist, and cross-reference guidance at [DOCUMENTATION.md#dx-systems-scope](agent_playbook/DOCUMENTATION.md#dx-systems-scope); stub-doc lifecycle criteria at [DOCUMENTATION.md#support-documents](agent_playbook/DOCUMENTATION.md#support-documents); MEMORY_MAP organization at [DOCUMENTATION.md#memory-map](agent_playbook/DOCUMENTATION.md#memory-map).
- <a id="data-format-documentation-rules"></a>**Data format documentation** — [DOCUMENTATION.md#data-format-documentation](agent_playbook/DOCUMENTATION.md#data-format-documentation).
- <a id="magic-number-elimination-rules"></a>**Magic-number elimination** — semantic constant practice, address-as-constant red flag, and detailed constantization rules at [ASM_STYLE.md#state-action-constants](agent_playbook/ASM_STYLE.md#state-action-constants); structured-field symbolization at [ASM_STYLE.md#structured-field-offsets](agent_playbook/ASM_STYLE.md#structured-field-offsets); pointer-byte load sweep at [DATA_RECOVERY.md#computed-pointer-recovery](agent_playbook/DATA_RECOVERY.md#computed-pointer-recovery); PPU packet integrity and window normalization at [DATA_RECOVERY.md#ppu-packet-streams](agent_playbook/DATA_RECOVERY.md#ppu-packet-streams).
- <a id="parity-bugs-and-patterns"></a>**Parity, bugs & patterns** — tail-call and redundant-instruction patterns at [ASM_STYLE.md#tail-call-annotations](agent_playbook/ASM_STYLE.md#tail-call-annotations); inline bug comments at [DOCUMENTATION.md#parity-bug-comments](agent_playbook/DOCUMENTATION.md#parity-bug-comments); symbolic-expression encoding for parity-preserved values at [DATA_RECOVERY.md#hardcoded-length-elimination](agent_playbook/DATA_RECOVERY.md#hardcoded-length-elimination); parity bug registry at [QUALITY_REVIEW.md#parity-bug-registry](agent_playbook/QUALITY_REVIEW.md#parity-bug-registry).
- <a id="relocatability-first-rules"></a>**Relocatability-first rules** — [ASM_STYLE.md#relocatability](agent_playbook/ASM_STYLE.md#relocatability).
- <a id="literal-base-readability-rule"></a>**Literal base readability rule** — [ASM_STYLE.md#literal-base-readability](agent_playbook/ASM_STYLE.md#literal-base-readability).
- <a id="data-blob-readability-rule"></a>**Data blob readability rule** — [agent_playbook/DATA_RECOVERY.md#data-blob-readability](agent_playbook/DATA_RECOVERY.md#data-blob-readability).
- <a id="nesrev-intake-sanity-gate"></a>**NESrev intake sanity gate** — [agent_playbook/NEW_PROJECT.md#nesrev-intake-sanity-gate](agent_playbook/NEW_PROJECT.md#nesrev-intake-sanity-gate).
- <a id="nesrev-code-pointer-recovery-pass"></a>**NESrev code-pointer recovery pass** — [DATA_RECOVERY.md#code-pointer-recovery](agent_playbook/DATA_RECOVERY.md#code-pointer-recovery). wrapper invocation + hint formats at [TOOLING.md#nesrev-controls](agent_playbook/TOOLING.md#nesrev-controls).
- <a id="bit-skip-overlay-cleanup"></a>**BIT-skip overlay multi-entry routine cleanup** — [DATA_RECOVERY.md#bit-skip-cleanup](agent_playbook/DATA_RECOVERY.md#bit-skip-cleanup).
- <a id="new-project-warning-baseline-bootstrap"></a>**New-project warning-baseline bootstrap** — [agent_playbook/NEW_PROJECT.md#warning-baseline-bootstrap](agent_playbook/NEW_PROJECT.md#warning-baseline-bootstrap).
- <a id="assembler-listings-parity-analysis"></a>**Using assembler listings for parity analysis** — [TOOLING.md#xasm-options](agent_playbook/TOOLING.md#xasm-options). parity drift at [TOOLING.md#parity-drift](agent_playbook/TOOLING.md#parity-drift).
- <a id="listing-assisted-pointer-blob-audit"></a>**Listing-assisted raw pointer blob audit** — [DATA_RECOVERY.md#listing-assisted-pointer-audit](agent_playbook/DATA_RECOVERY.md#listing-assisted-pointer-audit).
- <a id="xasm-structured-feature-workflow"></a>**xasm structured-feature workflow** — [TOOLING.md#xasm-structured-analysis](agent_playbook/TOOLING.md#xasm-structured-analysis). exit codes at [TOOLING.md#exit-codes](agent_playbook/TOOLING.md#exit-codes).
- <a id="computed-pointer-blob-consumer-recovery"></a>**Computed-pointer blob consumer recovery** — [DATA_RECOVERY.md#computed-pointer-recovery](agent_playbook/DATA_RECOVERY.md#computed-pointer-recovery).
- <a id="common-nes-ppu-packet-stream-pattern"></a>**Common NES PPU packet stream pattern** — [DATA_RECOVERY.md#ppu-packet-streams](agent_playbook/DATA_RECOVERY.md#ppu-packet-streams).
- <a id="auxiliary-script-hygiene"></a>**Auxiliary script hygiene** — [TOOLING.md#script-hygiene](agent_playbook/TOOLING.md#script-hygiene).
- <a id="batching-strategy"></a>**Batching strategy** — [agent_playbook/PASS_WORKFLOW.md#batching-and-commit-boundaries](agent_playbook/PASS_WORKFLOW.md#batching-and-commit-boundaries).
- <a id="pre-verify-change-impact-checklist"></a>**Pre-verify change-impact checklist** — [agent_playbook/PASS_WORKFLOW.md#pass-closeout](agent_playbook/PASS_WORKFLOW.md#pass-closeout).
- <a id="execution-efficiency-scorecard"></a>**Execution efficiency scorecard** — [agent_playbook/PASS_WORKFLOW.md#scorecard-sync](agent_playbook/PASS_WORKFLOW.md#scorecard-sync).
- <a id="phase-exit-checklist"></a>**Project maturity dimensions** — [agent_playbook/PASS_WORKFLOW.md#project-maturity-dimensions](agent_playbook/PASS_WORKFLOW.md#project-maturity-dimensions).
- <a id="ram-symbolization-prioritization-rules"></a>**RAM symbolization prioritization rules** — [agent_playbook/PASS_WORKFLOW.md#raw-ram-prioritization](agent_playbook/PASS_WORKFLOW.md#raw-ram-prioritization).
- <a id="post-rename-closeout-gates"></a>**Post-rename closeout gates** — [agent_playbook/PASS_WORKFLOW.md#completion-checklist](agent_playbook/PASS_WORKFLOW.md#completion-checklist).
- <a id="documentation-deliverables"></a>**Documentation deliverables** — [DOCUMENTATION.md#documentation-artifacts](agent_playbook/DOCUMENTATION.md#documentation-artifacts).
- <a id="data-label-documentation-template"></a>**Data-label documentation template** — [DOCUMENTATION.md#data-label-format](agent_playbook/DOCUMENTATION.md#data-label-format).
- <a id="documentation-reference-stability"></a>**Documentation reference stability** — [DOCUMENTATION.md#reference-document-use](agent_playbook/DOCUMENTATION.md#reference-document-use).
- <a id="active-use-of-reference-documentation"></a>**Active use of reference documentation** — [DOCUMENTATION.md#reference-document-use](agent_playbook/DOCUMENTATION.md#reference-document-use).
- <a id="pointer-table-conversion-rules"></a>**Pointer table conversion rules** — [DATA_RECOVERY.md#pointer-table-conversion](agent_playbook/DATA_RECOVERY.md#pointer-table-conversion).
- <a id="scanning-for-code-pointers-in-data"></a>**Scanning for code pointers in data** — [DATA_RECOVERY.md#code-pointer-recovery → General code-pointer scan procedure](agent_playbook/DATA_RECOVERY.md#code-pointer-recovery).
- <a id="orphan-opcode-blob-decode-sweep"></a>**Orphan opcode-blob decode sweep** — [DATA_RECOVERY.md#orphan-opcode-decode](agent_playbook/DATA_RECOVERY.md#orphan-opcode-decode).
- <a id="blob-decode-kpi-pre-assessment"></a>**Blob-decode KPI pre-assessment** — [DATA_RECOVERY.md#orphan-opcode-decode](agent_playbook/DATA_RECOVERY.md#orphan-opcode-decode).
- <a id="review-quality-bar"></a>**Review quality bar** — [agent_playbook/QUALITY_REVIEW.md#quality-review](agent_playbook/QUALITY_REVIEW.md#quality-review).
- <a id="success-evaluation-criteria"></a>**Success evaluation criteria** — [agent_playbook/QUALITY_REVIEW.md#quality-review](agent_playbook/QUALITY_REVIEW.md#quality-review).
- <a id="readability-self-audit"></a>**Readability self-audit** — [agent_playbook/QUALITY_REVIEW.md#readability-self-audit](agent_playbook/QUALITY_REVIEW.md#readability-self-audit).
- <a id="optional-deep-confidence-passes"></a>**Optional deep-confidence passes** — [agent_playbook/QUALITY_REVIEW.md#deep-confidence-passes](agent_playbook/QUALITY_REVIEW.md#deep-confidence-passes).
- <a id="command-template"></a>**Command template (general)** — [TOOLING.md#command-reference](agent_playbook/TOOLING.md#command-reference).
- **Pre-close relocation safety gate** — [PASS_WORKFLOW.md#pass-closeout](agent_playbook/PASS_WORKFLOW.md#pass-closeout).
- **Runtime evidence workflow** — [PASS_WORKFLOW.md#pass-closeout](agent_playbook/PASS_WORKFLOW.md#pass-closeout).
- **Script quality gate** — [TOOLING.md#script-hygiene](agent_playbook/TOOLING.md#script-hygiene).
- **Per-project trace capture runner** — [TOOLING.md#script-hygiene](agent_playbook/TOOLING.md#script-hygiene).
- **Headless / GUI constraints for runtime tracing** — [TOOLING.md#script-hygiene](agent_playbook/TOOLING.md#script-hygiene).
- **Confidence-promotion criteria (static vs. runtime)** — [QUALITY_REVIEW.md#static-vs-runtime-gaps](agent_playbook/QUALITY_REVIEW.md#static-vs-runtime-gaps).
- **`PARITY_GAPS.md` freshness** — [DOCUMENTATION.md#support-documents](agent_playbook/DOCUMENTATION.md#support-documents).
- **Packed-state promotion (mask/flag constants, threshold literals, lane aliases)** — [ASM_STYLE.md#state-action-constants](agent_playbook/ASM_STYLE.md#state-action-constants).
- **Indirect addressing literal sweep** — [ASM_STYLE.md#label-math](agent_playbook/ASM_STYLE.md#label-math).
- **Mixed tail regions (preserve byte layout, label only when producer/consumer is known)** — [DATA_RECOVERY.md#data-blob-readability](agent_playbook/DATA_RECOVERY.md#data-blob-readability).
- <a id="new-project-first-semantic-pass-shape"></a>**New-project first semantic pass shape** — [agent_playbook/NEW_PROJECT.md#first-three-pass-architecture](agent_playbook/NEW_PROJECT.md#first-three-pass-architecture).
- <a id="new-project-autonomy-defaults"></a>**New-project autonomy defaults** — [agent_playbook/NEW_PROJECT.md#new-project-autonomy](agent_playbook/NEW_PROJECT.md#new-project-autonomy).
- <a id="generated-pass-artifacts"></a>**Generated pass artifacts (cache, not source of truth)** — [agent_playbook/PASS_WORKFLOW.md#generated-vs-authored-artifacts](agent_playbook/PASS_WORKFLOW.md#generated-vs-authored-artifacts).
- <a id="persistent-raw-ram-review-queue"></a>**Persistent raw-RAM review queue** — [agent_playbook/PASS_WORKFLOW.md#raw-ram-queue](agent_playbook/PASS_WORKFLOW.md#raw-ram-queue).
- <a id="unused-symbol-closure-gate"></a>**Unused-symbol closure gate** — [agent_playbook/PASS_WORKFLOW.md#pass-closeout](agent_playbook/PASS_WORKFLOW.md#pass-closeout).
- <a id="dynamic-length-and-counter-rules"></a>**Dynamic length and counter rules** — [ASM_STYLE.md#label-math](agent_playbook/ASM_STYLE.md#label-math) (expression syntax) and [DATA_RECOVERY.md#hardcoded-length-elimination](agent_playbook/DATA_RECOVERY.md#hardcoded-length-elimination) (boundary labels, semantic count constants, parity-preserved counter bugs, packet-payload guard, re-verify-after-rewrite rule).


<a id="output-philosophy"></a>
## Output Philosophy

The final disassembly should be:
- Behavior-identical
- Readable without line-by-line opcode tracing
- Self-contained for day-to-day development
- Backed by docs that let a new developer modify systems safely
