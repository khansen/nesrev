# REVIEW_AUDITS Playbook

This playbook is the canonical home for the concrete review *procedures* run
during and near maturity: the static readability debt audit, the readability
self-audit, the expanded reviewer simulation, the stale-placeholder /
symbol-family / residual-magic-number / global-label audits, the project-wide
pointer-byte consolidation audit, and optional deep-confidence passes. The review
*criteria* that invoke these audits (quality bar, gold-standard checklist, KPI
interpretation, semantic-claims, parity registry) live in
[QUALITY_REVIEW.md](QUALITY_REVIEW.md).

## Ownership

This playbook owns the project-level review audit procedures:

- static readability debt audit before any static-exhaustion claim
- readability self-audit
- reviewer simulation expansion
- stale placeholder/value/address-name audits
- incomplete symbol-family audits
- residual magic-number and hardcoded-offset review
- project-wide pointer-byte consolidation audit
- global-label documentation/localization review
- optional deep-confidence passes

The gold-standard criteria that invoke these audits live in
[QUALITY_REVIEW.md](QUALITY_REVIEW.md). Audits may link to rules in other
playbooks but do not redefine them.

## Playbook Sections

<a id="static-readability-debt-audit"></a>
## Static Readability Debt Audit

Mandatory before static-exhaustion or gold-static claims. Record one
disposition per candidate class in the scorecard or `WORKING_NOTES.md`:
**fixed**, **queued static pass**, **deferred** with evidence gap, or
**runtime-gated** with trace question. Unexamined candidates forbid "static
done."

Run `project-pass-prep` / `project-next-pass`, then targeted scans:

```sh
source scripts/project_common.sh && load_project_conf <slug>

rg -n "^\\s*\\.DB\\b([^,]*,){12,}|\\b(Packed|Blob|StreamData|ProgramData|MacroData|MetaspriteRecord|FrameData|RawData)\\b" "${ASM_FILE}" "${DOC_ROOT}"
rg -n "\\b[A-Za-z_][A-Za-z0-9_]*\\+(\\$[0-9A-Fa-f]+|[0-9]+)\\b|\\.DB\\b.*[<>][A-Za-z_][A-Za-z0-9_]*" "${ASM_FILE}"
rg -n "(LDX|LDY|CPX|CPY) #(\\$[0-9A-Fa-f]{1,2}|[0-9]+)\\b" "${ASM_FILE}"
rg -n "\\b[A-Za-z_][A-Za-z0-9_]*(Record|Frame|Entry|Variant)[0-9]+\\b" "${ASM_FILE}" "${DOC_ROOT}"
rg -n "\\bNOP\\b|^\\s*\\.DB\\b.*\\$EA\\b" "${ASM_FILE}"
rg -n "^\\s*\\.DB\\s+\\$(FF|00)(,\\$(FF|00)){2,}\\b" "${ASM_FILE}"
rg -n "(AND|ORA|EOR|BIT|CMP) #(\\$[0-9A-Fa-f]{2}|%[01]{8})\\b|\\b[A-Za-z_][A-Za-z0-9_]*(Flags|Flag|Mask|Bits|State)\\b" "${ASM_FILE}"
```

Read owners before editing. Decisions: reflow proven opaque blobs/long rows per
[DATA_RECOVERY.md#data-blob-readability](DATA_RECOVERY.md#data-blob-readability);
replace real `Label+N`, count, and bound sites with labels/fields/label math;
encode parity off-by-one behavior symbolically with a note; prefer owner-scoped
record/frame names unless the ordinal is real; compare common subsystem
vocabulary with prior projects.

Required dispositions for this audit:

- **NOP and padding representation:** apply
  [ASM_STYLE.md#nop-and-padding-representation](ASM_STYLE.md#nop-and-padding-representation)
  to every NOP, executable `$EA` byte, jump-over-padding pattern, and
  terminal/inter-table fill island surfaced by the scans.
- **Packed flag families:** when one bit of a packed RAM/ZP/hardware/control
  byte is symbolized, audit the whole touched family. Use binary literals for
  bit constants and masks, introduce composite masks for repeated groups, and
  replace nearby raw bit tests in the same corridor.
- **Tail calls, forced branches, and redundant sequences:** scan for
  `JSR`/optional labels/`RTS`, compact unconditional branches, identity ALU
  ops (`ORA #0`, `EOR #0`, `AND #$FF`), and overlong transfer arithmetic.
  Annotate parity-preserved cases per
  [ASM_STYLE.md#tail-call-annotations](ASM_STYLE.md#tail-call-annotations).

<a id="readability-self-audit"></a>
## Readability Self-Audit

At the end of each pass — or at minimum every few passes when
working near gold-standard — read the touched region as a stranger
would and ask:
1. **New-comment admission audit.** For every newly authored comment,
   identify the pre-write decision: what exact non-obvious durable fact
   required prose, and why could symbols or structure not express it?
   If there was no valid answer, the comment should never have been
   authored; treat that as an authoring-process failure, not routine
   cleanup. Comment count is not pass progress.
   (Canonical rule at
   [DOCUMENTATION.md#comment-quality](DOCUMENTATION.md#comment-quality).)
2. **Symbolization test.** Could a semantic symbol, constant, field,
   state, mask, range label, or derived expression express the same
   meaning? If yes, the comment must not be authored; fix the code
   instead. Never accept prose explaining a still-hardcoded value.
3. **Narration test.** Does it restate the symbol, assignment,
   instruction sequence, branch condition, loop, addressing mode, or
   literal value? Do not author it.
4. **Audience test.** Does it teach standard 6502/NES behavior rather
   than this game's architecture, ownership, invariant, or unusual hardware
   use? Assume an experienced NES programmer and omit tutorial prose.
   (Canonical rule at
   [DOCUMENTATION.md#audience-contract](DOCUMENTATION.md#audience-contract).)
5. **Prose hygiene.** Does it cite a raw address for a location that now
   has a stable symbol? (Canonical examples and rule at
   [DOCUMENTATION.md#raw-address-prohibition](DOCUMENTATION.md#raw-address-prohibition).)
6. **State-machine completeness.** If a state byte family has been
   partially symbolized (`*_STATE_ACTIVE`, `*_STATE_CONSUMED`),
   are the remaining values clearly recorded in
   `WORKING_NOTES.md` with their writer/reader gap, or silently
   left as raw hex? (Canonical rules at
   [ASM_STYLE.md#state-action-constants](ASM_STYLE.md#state-action-constants)
   and [DOCUMENTATION.md#working-notes](DOCUMENTATION.md#working-notes).)
7. **Procedure headers.** Does the header preserve a non-obvious
   contract, side effect, ordering constraint, or public-entry role,
   or would it summarize the procedure name/body? Do not author
   walkthroughs or tautological headers.
   (Canonical rule at
   [DOCUMENTATION.md#procedure-comments](DOCUMENTATION.md#procedure-comments).)

Representative failures and dispositions:

- `; low bit OR'd into PPUCTRL shadow before write; toggles horizontal
  nametable` — do not write it; name the mask. Comment only a non-obvious reason.
- `; spin until the VBlank flag is set` — do not write it; name the wait/flag.
- `; warm-reset detection: $07FA..$07FC must hold BootSignature` — symbolize
  the range before deciding whether a non-obvious reset invariant needs prose.
- `; install 15-byte ResetDefaults into $0629..$0637` — label source,
  destination, and derived length instead of writing the comment.
- `; flush queued packet stream when $52 != $53` — name the queue fields and
  do not write the comment.
- `; vertical scroll = 0` — do not write it.
- `; OAM DMA source page = $0200 (OAM shadow)` — use the OAM base/derived page
  symbols; do not write the comment.

New comments must pass before they enter the patch. Apply a separate cleanup
review to pre-existing `.EQU` declaration blocks, procedure headers, and inline
branch comments touched by the pass. Data-table
`Format:` headers are out of scope: per
[DOCUMENTATION.md#data-label-format](DOCUMENTATION.md#data-label-format)
they intentionally document concrete record layouts (field order,
sizes, encoding), which would otherwise read as a "mechanics"
violation in question 3.
This audit is a mandatory closeout step, separate from KPI
verification:
- A green `make project-verify PROJECT=<slug>` is necessary but not
  sufficient.
- A pass that closes KPI debt but leaves verbose mechanics in
  declaration comments is incomplete.
- Authoring a low-value comment is a process failure even if closeout later
  catches it; documentation KPI improvement never justifies generating filler.
- A pass that symbolizes new addresses but does not sweep prose
  for stale citations is incomplete.
- A pass that partially symbolizes a state machine without
  recording the remaining gaps in `WORKING_NOTES.md` is
  incomplete.
- No script enforces every item, so the agent must explicitly
  perform it. The cost of skipping it is paid by every future
  reader.
<a id="reviewer-simulation"></a>
## Reviewer Simulation (Expanded)

The compact mandatory reviewer checklist lives at
[AGENTS.md#reviewer-simulation-checklist](../AGENTS.md#reviewer-simulation-checklist).
Run that checklist before every closeout. The expanded form below
is what to do when `make project-next-pass` reports only generic
`doc_closure` or no strong corridor — instead of declaring static
work exhausted, run the deeper audits below in this order:
1. **Stale placeholder / value / address-name audit** —
   [#stale-placeholder-audit](#stale-placeholder-audit).
2. **Incomplete symbol-family audit** —
   [#symbol-family-audit](#symbol-family-audit).
3. **Residual magic numbers and hardcoded offsets** —
   [#residual-magic-numbers](#residual-magic-numbers).
4. **Global-label documentation and localization review** —
   [#global-label-review](#global-label-review).
5. **Readability self-audit** on the highest-fanout corridor
   touched recently — [#readability-self-audit](#readability-self-audit).
6. **Systems-overview promotion review** — confirm any
   `*_DX_Systems.md` edit cleared the promotion and abstraction rules at
   [DOCUMENTATION.md#dx-systems-scope](DOCUMENTATION.md#dx-systems-scope);
   otherwise revert it and route the facts to the appropriate current-state
   artifact.
7. **Static readability debt audit** —
   [#static-readability-debt-audit](#static-readability-debt-audit).

Only after all seven turn up nothing actionable should the agent
conclude that static work is exhausted and runtime evidence
([#static-vs-runtime-gaps](QUALITY_REVIEW.md#static-vs-runtime-gaps)) is the next
move.

<a id="stale-placeholder-audit"></a>
## Stale Placeholder, Value, and Address-Name Audits

Sweep authored asm and docs for placeholder name patterns whose
semantics may now be known. Source the project config first so
`${ASM_FILE}` and `${DOC_ROOT}` resolve to the active project:

```sh
source scripts/project_common.sh && load_project_conf <slug>

# Placeholder / value-coded labels — case-insensitive, allow optional
# underscore between prefix and digits, require the suffix to start with
# at least one decimal digit (so semantic names like ZP_TitleModeActive
# and @@nmiStateDefault aren't flagged just because they happen to start
# with hex letters), accept up to 3 more hex chars, and terminate before
# any further hex char so embedded forms like Group0600Slot are still
# captured. PCRE2 lookahead requires `-P`.
rg -Pni '(state|mode|field|group|page|addr|arm|slot|cmd|phase)_?\d[0-9a-f]{0,3}(?![0-9a-f])' \
  "${ASM_FILE}" "${DOC_ROOT}"

# Hex-suffixed names where a semantic root is likely available
rg -n "\\b[A-Z][A-Za-z]+_?[0-9A-F]{2,4}\\b" "${ASM_FILE}" | rg -v "L[0-9A-F]{4,5}"
```

Treat hits as cleanup candidates: rename to the semantic name if
known, otherwise mark the placeholder explicitly as future debt in
`WORKING_NOTES.md`. The placeholder-policy rule itself lives at
[ASM_STYLE.md#placeholder-policy](ASM_STYLE.md#placeholder-policy);
do not restate it here.
<a id="symbol-family-audit"></a>
## Incomplete Symbol-Family Audits

A symbol family is "incomplete" when some members are named (e.g.
`OBJECT_STATE_ACTIVE`, `OBJECT_STATE_DYING`) but other observed
values of the same byte remain raw hex. After a partial symbolize,
sweep for the missing members:

```sh
source scripts/project_common.sh && load_project_conf <slug>

# Find candidate state/mode/cmd cluster sites still using raw immediates.
# Match the hex/decimal/binary forms used by the magic-number audit; STA
# never takes an immediate operand on 6502, so it is omitted.
rg -n "(LDA|LDX|LDY|CMP|CPX|CPY|AND|ORA|EOR) #(\\$[0-9A-F]{2}|[0-9]+|%[01]{1,8})\\b" "${ASM_FILE}" \
  | rg -v "STATE_|MODE_|CMD_|PHASE_"
```

For each hit, decide:

- If the value belongs to a known family member, name it and
  replace at the callsite.
- If the value is a parity-preserved bug, document it inline per
  [DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments)
  and add a registry entry per
  [#parity-bug-registry](QUALITY_REVIEW.md#parity-bug-registry); do not record it
  as a `WORKING_NOTES.md` open question.
- If the value's role is unknown, add it to the family's
  open-questions block in `WORKING_NOTES.md` with the
  producer/consumer pair.

Symbol-family naming conventions (prefix families, single-purpose
overlays) live at
[ASM_STYLE.md#naming-conventions](ASM_STYLE.md#naming-conventions)
and [ASM_STYLE.md#state-action-constants](ASM_STYLE.md#state-action-constants);
this section governs *finding* incomplete families, not how to
name them.
<a id="residual-magic-numbers"></a>
<a id="residual-magic-number-and-hardcoded-offset-review"></a>
## Residual Magic-Number and Hardcoded-Offset Review

After the constantization sweep is "complete" per KPI, scan for
residual magic numbers that escaped. Use `constant_kpi.sh`'s
detail-output mode rather than a raw `rg` pass — it consumes
`constant_magic_allowlist.csv` with full
(label, mnemonic, immediate) tuple awareness, so already-disposed
sites are excluded correctly and you only see truly unresolved
work. Pass `${KPI_FILE}` as the second argument so the script can
locate the allowlist next to it:

```sh
source scripts/project_common.sh && load_project_conf <slug>

# Per-site detail for residual magic immediates, allowlist-aware.
# Each line is "<line>:<label>:<mnemonic>:<immediate>". Hex, decimal,
# and binary immediates are all captured by the KPI itself.
constant_detail_file="$(mktemp)"
trap 'rm -f "${constant_detail_file}"' EXIT
KPI_DETAIL_FILE="${constant_detail_file}" \
  bash scripts/constant_kpi.sh "${ASM_FILE}" "${KPI_FILE}"
cat "${constant_detail_file}"

# Hardcoded structured-field offsets where pointer shape is known
rg -n "LDY #(\\$[0-9A-F]{2}|[0-9]+)\\b" "${ASM_FILE}"

# Hardcoded loop bounds / counter literals where label math would work
rg -n "(CPY|CPX) #(\\$[0-9A-F]{2}|[0-9]+)\\b" "${ASM_FILE}"
```

For each hit, pick exactly one of three dispositions:

1. **Symbolize.** Replace with the canonical symbolic form using
   the relevant rule:
   - Counter and length expressions —
     [ASM_STYLE.md#label-math](ASM_STYLE.md#label-math).
   - Hardcoded length / counter elimination —
     [DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination).
   - Structured-field offsets —
     [ASM_STYLE.md#structured-field-offsets](ASM_STYLE.md#structured-field-offsets).
   - Hardware constants and bitmasks —
     [ASM_STYLE.md#hardware-constants](ASM_STYLE.md#hardware-constants).
2. **Allowlist.** When the raw literal is intentionally clearer
   than any symbol (a true counter limit with no nameable
   semantics, an indexing micro-loop, etc.), add a row to
   `docs/reverse_engineering/inventory/constant_magic_allowlist.csv`
   with the rationale. The KPI suite reads the allowlist so future
   passes do not re-flag it.
3. **Parity-preserved encoding.** When the literal is a
   parity-preserved bug or a parity-preserved redundant
   instruction, annotate per the canonical rules:
   - parity-preserved expressions —
     [DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination)
     (symbolic expression encoding) plus the inline-comment format
     at [DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments)
     and the registry at [#parity-bug-registry](QUALITY_REVIEW.md#parity-bug-registry);
   - parity-preserved redundant instructions / tail calls —
     [ASM_STYLE.md#tail-call-annotations](ASM_STYLE.md#tail-call-annotations).

`project-maturity-check` warns on `strict_active_magic_immediates == 0` with an
empty allowlist — an over-constantization smell (every literal symbolized rather
than judged).

<a id="pointer-byte-consolidation-audit"></a>
## Pointer-byte Consolidation Audit

QUALITY_REVIEW owns the project-wide pointer-byte consolidation audit.
Corridor passes apply the recipes to the sites they touch (see
[DATA_RECOVERY.md#computed-pointer-recovery](DATA_RECOVERY.md#computed-pointer-recovery));
this audit handles the remaining sites across the project.

Run once symbolization has stabilized (raw-address debt at or near zero,
high-use RAM/ZP owners named) so the recipes match cleanly; not gated on
any phase.

The five DATA_RECOVERY recipes produce *candidates*, not proven
pointers. Execute the audit in four stages:

1. **Collect candidates.** Run each of the five recipes at
   [DATA_RECOVERY.md#computed-pointer-recovery](DATA_RECOVERY.md#computed-pointer-recovery)
   against the whole project and capture every hit. Treat the output as
   a candidate list, not a worklist.
2. **Classify each candidate.** Mark every site as one of:
   - *proven pointer* — pointer construction is unambiguous and the
     target resolves to a real semantic label, a `RAM_*Base` symbol, or known
     field offset;
   - *unresolved plausible pointer* — pointer shape matches but the
     target is not yet stable enough to substitute; defer with an
     `inferred` annotation and a `WORKING_NOTES.md` entry;
   - *non-pointer* — false positive from the recipe's grep; no code
     annotation needed. Only record the candidate in `WORKING_NOTES.md`
     when it recurs across audit runs or is genuinely ambiguous; do not
     create a parallel roster file.
3. **Group actionable candidates by corridor.** Bin every *proven
   pointer* under one primary owning corridor (the subsystem with the
   dominant consumer/producer for that site). Note secondary corridors on
   the same bin so one batch covers cross-corridor reviewers without
   processing the site twice.
4. **Process and verify one corridor batch at a time.** For each
   corridor bin, apply the substitution, run the corridor batch's diff
   review, then run parity verification before moving to the next
   corridor — even when the underlying mapping is globally invariant;
   see
   [PASS_WORKFLOW.md#batching-and-commit-boundaries](PASS_WORKFLOW.md#batching-and-commit-boundaries).

### Named pointer tables

Confirm every pointer-table label (`...PtrTable`, `...Pointers`) a pass opens has
a symbolic body, not a raw `.DB` lo/hi run — the name proves the entries are
pointers even where the consumer-proof audit misses them (copied `.DW` block plus
indirect `[ZP],Y`). `pointer_table_body_check.py` lists offenders
([TOOLING.md](TOOLING.md#pointer-table-relocation-gate)).

<a id="global-label-review"></a>
## Global-Label Documentation and Localization Review

The procedure-doc and global-code-label KPIs measure coverage; this
audit is the qualitative pair. The KPI script aggregates counts by
default; for the per-label walk, set `KPI_DETAIL_FILE` so the
script preserves its internal undocumented list:

```sh
source scripts/project_common.sh && load_project_conf <slug>

# Aggregate counts (default behavior)
bash scripts/global_code_label_doc_kpi.sh "${ASM_FILE}"

# Per-label detail: one line per undocumented global label as
# "<line>:<label>". Use mktemp (no PROJECT_NAME interpolation) so
# project slugs with spaces or shell-special characters cannot break
# the path; clean up after reading.
detail_file="$(mktemp)"
KPI_DETAIL_FILE="${detail_file}" \
  bash scripts/global_code_label_doc_kpi.sh "${ASM_FILE}"
cat "${detail_file}"
rm -f "${detail_file}"
```

For each undocumented or thinly-documented global label (read the
header band manually to judge thinness, since the KPI counts a
single non-empty comment line as "documented"):

- **Could it be localized?** If it is reachable only as a
  branch/fallthrough target inside one routine and has no
  cross-routine `JSR` / `JMP` callers, convert it to an `@@` local
  label — canonical rule at
  [ASM_STYLE.md#local-global-labels](ASM_STYLE.md#local-global-labels).
  Verify the call graph from `xref_with_data.json` rather than by
  text search.
- **If it must stay global, does it need a header?** Apply the
  procedure-comment rules at
  [DOCUMENTATION.md#procedure-comments](DOCUMENTATION.md#procedure-comments).
  Add one only for a non-obvious contract or public-entry role; a semantic name
  and clear callers may be sufficient. Do not write generic placeholder
  headers.
- **Is the global label the entry to an inline return-table
  dispatch?** If so, document the dispatcher contract per
  [DATA_RECOVERY.md#code-pointer-recovery](DATA_RECOVERY.md#code-pointer-recovery).

Naming and scope rules (when `@@` is visible, what targets must
stay global) live at
[ASM_STYLE.md#local-global-labels](ASM_STYLE.md#local-global-labels);
this section governs the qualitative review, not the spelling.
<a id="deep-confidence-passes"></a>
## Optional Deep-Confidence Passes

After baseline completion (gold-standard machine gates green plus
[#readability-self-audit](#readability-self-audit) on the last
touched corridor), prioritize the following deep-confidence work:

1. **Per-kind state/action transition matrices.** For each named
   state-machine family, produce a writer/reader matrix showing
   every observed value and the transition triggers. Surfaces
   missing family members for
   [#symbol-family-audit](#symbol-family-audit).
2. **Producer/consumer ownership comments on packed regions.**
   Annotate each packed table (audio, motion, metasprite, script,
   etc.) with the routines that consume it, and — when the table
   is built or mutated at runtime — the routines that construct or
   mutate it. Most ROM tables are immutable, so the consumer half
   is the usual product; do not invent writers for static tables.
   Follow
   [DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination)
   for boundary labels and
   [DOCUMENTATION.md#data-label-format](DOCUMENTATION.md#data-label-format)
   for the comment layout.
3. **Instrumented trace notes for unresolved fields.** Convert
   open `WORKING_NOTES.md` questions into trace plans under
   [#static-vs-runtime-gaps](QUALITY_REVIEW.md#static-vs-runtime-gaps); promote
   confidence only after the trace captures evidence per the
   confidence-promotion workflow there.
4. **Consolidate terminology in `TERMINOLOGY_CROSSWALK.md`.**
   Merge synonyms, retire abandoned placeholders, and reconcile
   the in-asm vocabulary against the canonical crosswalk per
   [DOCUMENTATION.md#terminology-crosswalk](DOCUMENTATION.md#terminology-crosswalk).
   A separate `GLOSSARY.md` is only worth introducing when it adds
   distinct developer-facing value over the crosswalk; otherwise
   keep terminology consolidation inside the crosswalk.
These passes are optional in the sense that they sit beyond the
gold-standard floor; they are still subject to the same closeout
gates (parity, scorecard sync, docs/process checks) as any other
pass.
