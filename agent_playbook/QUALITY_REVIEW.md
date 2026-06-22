# QUALITY_REVIEW Playbook

This playbook is the canonical home for post-pass and project-level review procedures — readability self-audit, gold-standard assessment, KPI interpretation, the expanded reviewer simulation, stale-placeholder / symbol-family / residual-magic-number / global-label audits, the project-wide pointer-byte consolidation audit, optional deep-confidence passes, and static-versus-runtime gap classification. The root `AGENTS.md` keeps the short Reviewer Simulation Checklist; this file provides the thorough final-tail and project-review procedure.

## Ownership

This playbook owns post-pass and project-level review procedures:

- readability self-audit
- gold-standard assessment
- KPI interpretation and limitations
- reviewer simulation expansion
- stale placeholder/value/address-name audits
- incomplete symbol-family audits
- residual magic-number and hardcoded-offset review
- project-wide pointer-byte consolidation audit
- global-label documentation/localization review
- optional deep-confidence passes
- static-versus-runtime-gated gap classification
- semantic-claims ledger (maturity/gold-closeout evidence model)

The root `AGENTS.md` retains the short reviewer simulation checklist; this
file provides the thorough final-tail and project-review procedure. Quality
checks may link to rules in other playbooks but do not redefine them.

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
   self-audit at [#readability-self-audit](#readability-self-audit)
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
   an inventory, not a quality score.
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
   and KPI filler fail this item.
8. **Major data regions include format and index comments.**
9. **Onboarding docs are complete and cross-linked**
   (`ONBOARDING.md`, `QUICK_REFERENCE.md`, `MEMORY_MAP.md`,
   and promoted subsystem `*_DX_Systems.md`). A not-yet-promoted systems
   scaffold is acceptable while semantic work remains; speculative expansion
   is not.
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
17. **No obvious derivable counts/bounds** remaining as raw
    literals in executable logic when table/record label math
    would be clearer.
18. **Systems-overview promotion and abstraction are correct.**
    `*_DX_Systems.md` remains minimal until stable names, ownership, control
    flow, and format boundaries exist. A promoted overview contains no
    unresolved `LXXXX`, raw RAM/ZP inventory, boot-step walkthrough,
    helper-by-helper narration, hypotheses, or future-pass planning. Route
    provisional material to `WORKING_NOTES.md` or process artifacts and link
    detailed formats/state machines instead of embedding them.
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

Only after all six turn up nothing actionable should the agent
conclude that static work is exhausted and runtime evidence
([#static-vs-runtime-gaps](#static-vs-runtime-gaps)) is the next
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
rg -n "\\b[A-Z][A-Za-z]+_?[0-9A-F]{2,4}\\b" "${ASM_FILE}" | rg -v "L[0-9A-F]{4}"
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
  [#parity-bug-registry](#parity-bug-registry); do not record it
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
     and the registry at [#parity-bug-registry](#parity-bug-registry);
   - parity-preserved redundant instructions / tail calls —
     [ASM_STYLE.md#tail-call-annotations](ASM_STYLE.md#tail-call-annotations).

<a id="pointer-byte-consolidation-audit"></a>
## Pointer-byte Consolidation Audit

QUALITY_REVIEW owns the project-wide pointer-byte consolidation audit.
Corridor passes apply the recipes to the sites they touch (see
[DATA_RECOVERY.md#computed-pointer-recovery](DATA_RECOVERY.md#computed-pointer-recovery));
this audit handles the remaining sites across the project.

Run when enough symbolization has stabilized that the recipes match
cleanly (typically once raw-address debt is at or near zero and high-use
RAM/ZP owners are named). The audit is not gated on any phase.

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
   pointer* under exactly one primary owning corridor — the
   routine/data subsystem with the dominant consumer/producer
   relationship for that site. Note any secondary corridors as
   dependencies or review scope on the same bin so the corridor batch
   covers cross-corridor reviewers without processing the site twice.
4. **Process and verify one corridor batch at a time.** For each
   corridor bin, apply the substitution, run the corridor batch's diff
   review, then run parity verification before moving to the next
   corridor — even when the underlying mapping is globally invariant;
   see
   [PASS_WORKFLOW.md#batching-and-commit-boundaries](PASS_WORKFLOW.md#batching-and-commit-boundaries).

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
   [#static-vs-runtime-gaps](#static-vs-runtime-gaps); promote
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
covered by [#reviewer-simulation](#reviewer-simulation):

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

Static analysis eventually plateaus on every project. This section
turns the residual uncertainty into a tractable backlog: classify
each open question, schedule the right evidence capture, and
promote confidence only once the capture lands.

### Confidence promotion criteria
- `high confidence (static)` = control/data flow proves correctness.
- `high confidence (runtime)` = repeated trace evidence.
- If runtime frequency unknown, document as "statically reachable; runtime
  frequency pending."

The root [AGENTS.md#confidence-protocol](../AGENTS.md#confidence-protocol)
defines the `high` / `medium` / `inferred` semantics; the
(static)/(runtime) qualifier above scopes the evidence channel.

### Operational classification procedure

For each unresolved item — a residual `inferred` annotation, an
open `WORKING_NOTES.md` question, an incomplete symbol-family
member, or a parity-preserved bug whose root cause is unknown:
1. **Identify the gap source.** Enumerate from three places: the
   `inferred` annotations remaining in asm/docs (`rg -n
   'inferred' "${ASM_FILE}" "${DOC_ROOT}"`), `WORKING_NOTES.md`
   open-questions blocks, and the parity-bug registry's
   "root cause unknown" entries.
2. **Classify the gap as static or runtime.**
   - **Static-resolvable.** The control-flow and data-flow
     evidence needed to close the gap exists in the asm — the
     work is to read it carefully (cross-routine call tracing,
     pointer-table resolution, structured-field offset proof).
     Static-resolvable gaps stay in `WORKING_NOTES.md` and go
     into the next [#reviewer-simulation](#reviewer-simulation)
     pass.
   - **Runtime-gated.** Closing the gap requires observing the
     ROM running — the value depends on user input, RNG, frame
     timing, scenario state, or external state the disassembly
     cannot reach by reading. Runtime-gated gaps move out of
     `WORKING_NOTES.md` into a trace plan.
3. **Schedule the evidence capture.** For runtime-gated gaps,
   author a trace plan under
   `docs/reverse_engineering/` (capture runbook + scenario + the
   producer/consumer label pair under observation) per
   [PASS_WORKFLOW.md#pass-closeout → Runtime evidence workflow](PASS_WORKFLOW.md#pass-closeout).
   Each trace plan names the expected signal and the
   confidence-promotion criteria that the captured evidence has
   to satisfy.
4. **Promote confidence on capture.** Once evidence lands, apply
   the [Confidence Protocol](../AGENTS.md#confidence-protocol)
   promotion sweep: revisit prior `inferred` annotations, drop
   the tag where the evidence now proves the role, preserve any
   explanatory comment (drop the uncertainty marker, not the
   documentation). A single capture only supports the level
   warranted by the evidence — promote to `medium confidence
   (runtime)` if one trace agrees; `high confidence (runtime)`
   requires repeated traces across scenarios per the criteria
   above. Do not pre-emptively promote — the capture has to
   actually land first.
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
