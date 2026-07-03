# NEW_PROJECT Playbook

This playbook is the canonical home for new-project intake, scaffolding, ROM and header validation, warning-baseline bootstrap, reference-document processing, the first-three-pass architecture, and new-project autonomy defaults. The root `AGENTS.md` keeps only the two universal constraints (ROMs come from the user; mapper/PRG/CHR size is derived from the iNES header).

## Ownership

This playbook owns project bootstrapping:

- toolchain prerequisites
- ROM support matrix and header intake
- project scaffolding
- initial assembly generation
- reference-document processing and terminology crosswalk seeding
- warning-baseline bootstrap and intake acceptance checklist
- first-three-pass architecture
- new-project autonomy defaults

Code/data recovery work performed during intake routes to
[DATA_RECOVERY.md](DATA_RECOVERY.md); the terminology crosswalk artifact itself
is owned by [DOCUMENTATION.md](DOCUMENTATION.md#terminology-crosswalk).

## Playbook Sections

<a id="starting-a-new-project"></a>
## Starting a New Project

The end-to-end intake flow for a new game project:

1. Verify the host toolchain — see [#prerequisites](#prerequisites).
2. Identify the game slug and locate the reference ROM file — see
   [#rom-intake](#rom-intake). Knowing the support matrix at
   [#rom-support-matrix](#rom-support-matrix) up front helps you
   recognize obviously unsupported ROMs early, but the enforcing gate
   runs at step 5.
3. Scaffold the project — see [#project-scaffolding](#project-scaffolding).
4. Place the reference ROM inside the scaffold at
   `projects/<slug>/reference/<slug>.nes`.
5. Generate the initial assembly from the ROM — see
   [#initial-assembly-generation](#initial-assembly-generation). This is
   the gate that validates the ROM against the support matrix; an
   unsupported ROM fails here with an explicit message naming the
   offending field. Stop and surface the limitation to the user if it
   fails — do not proceed with intake.
6. Audit hidden-code and indirect-dispatch candidates. Record `none`
   or `configured` recovery status in `project.conf`, track any
   controls under `config/nesrev/`, and regenerate until stable — see
   [#initial-assembly-generation](#initial-assembly-generation),
   [#nesrev-intake-sanity-gate](#nesrev-intake-sanity-gate), and
   [DATA_RECOVERY.md#code-pointer-recovery](DATA_RECOVERY.md#code-pointer-recovery).
7. Run `make project-intake PROJECT=<slug>`, then bootstrap the warning
   baseline and initialize the scorecard — see
   [#warning-baseline-bootstrap](#warning-baseline-bootstrap).
8. Confirm intake acceptance and commit the intake baseline — see
   [#intake-acceptance](#intake-acceptance) and [#intake-baseline-commit](#intake-baseline-commit).
9. Process game reference documentation, then commit the reference-prep
   artifacts — see [#reference-document-processing](#reference-document-processing)
   and [#reference-prep-commit](#reference-prep-commit).
10. Only after step 9 begin the first semantic naming pass.
11. Apply [#first-three-pass-architecture](#first-three-pass-architecture)
    for the first three semantic passes unless code-pointer recovery still
    needs to dominate.
12. Default first-session scope is maximum useful progress without waiting
    for further user feedback — see [#new-project-autonomy](#new-project-autonomy).

<a id="prerequisites"></a>
## Prerequisites

Verify the host toolchain before starting a new project:

```sh
make project-doctor
```

The check reports each required tool's status and exits non-zero if any
are missing. Required: `java`, `javac`, `xasm` (6502 assembler), `bash`,
`python3`, `rg` (ripgrep), `od`, `dd`, `awk`, `sed`, `perl`, `make`,
`git`. Optional but recommended: `jq` (used for inspecting generated
pass artifacts), `shellcheck` (used when editing scripts). A
POSIX-compliant base toolset (`cmp`, `mktemp`, `sort`, `tee`, `wc`,
`tr`, `head`, `cat`, `grep`, `find`, `basename`, `dirname`) is
presumed present and not checked individually; hosts missing these are
not supported. The script verifies presence only, not minimum versions
or capabilities; the hint field names a standard install source for
each missing tool.

<a id="rom-support-matrix"></a>
## ROM Support Matrix

NESrev's regenerator currently supports a narrow slice of NES ROMs. A
ROM is supported when **all** of these hold against its iNES header:

| Field | Header byte(s) | Supported value | Notes |
|---|---|---|---|
| Magic | $00-$03 | `4E 45 53 1A` | iNES header marker |
| Header format | bits 2-3 of $07 | `0b00` (iNES 1.0) or `0b10` (NES 2.0) | Reserved/legacy variants (`0b01`, `0b11`) are rejected. NES 2.0 is accepted only when the decoded mapper and ROM sizes still match the matrix below |
| Mapper | high nibble of $06 \| high nibble of $07 \| NES 2.0 byte $08 low nibble | `0` (NROM) | Other mappers are rejected; see error message |
| PRG size | $04 plus NES 2.0 byte $09 low nibble | `1` or `2` units = 16 or 32 KB | NROM-128 mirrors at `$C000`; NROM-256 maps at `$8000` |
| CHR size | $05 plus NES 2.0 byte $09 high nibble | `0` or `1` unit (0 or 8 KB) | CHR-RAM or 8 KB CHR-ROM |
| Trainer flag | bit 2 of $06 | `0` or `1` | Optional 512-byte trainer is skipped on disassembly |
| Container length | total file size | exactly `16 + trainer + PRG + CHR` | Truncated containers fail; trailing bytes also fail unless `ALLOW_TRAILING_BYTES=1` is set after manual audit |

`make project-regenerate-asm` enforces this matrix in
[`scripts/project_regenerate_asm.sh`](../scripts/project_regenerate_asm.sh)
and fails with an explicit message naming the offending field plus a
pointer back to this anchor. The check runs only after the project is
scaffolded and the ROM is placed (steps 3-5 of [#starting-a-new-project](#starting-a-new-project)),
so a quick eyeball of the iNES header before scaffolding can save a
round trip on obviously unsupported ROMs. If a ROM falls outside the
matrix, do not proceed with intake — surface the limitation to the
user and stop; nesrev cannot disassemble it correctly.

<a id="rom-intake"></a>
## ROM and Header Intake

Slug identification and ROM placement (steps 2 and 4 of
[#starting-a-new-project](#starting-a-new-project)) happen before the
support-matrix gate fires at step 5; the slug is needed to scaffold
the project. At that early stage ask the user only for what cannot be
discovered locally — normally the intended game/title and whether
reference docs/ROM will be provided if absent. Derive PRG/CHR size,
ROM container length, code-pointer state, and prior-project analogue
from the ROM header and existing artifacts, not the user. Once step 5
confirms the matrix, no further ROM-identity questions are needed.

Never source or download commercial ROM/reference material yourself.
The user must provide ROMs, manuals, and reference docs outside
git-tracked source.
<a id="project-scaffolding"></a>
## Project Scaffolding

Scaffold the new project with the chosen slug:

```sh
make project-init PROJECT=<slug>
```

This is the canonical entry point. The Make target wraps
[`scripts/new_project.sh`](../scripts/new_project.sh), which creates the
canonical project directory layout under `projects/<slug>/` plus the
`docs/reverse_engineering/` shell. See the script for the exact
generated paths; this playbook does not duplicate them.

New scaffolds include `SEMANTIC_CLAIMS.md` and set `SEMANTIC_CLAIMS_REQUIRED="1"`
in `project.conf`, opting into strict semantic-claims maturity. The ledger may
stay sparse until gold closeout; the model and checker live at
[QUALITY_REVIEW.md#semantic-claims](QUALITY_REVIEW.md#semantic-claims).
<a id="initial-assembly-generation"></a>
## Initial Assembly Generation

Generate the initial assembly from the reference ROM:

```sh
make project-regenerate-asm PROJECT=<slug>
```

Before intake, complete hidden-code/code-pointer discovery. Record
`NESREV_RECOVERY_STATUS="none"` when no controls are needed; otherwise
track them under `config/nesrev/`, set the matching `NESREV_*_FILE`
paths, and use `"configured"`. The base command must reproduce the
assembly; command-line paths are experimental overrides only. Formats
and configuration live at
[TOOLING.md#nesrev-controls](TOOLING.md#nesrev-controls).

Once discovery and regeneration are stable, run:

```sh
make project-intake PROJECT=<slug>
```

`make project-intake` may fail the first time if the
automated bundle cannot resolve a generation artifact. Treat intake as
an iterative loop, not a one-shot — see
[#nesrev-intake-sanity-gate](#nesrev-intake-sanity-gate) below.
Code-pointer recovery mechanics live at
[DATA_RECOVERY.md#code-pointer-recovery](DATA_RECOVERY.md#code-pointer-recovery).

<a id="nesrev-intake-sanity-gate"></a>
## NESrev Intake Sanity Gate

**Precondition:** step 5 enforces the iNES header and container length.
Resolve any failure, including the audited
[#trailing-byte-override](#trailing-byte-override), before this loop.

Intake refuses the scaffold's `pending` recovery state. Complete
discovery first, then run intake; fix the first failing gate,
regenerate when controls change, and repeat until green.

The loop steps in order of typical failure:

1. **Run intake.**
   ```sh
   make project-intake PROJECT=<slug>
   ```
2. **Diagnose parity.** If intake's verify step reports a binary
   mismatch, run the canonical parity-drift wrapper to localize the
   divergent bytes before regenerating:
   ```sh
   make project-compare PROJECT=<slug>
   ```
   Diagnostic options and the parity-drift workflow live at
   [TOOLING.md#parity-drift](TOOLING.md#parity-drift).
3. **Fix generation artifacts first (no semantic refactors yet).**
   Common failures are bad operand/branch rendering or missing
   recovery controls. Update tracked controls and `project.conf` per
   [TOOLING.md#nesrev-controls](TOOLING.md#nesrev-controls), then:
   ```sh
   make project-regenerate-asm PROJECT=<slug>
   ```
   After a control change, review warning-baseline additions/removals
   on the next intake; do not accept drift silently.
4. **Rerun intake.** Repeat from step 1 until intake exits zero with
   the tracked control configuration.
5. **Only after intake parity is green** start naming, label, or
   constant passes.

<a id="trailing-byte-override"></a>
### Trailing-byte override

When a ROM's container is larger than the iNES header declares, the
regenerator refuses by default. Audit the trailing bytes before
proceeding. The override is only valid when the audit confirms the
trailer is safely ignorable (dumper metadata, padding, or a known
harmless trailer). If the bytes are meaningful or unknown, **do not
set the override** — `ALLOW_TRAILING_BYTES=1` silently discards
them; stop and either obtain a clean dump or treat the project as
out of scope until the trailer's semantics are designed in.

Record the audit as a durable, reproducible artifact:

1. Inspect the trailer from the repository root:
   `od -An -tx1 -j <expected_size> projects/<slug>/reference/<slug>.nes`.
   Note the byte count and any recognizable signature/pattern.
2. Add a `Trailing-byte audit` entry to
   `projects/<slug>/docs/reverse_engineering/ONBOARDING.md` (or
   `WORKING_NOTES.md` if ONBOARDING is finalized) with these fields,
   since the ROM is not git-tracked:
   - **ROM sha256**: bind the audit to the exact dump using the
     doctor-checked `python3` (no extra dependency):
     ```sh
     python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' \
       projects/<slug>/reference/<slug>.nes
     ```
   - **Trailer sha256 or inline byte dump**: the same one-liner
     against a `dd`-extracted trailer, or the full `od` output above
     when the trailer is short.
   - **Trailer length** in bytes (must match the
     `ALLOW_TRAILING_BYTES` warning).
   - **Audit conclusion** — must explicitly classify the trailer as
     ignorable (`safe to ignore`, `dumper metadata`, `confirmed
     padding`, ...). Meaningful or unknown trailers disqualify the
     override; record the finding but do not proceed.
   - **Date and reviewer**.
3. Re-run the regenerator with the override:
   ```sh
   ALLOW_TRAILING_BYTES=1 make project-regenerate-asm PROJECT=<slug>
   ```
4. The regenerator emits a warning naming the ignored byte count;
   confirm it matches the audit entry, then proceed with intake.
<a id="reference-document-processing"></a>
## Reference Document Processing

After `make project-intake` is green and before any semantic naming
pass, review external sources in `docs/game_reference/` and put
authored term extraction and mappings under `docs/crosswalk/`, never
under the ignored source tree. The
canonical workflow — what to collect, when the crosswalk gate fires,
what to record if no reference docs are available, and how to keep the
crosswalk current as the project matures — lives at
[DOCUMENTATION.md#terminology-crosswalk](DOCUMENTATION.md#terminology-crosswalk)
(Mandatory game-reference intake + Crosswalk synchronization protocol);
this section just orders that work within the larger new-project intake
flow.
<a id="warning-baseline-bootstrap"></a>
## Warning Baseline Bootstrap

`make project-intake` already assembles the project and, if
`WARNING_BASELINE.txt` is empty, seeds it with every current
`defined but not used` symbol. Each auto-seeded line gets the
placeholder rationale `REVIEW REQUIRED: intake auto-seed; replace with
symbol-specific rationale`.
The intake wrapper then runs `project-verify` against that seeded
baseline. The docs gate rejects any remaining `REVIEW REQUIRED`
rationale, so a warning-producing fresh ROM may intentionally fail the
first `project-intake` run after seeding. Curate the seeded rationales,
then rerun `make project-intake PROJECT=<slug>` to complete intake.

The agent's bootstrap work after the wrapper finishes:

1. Review the auto-seeded entries in `WARNING_BASELINE.txt` and
   replace the placeholder rationale with a specific reason for each
   symbol that should stay retained.
   For NESrev-emitted labels at the start of orphan `.DB` regions,
   consumer evidence is often unavailable at intake. A valid provisional
   rationale may therefore be shape-based: cite the observable byte
   shape or local boundary, state that the live consumer is not yet
   recovered, and name the future corridor that must revisit it. Do not
   claim stable semantics until code or data-flow evidence proves them.
2. For any auto-seeded entry that is not genuinely intentional,
   resolve the underlying warning at the source first — either give
   the symbol a real assembler-visible reference (a `JSR`, `JMP`,
   load, table entry, etc.) or remove the symbol — then delete the
   matching line from `WARNING_BASELINE.txt`. A `Used by:` comment is
   documentation, not a reference, and does not clear the warning.
   Deleting the baseline entry before the warning is gone will fail
   verification.
3. Confirm that `QUICK_REFERENCE.md`'s Assembler Warnings section
   still points at `WARNING_BASELINE.txt` as the single per-symbol
   registry; the scaffold seeds that reference and the registry itself
   is not duplicated in the quick reference.
4. Rerun `make project-intake` so the verifier confirms the curated
   baseline still matches the current build.
After bootstrap, treat baseline drift as a required review item —
do not ignore changes silently.
`scripts/new_project.sh` writes `PROGRESS_SCORECARD.md` with the
`Intake baseline` row already present (pass_id 0) and KPI cells empty.
Populate or confirm that row from the intake metrics; do not create a
new row for the intake baseline.
<a id="intake-acceptance"></a>
## Intake Acceptance Checklist

"Intake green" is not the same as "project healthy." Confirm all of:

1. `make project-intake PROJECT=<slug>` exits zero. This wrapper invokes
   `project-verify` with `ALLOW_UNRESOLVED_LXXXX=1`, refreshes the
   inventory, and runs process/docs checks; do not substitute a strict
   `make project-verify` here — semantic naming has not started yet and
   the `LXXXX` gate is intentionally suppressed.
2. `WARNING_BASELINE.txt` matches the current build with no auto-seed
   placeholders left in the rationale column.
3. Recovery discovery is recorded as `none`, or as `configured` with
   every active control tracked under `config/nesrev/` and named in
   `project.conf`. Base-command regeneration reproduces the assembly.
4. `ONBOARDING.md` has final intake/recovery status and no scaffold
   replacement directions. `project-intake` replaces the scaffold's
   setup-oriented First Steps body with a Resuming Work section; if that
   section still reads like setup instructions, intake closeout is not
   finished.
5. The `Intake baseline` row in `PROGRESS_SCORECARD.md` is populated.
   `project-intake` auto-syncs the supported KPI cells
   (`labels_remaining`, `raw_rom_calls_remaining`,
   `raw_indirect_operands_remaining`,
   `hardcoded_counter_sites_remaining`) and fills the empty outcome
   cells (`verify` → `pass (intake-relaxed)` since `ALLOW_UNRESOLVED_LXXXX=1`
   was set, `docs_check` → `pass`; `raw_ptr_immediates_remaining` →
   `not measured`, since no automated KPI computation exists for that
   column yet), plus `rework_items` → `0` and a durable note that the
   intake baseline is captured and semantic naming has not started.
   Cells that were already filled by a human are preserved.

Expected residual debt that does **not** disqualify intake:

- Unresolved `LXXXX` procedure labels — intake and early naming
  corridors may use explicit relaxed verification. Strict-closeout
  semantics live at
  [PASS_WORKFLOW.md#semantic-pass-verification](PASS_WORKFLOW.md#semantic-pass-verification).
- The seven `999999` KPI ceilings the scaffold writes to the project
  config (`MAX_ACTIVE_RAW_LOWADDR`, `MAX_ACTIVE_MAGIC_IMMEDIATES`,
  `MAX_ACTIVE_BRANCH_LITERALS`, `MAX_INFERRED_ANNOTATIONS`,
  `MAX_UNDOCUMENTED_PROCEDURES`, `MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS`,
  `MAX_UNDOCUMENTED_DATA_LABELS`). They are provisional placeholders
  and stay in place until the project approaches maturity. Procedure/global
  code-label ceilings are review inventories, not a mandate to reach zero by
  adding comments; never tighten them through filler.
- A populated `WARNING_BASELINE.txt` containing baselined symbols.

Do not declare the project healthy or run
`make project-maturity-check` against an intake baseline — that gate is
designed to fail until the maturity dimensions at
[PASS_WORKFLOW.md#project-maturity-dimensions](PASS_WORKFLOW.md#project-maturity-dimensions)
have closed.
<a id="clean-baseline-commit"></a>
<a id="intake-baseline-commit"></a>
## Intake Baseline Commit

Once the acceptance checklist passes, commit the intake baseline. This
is the first of two intake commits; reference-document processing comes
next and is committed separately so the intake baseline stays
identifiable in history.

<a id="reference-prep-commit"></a>
## Reference Preparation Commit

After [#reference-document-processing](#reference-document-processing)
seeds the terminology crosswalk and any reference-derived artifacts,
commit those changes as a second, separate commit. The first semantic
naming pass should then be its own third commit so both intake stages
remain identifiable in history.
<a id="first-three-pass-architecture"></a>
## First Three-Pass Architecture

These are candidate corridors, not fixed checklists. Each pass selects
one coherent ownership corridor and closes its evidence-supported
dimensions.

1. **Core infrastructure candidate** — one connected reset, NMI, IRQ,
   frame-service, controller, PPU, or OAM corridor; do not bundle
   unrelated infrastructure.
2. **Main control-flow candidate** — one connected game-mode,
   state-dispatch, or frame-lifecycle corridor with its owned RAM/ZP,
   tables, and local control flow.
3. **First major subsystem pass** — one gameplay, rendering, or audio
   corridor closed end-to-end under the
   [high-value pass contract](../AGENTS.md#high-value-pass-contract).
Recovered dispatch/BIT-overlay work joins only its owning corridor;
otherwise schedule it separately.
Do not spend early passes on isolated labels or low-fanout mechanical
cleanup while a core infrastructure routine or a major dispatch/data
corridor is still unnamed.
### Recommender caveat (passes 1-3)

`make project-next-pass` ranks cluster candidates by total reference
fanout with light corridor analysis, so popular MMIO helpers may rank
above architectural anchors on a fresh project. Review the candidates
and use `TARGET=<anchor>` when the default is not the best connected
reset/frame-service, state-dispatch, or major-subsystem corridor.
`next_pass.json` is an evidence-backed candidate backlog, not a
strategic recommendation or authorization to combine unrelated work.
<a id="new-project-autonomy"></a>
## New Project Autonomy Defaults

When starting a new project, make these decisions locally unless
blocked:

- **Mapper / PRG / CHR size:** parse the iNES header during intake and
  use it to set ROM-range assumptions. Do not ask the user whether it
  is NROM-128, NROM-256, or another mapper unless the header is
  missing or contradictory.
- **Prior-project analogue:** choose the analogue by evidence — same
  publisher or early Nintendo engine family first, then similar
  subsystem signatures (audio driver shape, PPU packet parser,
  OAM/metasprite layout), then genre/era. Record the chosen analogue
  in the first semantic pass's scorecard notes using
  `Analogue: <project_slug> (<applied pattern or reason it did not fit>)`.
- **Codepointers:** begin discovery without assuming controls are
  needed. Their absence does not mean the ROM is free of code-pointer
  tables —
  always run the code-pointer recovery discovery per
  [DATA_RECOVERY.md#code-pointer-recovery](DATA_RECOVERY.md#code-pointer-recovery)
  before setting `NESREV_RECOVERY_STATUS="none"`. If discovery finds
  controls, author them under `projects/<slug>/config/nesrev/` and
  reference them from `project.conf`.
- **Reference docs:** use whatever the user supplied under
  `docs/game_reference/`. If none exist and the user has not promised
  to provide them, record the absence explicitly and proceed; do not
  repeatedly ask.
- **Session ceiling:** continue through the next mandatory gate or
  coherent high-value pass. Stop only for missing user-provided
  artifacts, parity drift that needs user judgment, or an explicit
  user pause.
