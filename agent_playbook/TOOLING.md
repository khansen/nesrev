# TOOLING Playbook

This playbook is the canonical home for xasm, NESrev, and project-wrapper tooling — listing/xref options, structured analysis workflow, NESrev regeneration controls, inventory commands, parity-drift diagnostics, the consolidated command reference, exit-code interpretation, and auxiliary-script hygiene. The root `AGENTS.md` keeps only the Mandatory Routing Table entry that names this file.

## Ownership

This playbook owns commands, tool options, and diagnostic procedures:

- xasm listings and xref options
- data-consumer, data-coverage, and index-pattern analysis
- NESrev regeneration controls
- inventory commands
- parity-drift diagnostics
- the canonical command reference
- tool exit codes and debugging
- auxiliary-script hygiene

Other playbooks link to exact tooling sections here rather than copying command
blocks. Minimal root lifecycle commands may appear in `AGENTS.md`; every other
command example lives only here.

## Playbook Sections

<a id="xasm-options"></a>
## xasm Listings and Xref Options

The `xasm` assembler provides `--listing=FILE` to map CPU addresses and
emitted hex bytes to source lines. This is the primary tool for diagnosing
binary drift.

**Prefer JSON format** (`--listing-format=json` or `ndjson`) over plaintext
listings. JSON listings are machine-parseable, handle continuation rows as
first-class records, and can be processed with `jq`/Python instead of
fragile text parsing. Reserve plaintext `.lst` for quick human inspection
only.
```sh
# Preferred: machine-readable listing
xasm --pure-binary --listing=Game.lst.json --listing-format=json Game.asm

# Fallback: human-readable plaintext
xasm --pure-binary --listing=Game.lst Game.asm
```

<a id="xasm-structured-analysis"></a>
## xasm Structured Feature Workflow

Use structured `xasm` outputs through the wrapper workflow. Ad-hoc `xasm`
commands are for debugging only.
### Warm-Up and Closeout

```sh
make project-regenerate-asm PROJECT=<slug>
make project-pass-prep PROJECT=<slug>
make project-next-pass PROJECT=<slug>
make project-pass-start PROJECT=<slug>
make project-pass-closeout PROJECT=<slug>
make project-pass-finish PROJECT=<slug>
```

Optional `KEY=value` arguments (append to the same line):
`project-regenerate-asm` accepts the five hint inputs at
[#nesrev-controls](#nesrev-controls) plus `ALLOW_TRAILING_BYTES=1`
(audited trailer override); `project-pass-start` accepts `PASS=<id>`
and `TARGET=<corridor_anchor_or_notes_plan>`; `project-pass-closeout`
accepts `PASS=<id>`; `project-pass-finish` accepts `PASS=<id>`,
`VERIFY_MODE=strict|relaxed`, `FOCUS=<text>`, and `NOTES=<text>`.
`project-next-pass` refreshes stale cache before emitting evidence buckets;
prep output goes to stderr so `FORMAT=json` stays clean. The
top bucket is not a pass decision; `project-pass-start` records the operator's
selected corridor objective.

### Evidence Order (Mandatory)

1. **Generated pass artifacts** (`inventory/pass/`) — use first for corridor selection, consumer identification, pass resumption, and cluster sizing.
2. **Structured xasm outputs** (JSON/NDJSON listing, xref, audit) — use when pass cache lacks the needed fact.
3. **Raw asm source** — only for final edits, scope checks, declaration-site comments, and control-flow confirmation.
Do not use broad `rg` sweeps or ad-hoc KPI scripts when pass artifacts already provide the information. If you must fall back, report what was missing and why.
### xasm Feature Summary

- `--compare`: fast first-mismatch diagnosis with source mapping; use before full `make project-verify`.
- `--listing-format=json|ndjson`: machine-parseable listing; continuation rows are first-class records.
- `--xref`: generate before rename sweeps. Default: `--xref-include-locals=false --xref-include-anon=false`. Use `--xref-include-owner=true` for lexical ownership.
- `--Werror=unused-equ`: hard blocker during constantization/symbolization. Remove unused `.EQU` in same pass.
- `--audit-raw-addresses`: find residual raw addresses. Preferred wrapper: `make project-audit PROJECT=<slug> FORMAT=json`. Shell-quote `$` in ROM ranges.
<a id="data-consumer-analysis"></a>
## Data-Consumer, Data-Coverage, and Index-Pattern Analysis

`make project-pass-prep` emits baseline parity status, both xref summaries,
owner-enriched xref, and three structured-analysis outputs into
`docs/reverse_engineering/inventory/pass/`. Compatible outputs are bundled into
one xasm process so the wrapper does not repeat the same parse/assemble work;
the filtered generic-label xref summary stays separate because summary context
is computed after the include filter is applied. Only `data_consumers.json` is
loaded by `make project-next-pass` (consumer rollups for generated evidence);
`index_patterns.json` and `data_coverage.json` are manual evidence artifacts.

### Index-pattern analysis

```sh
xasm --pure-binary -o Game.o \
    --analyze-index-patterns \
    --index-patterns-output=docs/reverse_engineering/inventory/pass/index_patterns.json \
    --index-patterns-format=json \
    Game.asm
```

Produces `index_patterns.json` — one record per indexed access site,
including `table_label`, `routine`, `site_addr`, `access_kind`
(`read`/`write`), `access_pattern` (`base`, `base_plus_const`,
`paired_byte_reads`, …), `index_register`, `displacement`, and
`index_value_source_kind`. Useful for finding shared lookup tables,
stride-indexed records, and pointer-table consumers without hand-grepping.

### Data-consumer analysis

```sh
xasm --pure-binary -o Game.o \
    --data-consumers \
    --data-consumers-output=docs/reverse_engineering/inventory/pass/data_consumers.json \
    --data-consumers-format=json \
    Game.asm
```

Produces `data_consumers.json` — one record per data label, aggregating
direct symbol-span accesses: `read_site_count`, `write_site_count`,
`distinct_routine_count`, `observed_constant_displacements`,
`access_patterns`, plus per-site arrays of `read_sites`/`write_sites`
with `routine`, `site_addr`, `displacement`, and `addressing_mode`
(`absolute_x`/`absolute_y`/...). Indirect ZP-pointer consumers are
*not* tracked here — they require manual trace.

### Data-coverage analysis

```sh
xasm --pure-binary -o Game.o \
    --analyze-data-coverage \
    --data-coverage-output=docs/reverse_engineering/inventory/pass/data_coverage.json \
    --data-coverage-format=json \
    Game.asm
```

Produces `data_coverage.json` — for each data label: `declared_start`,
`declared_end_exclusive`, `declared_size`, `covered_ranges`,
`covered_size`, `uncovered_ranges`, `uncovered_size`, `access_count`,
and `has_indexed_accesses_without_exact_coverage`. Useful for spotting
declared spans whose interior bytes have no direct reader (potential
mis-split blobs or hidden consumers).

Prefer these structured outputs over ad-hoc grep when planning a pass;
see also [Evidence Order](#xasm-structured-analysis).

<a id="nesrev-controls"></a>
## NESrev Regeneration Controls

NESrev is the disassembler. It is driven through the
`make project-regenerate-asm` wrapper, optionally fed five recovery
control files that compose. For reproducible projects, keep active
controls under `projects/<slug>/config/nesrev/` and name them in
`project.conf`; the base wrapper command then reloads them
automatically. Use these controls when the linear-trace pass leaves
code unreachable behind indirect dispatch, mis-decodes data blobs, or
fails to recover inline-call payloads.

### Hint file formats

```sh
# codepointers.csv — pipe-delimited. Mapper 0 rows use start = raw PRG
# offset (hex), count = number of pointers. MMC1 rows may instead use
# bank|addr|count when banked CPU context is clearer. Use for contiguous
# CODE-pointer tables: NESrev labels each target AND traces it as code.
# For MMC1 fixed-bank tables whose entries are $8000-$BFFF addresses, each
# entry seeds that CPU address in every non-final PRG bank; the table word
# remains raw because no single label exists.
# start|count
# 0x0008|30
# bank|addr|count
# 0|$8100|12

# datapointers.csv — same shape as codepointers.csv, but targets are DATA
# records. NESrev labels each target so the .DW line reads symbolically, but
# does not trace the bytes at the target as code. Use when a few "lucky"
# records would otherwise mis-decode as plausible instructions (5-byte audio
# period/envelope tables, etc.).
# start|count
# 0x2813|30

# codeentries.txt — one canonical ROM CPU address per line, or bank|addr for
# MMC1 switched-window entries. # and ; start comments. Use for SCATTERED code
# entry points reached via indirect dispatch where the pointer is loaded from
# individual `LDA #imm / STA ZP_PTR` pairs rather than a contiguous table.
# $C22F   ; channel 0 command handler (reached via JMP [$00EB])
# $D187
# bank|addr
# 0|$8120
# 7|$C000

# inlinecalls.csv — pipe-delimited; callee CPU address + payload layout
# descriptor for inline-call patterns (JSR followed by inline bytes the
# callee consumes from the return address). Layout tokens include `u8`,
# `bytes(N)`, `counted8`, `ptr16(data)`, `ptr16(code,+1)`, and repeat
# shorthand such as `ptr16(code)*31`. Use callsite rows when one helper
# has variable record lengths. MMC1 rows
# may use bank|callee|layout for switched-bank callees, or
# bank|callsite|callee|layout when the JSR site is in a specific bank.
# callee|layout
# $C8BB|u8,ptr16(data)
# $C963|bytes(6)
# $EA05|counted8
# callsite|callee|layout
# $C120|$C27C|ptr16(code)*3
# bank|callee|layout
# 0|$8120|u8
# bank|callsite|callee|layout
# 0|$8027|$C27C|ptr16(code)*2

# dataranges.csv — pipe-delimited; explicit data-byte regions NESrev should
# treat as opaque payload rather than trying to decode as instructions. MMC1
# rows may use bank|addr|length for switched-bank data.
# start|length
# $CD20|14
# $D5B6|34
# bank|addr|length
# 0|$9000|32
```

### Wrapper invocation

The reproducible command is always:

```sh
make project-regenerate-asm PROJECT=<slug>
```

Set active paths in `projects/<slug>/project.conf`:

```sh
NESREV_RECOVERY_STATUS="configured"
NESREV_CODEPOINTERS_FILE="projects/<slug>/config/nesrev/codepointers.csv"
NESREV_CODEENTRIES_FILE="projects/<slug>/config/nesrev/codeentries.txt"
NESREV_DATAPOINTERS_FILE=""
NESREV_INLINECALLS_FILE=""
NESREV_DATARANGES_FILE=""
```

Use `NESREV_RECOVERY_STATUS="none"` only after discovery finds no
required controls. The scaffold's `pending` value blocks intake so a
plain linear-trace result cannot be committed accidentally.

`CODEPOINTERS=`, `DATAPOINTERS=`, `CODEENTRIES=`, `INLINECALLS=`, and
`DATARANGES=` command-line values override the
matching configured path for one run. Use overrides to experiment, then move accepted
inputs into `config/nesrev/` and `project.conf` before intake or
commit. Controls under the ignored `reference/` tree are not
reproducible build inputs.

### Configuration notes

- In this repo, local `NESrev` consumes the raw PRG, not the `.nes`
  container.
- `codepointers.csv` / `datapointers.csv` `start` is a raw PRG offset, not a
  `.nes` file offset and not a CPU address.
- `codeentries.txt`, `inlinecalls.csv` callees, and `dataranges.csv`
  starts are CPU addresses in the canonical project ROM range
  (`$C000-$FFFF` for NROM-128 and MMC1 fixed-bank code,
  `$8000-$FFFF` for NROM-256). MMC1 `$8000-$BFFF` targets require
  bank-qualified `codeentries.txt` rows, pointer evidence from within the
  same switched bank, or an explicitly configured code-pointer table whose
  ambiguous entries should be probed across all non-final PRG banks.
- Pick the right hint:
  - contiguous table → code routines: `codepointers.csv`
  - contiguous table → fixed-size data records: `datapointers.csv`
  - scattered indirect-dispatch entries with no static table: `codeentries.txt`
  - JSR-with-inline-payload patterns: `inlinecalls.csv`
  - data ranges NESrev keeps eagerly decoding as instructions: `dataranges.csv`
- All five may be present at once; they compose.
- Seed any new entries discovered during the re-run; NESrev will surface
  additional unreachable labels as it traces deeper.
When to run NESrev regeneration during a Code-Pointer Recovery Pass is
recovery-strategy guidance — see
[DATA_RECOVERY.md#code-pointer-recovery](DATA_RECOVERY.md#code-pointer-recovery).

<a id="inventory-commands"></a>
## Inventory Commands

Inventory snapshots in `docs/reverse_engineering/inventory/` are
machine-readable summaries of symbols, pointer targets, KPIs, and other
project state. Refresh them before closing any pass that touched
symbols, constants, pointers, or counts.

### Refresh wrappers

```sh
# Canonical wrapper — refreshes all inventory snapshots for the project.
make project-inventory PROJECT=<slug>

# Equivalent script form (occasionally used inside other wrappers).
scripts/refresh_inventory.sh <slug>
```

For *when* to refresh the inventory during a pass, see
[PASS_WORKFLOW.md#pass-closeout](PASS_WORKFLOW.md#pass-closeout). The
canonical authored-artifact catalog (`renames.csv`,
`pointer_targets.csv`, `branch_literal_sites.csv`,
`constants_catalog.csv`, `data_extent_assertions.csv`,
`unknowns.md`, etc.) lives at
[AGENTS.md#intermediate-artifacts](../AGENTS.md#intermediate-artifacts);
the generated cache under
`docs/reverse_engineering/inventory/pass/` is documented at
[PASS_WORKFLOW.md#generated-vs-authored-artifacts](PASS_WORKFLOW.md#generated-vs-authored-artifacts).

`pointer_targets.csv` reports source owners for actual `.DW` pointer tables.
Inline return-table payloads are attributed to their dispatching callsite, not
to a synthetic table label, and the terminal three NES CPU vector words are
excluded so they are not misattributed to the preceding data label.

### Raw-address audit

```sh
# Project wrapper (preferred): runs xasm --audit-raw-addresses with the
# project's configured ROM range and writes machine-readable findings.
make project-audit PROJECT=<slug> FORMAT=json
```
### KPI and assertion scripts

Each KPI script reads the asm plus an inventory config and prints a metric
(definition count, doc coverage, etc.) plus a per-line breakdown. Assertion
scripts read reviewed inventory ledgers, such as table-span assertions. They
are read-only; failures should drive an edit and re-run rather than config
tweaks.
```sh
bash scripts/branch_literal_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/comment_quality_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/constant_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/data_label_doc_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/data_extent_assertions_check.sh Game.asm docs/reverse_engineering/inventory/data_extent_assertions.csv
bash scripts/global_code_label_doc_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/inferred_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/procedure_doc_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
bash scripts/raw_address_kpi.sh Game.asm docs/reverse_engineering/inventory/kpis.conf
```

KPI gates are floors, not finish lines — see
[QUALITY_REVIEW.md#kpi-interpretation](QUALITY_REVIEW.md#kpi-interpretation),
which extends the guiding principle at
[AGENTS.md#guiding-pass-philosophy](../AGENTS.md#guiding-pass-philosophy).

<a id="parity-drift"></a>
## Parity-Drift Diagnostics

When a parity check fails, the listing bridges ROM offsets to source lines:

1. Identify the differing ROM offset (e.g., from `cmp -l` or `make project-compare`).
2. Convert to CPU address (NROM-128: `CPU_ADDR = $C000 + ROM_OFFSET`; NROM-256: `CPU_ADDR = $8000 + ROM_OFFSET`; MMC1 fixed bank: use `$C000 + (ROM_OFFSET - fixed_bank_offset)` for offsets in the final 16 KB bank).
3. Look up that address in the listing (with JSON: `jq` filter on `.addr`; with plaintext: text search).
4. Troubleshoot: check hex bytes against reference, look for mis-sized instructions (Absolute vs Zero Page), floating labels from size discrepancies upstream, or raw operands that need symbolization.
<a id="command-reference"></a>
## Command Reference

Compact index of every command documented in this playbook plus a few
debug-only recipes not big enough to warrant their own section.

### xasm

- Assemble + listing (preferred JSON form): [#xasm-options](#xasm-options)
- Wrapper workflow (regenerate-asm, pass-prep/next/start/closeout):
  [#xasm-structured-analysis → Warm-Up and Closeout](#xasm-structured-analysis)
- Feature summary (`--compare`, `--xref`, `--Werror=unused-equ`,
  `--audit-raw-addresses`): [#xasm-structured-analysis → xasm Feature
  Summary](#xasm-structured-analysis)
- Debugging command catalog (one-line forms of the above):
  [#exit-codes → Debugging Commands](#exit-codes)
- Exit-code interpretation: [#exit-codes](#exit-codes)

### Structured pass-prep analysis

- Index patterns, data consumers, data coverage:
  [#data-consumer-analysis](#data-consumer-analysis)

### NESrev regeneration

- CSV hint formats + wrapper invocation:
  [#nesrev-controls](#nesrev-controls)

### Inventory and KPIs

- Refresh wrappers (`make project-inventory`, `scripts/refresh_inventory.sh`):
  [#inventory-commands → Refresh wrappers](#inventory-commands)
- Raw-address audit wrapper: [#inventory-commands → Raw-address audit](#inventory-commands)
- KPI script suite (full list): [#inventory-commands → KPI scripts](#inventory-commands)

### Parity drift

- 4-step diagnosis procedure: [#parity-drift](#parity-drift)

### Anti-placeholder doc check

**Must return no matches** — fails the docs-quality gate otherwise:
```sh
rg -n "Format: packed byte data block \\(structure documented by nearby consumer code\\)\\.|Used by: routines that reference this label in gameplay/render/audio paths\\." Game.asm
```

### Mismatch debugging recipes

Used after `make project-verify` or `make project-compare` reports drift:

```sh
# First differing byte (raw file compare)
cmp -l extracted_prg.bin Game.o | head

# Hex bytes around a mismatch
# -j <ROM_OFFSET> -N <BYTE_COUNT>
od -An -tx1 -j 60 -N 16 Game.o
```

**Run xasm and verify sequentially, not in parallel** — concurrent runs
produce stale/intermediate `Game.o` that triggers false parity failures.
### Search recipes

```sh
# Unresolved generic labels
rg -n "\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:" Game.asm

# Unknown symbols
rg -n "\bUNK_" Game.asm

# Indirect control-flow sites (likely pointer consumers)
rg -n "JMP \\(|JMP \\[|\\[[A-Za-z0-9_]+\\]" Game.asm
```

### Mass symbolization

A full strategy, not a one-liner: it requires a preflight match-count,
asm-only scoping, `.EQU` exclusion, data-table exclusion, and a
post-edit prose sweep. See
[PASS_WORKFLOW.md#batching-and-commit-boundaries → Mass symbolization decision tree](PASS_WORKFLOW.md#batching-and-commit-boundaries)
for the complete decision tree and the mechanics above for the
in-place edit script checklist.

<a id="exit-codes"></a>
## Tool Exit Codes and Debugging

### Exit Codes

- `2`: CLI misuse.
- `3`: file I/O failure.
- `4`: audit findings (`--audit-level=error`).
- `5`: compare mismatch.

### Debugging Commands

```sh
xasm --pure-binary --listing=Game.lst.json --listing-format=json Game.asm
xasm --pure-binary --xref=Game.xref.json --xref-format=json --xref-include-owner=true Game.asm
xasm --pure-binary --audit-raw-addresses '--audit-rom-range=$C000-$FFFF' --audit-output-format=json Game.asm > Game.audit.json
xasm --pure-binary --Werror=unused-equ Game.asm
xasm --pure-binary --compare=reference_prg.bin Game.asm
make project-comment-audit PROJECT=<slug> FORMAT=text
```

Use `$8000-$FFFF` as the raw-address audit range for NROM-256 projects.
Use `$C000-$FFFF` for NROM-128 and MMC1 fixed-bank projects.

<a id="script-hygiene"></a>
## Auxiliary-Script Hygiene

To prevent repository clutter and noise in `git status`, avoid placing
ad-hoc or temporary helper scripts (e.g., Python analysis scripts,
one-off scrapers) directly in project or script directories.
### Temporary script placement

- Place all temporary scripts in the `tmp/projects/<slug>/` directory at
  the project root (creating it if necessary).
- This ensures isolation when multiple agents are working on different
  projects in parallel.
- If a script becomes a permanent part of the project's workflow, move
  it to the official `scripts/` directory or the project-specific
  `scripts/` folder (create `projects/<slug>/scripts/` — and analogously
  `tools/` or `notes/` — on demand; the scaffold no longer pre-creates
  them) and document it in `QUICK_REFERENCE.md`.
### Session-end cleanup

- Before closing a project session, identify any unmanaged scripts in
  `projects/<slug>/` and move or delete them.
- Do not stage or commit temporary scripts to the repository.
### Script quality gate
Deterministic output, explicit error messages, no fragile quoting, works
under `set -euo pipefail`, documented in `QUICK_REFERENCE.md`.

### Mass-replacement mechanics

Cross-referenced from
[PASS_WORKFLOW.md#batching-and-commit-boundaries → Mass symbolization decision tree](PASS_WORKFLOW.md#batching-and-commit-boundaries).
When that decision tree says to drive a sweep with Perl, follow these
mechanics:

- **Use Perl, not sed.** `sed` word boundaries are inconsistent
  across OS. Pattern shape:
  `s/(?<!\w)INST\s+\\\$0{0,3}ADDR\b/INST SYMBOL/gi`.
- **Handle variable leading zeros.** Account for 0-3 leading zeros
  (`$DA`, `$0DA`, `$00DA`).
- **Recursive definition guard.** Exclude `.EQU` lines
  (`unless /\.EQU/`) to prevent `ZP_VAR .EQU ZP_VAR`.
- **Exclude data tables.** Only symbolize executable instructions
  and indirect operands, not `.DB`/`.ASC` content.
- **Replacement impact gate.** Preflight grep to count matches.
  Scope explicitly (asm-only or docs-only). After replacement, scan
  `Format:`/`Used by:`/`Index:` fields for collateral rewrites.
- **Perl string quoting.** Use single-quoted strings for `$`
  literals in Perl hash values. Anti-pattern: `'RAM_Base+\$28'`
  (backslash). Correct: `'RAM_Base+$28'`.
### Multiline doc/ledger edits

Do not write `renames.csv` rows, markdown bullet lists, or scorecard
rows via shell-constructed strings that embed literal `\n`. Use
`apply_patch` or another file-safe editor so each logical row/bullet
is written as an actual line in the target file.
### Dollar-sign text safety

Do not use shell interpolation to inject documentation text
containing `$` literals (for example `$0203`, `$C000`, `$0A`) into
markdown, CSV, or asm comments. Use single-quoted patch content or a
file-safe editor so `$` remains literal and cannot expand to shell
variables or process names.
### Anonymous back-label conversion

Anonymous back-labels (`-`) are optional, not default. Apply only
when all readability checks pass: loop is short and linear (head and
back-branch close together); no intermediate conditional branches
that reduce readability; no cross-scope visibility requirement; scope
audit confirms only backward branches within the same global
procedure reference the label; place `-` on the same line as the
first instruction (`- LDA $00`, not on a standalone line); use Perl
(not sed) for multi-line transformations.

<a id="runtime-trace-tooling"></a>
### Runtime trace tooling

Runtime tracing is a standard evidence lane, not an ad-hoc last resort. Use it
when static analysis cannot prove a behavior because the answer depends on live
input, timing, RNG, scenario state, or emulator-visible external state.

Commit durable trace infrastructure when it is repeatable and project-local:

- capture runners under `scripts/run_trace_*.sh`
- emulator Lua scripts under `tools/trace/`
- analyzers under `scripts/analyze_*_trace.sh` or equivalent
- synthetic fixtures under `tools/trace/fixtures/`
- reduced evidence summaries under `docs/reverse_engineering/`
- command references in `docs/reverse_engineering/QUICK_REFERENCE.md`

Do not commit raw capture logs, savestates, emulator movies, screenshots, GUI
probe scripts, or one-off crash/debug experiments unless the user explicitly
asks for a curated fixture. Put volatile output under a project `tmp/` path and
ignore it.

Trace scripts must install the watches themselves. The operator may drive the
scenario by playing live input or replaying a movie, but they should not have to
open a debugger UI, set manual breakpoints, or copy watch lists by hand.

<a id="trace-helper-roms"></a>
### Trace helper ROMs

Using a small local mod to set up a runtime scenario is an approved trace
strategy. Prefer a helper ROM when the static question is blocked by long setup
time, late-game phase access, RNG, repeated deaths, or awkward player
positioning. The point is to make the evidence capture short and repeatable,
not to change the behavior under test.

Rules for trace helpers:

- Keep the patch minimal and scenario-oriented: phase select, direct phase
  entry, fixed spawn script, player/enemy positioning, or input-release gates
  are appropriate setup changes.
- Treat helper asm as relocatable source, not as a byte-for-byte patch budget.
  It is fine to expand or shrink setup procedures, insert wrapper routines,
  remove or shorten irrelevant setup/data/music/title-stream content, and let
  labels/vectors move, as long as the helper ROM still assembles to the
  project's configured PRG size (for the NROM-128 projects this is 16 KB) and
  the CPU vectors remain the final vector words. Do not waste time scavenging
  exact padding bytes unless the build actually needs it.
- Preserve the code path being measured. Do not patch the routine, RAM field,
  state transition, collision path, or data consumer whose semantics the trace
  is meant to prove.
- If size pressure forces trimming, trim only content outside the evidence
  path (for example title-screen PPU bytes, music data, unused helpers, or
  unrelated late-game data) and document why that content cannot affect the
  measured path. If the trimmed content might affect the behavior under test,
  lower the confidence or pick a different helper strategy.
- Document the setup in the trace plan and reduced evidence summary: helper ROM
  name, changed setup conditions, and why the behavior under test is still the
  stock path.
- Treat `projects/*/mods/` as local experiment space. Do not commit helper
  mods unless the user explicitly asks for that specific mod to become a
  curated fixture or reusable tool.
- If the helper ROM changes more than setup, lower the confidence or use the
  capture only as a harness/debug signal until a stock-path capture corroborates
  it.

Use the templates in `agent_playbook/templates/trace/` when a project needs a
new harness. The default split is:

- **FCEUX frame-poll backend**: stable baseline for transition graphs,
  milestones, and per-frame context. Avoid FCEUX write callbacks unless the
  exact local build has been proven stable; they may enter debugger execution
  paths and crash some builds.
- **Mesen precision backend**: optional writer-PC backend when per-transition
  ownership matters. Prefer script-installed memory callbacks/watchpoints over
  manual debugger breakpoints.

Every analyzer must be validated on a committed synthetic fixture before real
capture evidence is used for naming. Reduced summaries should include the
scenario gate/milestones, verdict, transition table, and interpretation notes
that tie the captured signal back to the specific static uncertainty.

### Headless/GUI constraints

If runtime tracing requires a GUI, do not block progress. Implement a
local-user runnable script that launches the emulator with the trace script
already loaded. Validate the analyzer with synthetic logs and mark the evidence
gap as "capture pending" until a real capture lands.
