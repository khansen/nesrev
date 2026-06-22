#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 1
fi

slug="$1"

if [[ ! "$slug" =~ ^[a-z0-9_\-]+$ ]]; then
  echo "error: project_slug must match [a-z0-9_-]+" >&2
  exit 2
fi

root="projects/${slug}"

if [[ -e "$root" ]]; then
  echo "error: ${root} already exists" >&2
  exit 3
fi

mkdir -p "$root"/{asm,reference,build,docs}
mkdir -p "$root/config/nesrev"
mkdir -p "$root/docs/reverse_engineering/inventory"
mkdir -p "$root/docs/crosswalk"
mkdir -p "$root/docs/game_reference"/{manuals,faqs,metadata}
for d in asm reference docs; do
  touch "$root/$d/.gitkeep"
done
for d in manuals faqs; do
  touch "$root/docs/game_reference/$d/.gitkeep"
done
touch "$root/config/nesrev/.gitkeep"

cat > "$root/README.md" <<DOC
# ${slug}

## Setup

> All \`make\` commands in this project must be run from the
> **repository root** (the directory that contains the top-level
> Makefile). They will fail with "No rule to make target" or
> "no Makefile found" if invoked from inside \`projects/${slug}/\`.

1. Place the ROM at \`reference/${slug}.nes\` (iNES, 16 KB PRG).
2. \`make project-regenerate-asm PROJECT=${slug}\` — produces \`asm/${slug}.asm\` with LXXXX placeholders.
3. Audit hidden-code and indirect-dispatch candidates. Record either
   \`NESREV_RECOVERY_STATUS="none"\` or \`"configured"\` in
   \`project.conf\`; configured recovery files live under
   \`config/nesrev/\`. Formats and override rules live at
   [\`agent_playbook/TOOLING.md#nesrev-controls\`](../../agent_playbook/TOOLING.md#nesrev-controls).
4. Regenerate with the tracked controls, then run
   \`make project-intake PROJECT=${slug}\`. Intake baselines KPIs and emits
   \`docs/reverse_engineering/inventory/{intake_listing,intake_xref,raw_address_audit}.json\`.

## Layout

- \`asm/${slug}.asm\` — disassembly source
- \`reference/${slug}.nes\` — input ROM (gitignored)
- \`config/nesrev/\` — tracked NESrev recovery controls used by regeneration
- \`build/${slug}.o\` — xasm output (gitignored)
- \`docs/reverse_engineering/\` — pass docs, scorecard, KPI configs in \`inventory/\`
- \`docs/crosswalk/TERMINOLOGY_CROSSWALK.md\` — external term ↔ asm symbol map
- \`docs/game_reference/\` — untracked external source material only
- \`docs/crosswalk/MANUAL_TERMS.md\` — tracked terminology extracted from references

## Workflow

See \`docs/reverse_engineering/QUICK_REFERENCE.md\` for the command list.
Pass-completion contract lives at the
[Corridor Execution Contract](../../AGENTS.md#work-order).
DOC

cat > "$root/project.conf" <<DOC
# Per-project configuration for scripts/project_*.sh wrappers.
# Paths are repository-root relative.

PROJECT_NAME="${slug}"
ASM_FILE="projects/${slug}/asm/${slug}.asm"
REF_NES="projects/${slug}/reference/${slug}.nes"
OUT_BIN="projects/${slug}/build/${slug}.o"
DOC_ROOT="projects/${slug}/docs/reverse_engineering"
SYSTEMS_DOC="projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
XASM_AUDIT_ROM_RANGE="\\\$C000-\\\$FFFF"
XASM_COMPARE_CPU_BASE="\\\$C000"

# New clean-room projects opt into strict semantic-claims maturity. The
# SEMANTIC_CLAIMS.md ledger may stay sparse until gold closeout; the checker
# (run by project-maturity-check) validates structure only. Legacy projects
# omit this flag and the check is advisory.
SEMANTIC_CLAIMS_REQUIRED="1"

# Hidden-code/recovery discovery must be resolved before intake:
#   pending    discovery not completed
#   none       discovery completed; no controls required
#   configured one or more tracked control paths below are active
NESREV_RECOVERY_STATUS="pending"
NESREV_CODEPOINTERS_FILE=""
NESREV_CODEENTRIES_FILE=""
NESREV_DATAPOINTERS_FILE=""
NESREV_INLINECALLS_FILE=""
NESREV_DATARANGES_FILE=""
DOC

cat > "$root/docs/reverse_engineering/ONBOARDING.md" <<DOC
# Onboarding

## Project Snapshot

- Target: NES disassembly at \`asm/${slug}.asm\`.
- Status: scaffolded; intake gates have not completed.
- Recovery controls: pending discovery before intake.

## First Steps

> All \`make\` commands below must be run from the repository root
> (the directory that contains the top-level Makefile), not from
> inside this project directory.

1. Place the reference ROM at \`reference/${slug}.nes\`. It must be a
   strict iNES 1.0 file matching the
   [support matrix](../../../../agent_playbook/NEW_PROJECT.md#rom-support-matrix).

2. Generate the assembly. This step also validates the ROM against the
   support matrix and rejects unsupported headers, mappers, sizes, or
   trailing bytes:

\`\`\`sh
make project-regenerate-asm PROJECT=${slug}
\`\`\`

3. Audit hidden-code and indirect-dispatch candidates. Set
   NESREV_RECOVERY_STATUS in \`project.conf\` to \`none\` or
   \`configured\`; keep configured files under \`config/nesrev/\`.

4. Regenerate with the resulting tracked configuration, then run intake:

\`\`\`sh
make project-regenerate-asm PROJECT=${slug}
make project-intake PROJECT=${slug}
\`\`\`

5. Read docs in order:
- \`QUICK_REFERENCE.md\`
- \`${slug}_DX_Systems.md\`
- \`MEMORY_MAP.md\`
- \`docs/crosswalk/TERMINOLOGY_CROSSWALK.md\`
DOC

cat > "$root/docs/reverse_engineering/QUICK_REFERENCE.md" <<DOC
# Quick Reference

## Core Commands

> Run all \`make\` commands below from the **repository root** (the
> directory that contains the top-level Makefile). They will fail
> with "no Makefile found" if invoked from inside this project
> directory.

Each line below is a copy-paste-runnable base invocation. Optional
variables that some targets accept are listed under
[Optional variables](#optional-variables).

- \`make project-regenerate-asm PROJECT=${slug}\`
- \`make project-intake PROJECT=${slug}\`
- \`make project-pass-prep PROJECT=${slug}\`
- \`make project-next-pass PROJECT=${slug}\`
- \`make project-pass-start PROJECT=${slug}\`
- \`make project-pass-closeout PROJECT=${slug}\`
- \`make project-verify PROJECT=${slug}\`
- \`make project-docs-check PROJECT=${slug}\`
- \`make project-process-check PROJECT=${slug}\`
- \`make project-maturity-check PROJECT=${slug}\`
- \`make project-inventory PROJECT=${slug}\`
- \`make project-ci PROJECT=${slug}\`
- \`make project-audit PROJECT=${slug} FORMAT=json\`
- \`make project-comment-audit PROJECT=${slug}\`
- \`make project-compare PROJECT=${slug}\`

## Optional variables

Append these to the relevant target's command line as additional
\`KEY=value\` arguments. Brackets in this list denote optionality —
they are not part of the command syntax.

- \`project-regenerate-asm\`: tracked recovery-control paths normally come
  from \`project.conf\`. \`CODEPOINTERS=<csv>\`, \`DATAPOINTERS=<csv>\`,
  \`CODEENTRIES=<txt>\`, \`INLINECALLS=<csv>\`, and
  \`DATARANGES=<csv>\` are explicit one-run overrides.
  \`ALLOW_TRAILING_BYTES=1\` — proceed past oversized iNES containers
  after a recorded trailing-byte audit (see
  [agent_playbook/NEW_PROJECT.md#trailing-byte-override](../../../../agent_playbook/NEW_PROJECT.md#trailing-byte-override)).
- \`project-pass-start\`: \`PASS=<id>\`, \`TARGET=<corridor_anchor>\` —
  set the pass id and record the selected corridor objective; omitting
  \`TARGET=<corridor_anchor>\` warns and defaults to the first candidate.
- \`project-pass-closeout\`: \`PASS=<id>\` — close out a specific pass
  id rather than the latest.
- \`project-next-pass\`, \`project-audit\`, \`project-compare\`,
  \`project-comment-audit\`: \`FORMAT=text|json\` — change output mode
  (default \`text\`). The Core Commands list above invokes
  \`project-audit\` with \`FORMAT=json\` for inventory pipelines; pass
  \`FORMAT=text\` for human-readable output.

## Pass Artifacts

- \`project-pass-prep\` generates owner-enriched xref JSON in
  \`docs/reverse_engineering/inventory/pass/xref_with_data.json\`
- wrappers and helper scripts should prefer emitted \`owner_routine\` fields over
  re-deriving lexical owners when available

## Assembler Warnings

See \`WARNING_BASELINE.txt\` for the intentionally retained \`defined but not used\` warnings and per-symbol rationale.
DOC

cat > "$root/docs/reverse_engineering/MEMORY_MAP.md" <<'DOC'
# Memory Map

ZP and RAM ownership grouped by subsystem. Add each named symbol under
its owning subsystem; rename, remove, or add subsystems as the project
takes shape.

## Zero Page

### Scratch ($00-$0C)

Multi-purpose scratch; document per-procedure `.EQU` overlays here.

### Frame / NMI

### Gameplay state

### Player state

### Actor state

### Rendering / PPU update queue

### Audio

### Score / HUD

## CPU RAM

### OAM shadow ($0200-$02FF)

### Per-subsystem allocations

Mirror the Zero Page subsystem sections above.
DOC

cat > "$root/docs/reverse_engineering/WARNING_BASELINE.txt" <<'DOC'
# symbol|rationale
# Add one line per intentionally retained assembler warning:
# SymbolName|short rationale
DOC

cat > "$root/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'DOC'
# Progress Scorecard

Track objective throughput and quality metrics for each major pass.

## Metrics

- pass_id: sequential major pass number
- focus: short scope summary
- labels_remaining: count of unresolved opaque labels
- raw_rom_calls_remaining: count of hardcoded `JSR/JMP $XXXX` sites not justified
- raw_ptr_immediates_remaining: count of unresolved pointer-byte immediate loads
- raw_indirect_operands_remaining: count of unresolved `[$NN]` style operands
- hardcoded_counter_sites_remaining: count of unresolved semantic loop/count literals
- warnings_baseline_delta: added/removed intentional warnings
- verify: pass/fail
- docs_check: pass/fail
- rework_items: number of fixes caused by missed required sweeps
- notes: key outcomes / blockers; pass 1 must include
  \`Analogue: <project_slug|none> (<applied pattern or reason it did not fit>)\`

## Pass Log

| pass_id | focus | labels_remaining | raw_rom_calls_remaining | raw_ptr_immediates_remaining | raw_indirect_operands_remaining | hardcoded_counter_sites_remaining | warnings_baseline_delta | verify | docs_check | rework_items | notes |
|---|---|---:|---:|---:|---:|---:|---|---|---|---:|---|
| 0 | Intake baseline | | | | | | 0 | | | | |

Closeout auto-syncs the supported KPI cells (`labels_remaining`, `raw_rom_calls_remaining`,
`raw_indirect_operands_remaining`, `hardcoded_counter_sites_remaining`); do not hand-edit
those derived counts.
DOC

cat > "$root/docs/crosswalk/TERMINOLOGY_CROSSWALK.md" <<'DOC'
# Terminology Crosswalk

Map external/reference terminology to internal assembly symbols without
claiming implementation knowledge before code evidence exists.

## Source Inputs

- manuals / guides / FAQs in `docs/game_reference/`
- in-ROM UI/script text
- current disassembly evidence

## Naming Policy

- prefer gameplay/domain names over raw-address names
- keep neutral names when semantics are not yet proven
- consolidate aliases for one game concept into one row
- leave asm mappings blank until code evidence identifies an implementation
- apply mapping confidence to the term-to-code mapping, not to the source's
  vocabulary

## Crosswalk

| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|

Use `reference-only` when the term is established by source material but has
not been mapped to code. Use `unmapped` when even the source terminology or
concept boundary remains unresolved. Do not use `high`, `medium`, or
`inferred` until assembly evidence supports a term-to-code mapping.

## Open Terminology Gaps

- fill this section during intake if reference terminology is missing or unclear
DOC

cat > "$root/docs/crosswalk/MANUAL_TERMS.md" <<'DOC'
# Manual Terms

Track project-authored terminology extracted from external manuals and guides.
The source files themselves stay untracked under `docs/game_reference/`.

| term / aliases | source | notes |
|---|---|---|
DOC

cat > "$root/docs/reverse_engineering/inventory/kpis.conf" <<'DOC'
# KPI thresholds for `make project-verify`.
# Each variable is read by its dedicated runner under scripts/.
# Tighten values toward their target as cleanup progresses.

# Raw addresses: $XX low-address operands and $Cxxx-$Fxxx ROM operands.
MAX_ACTIVE_RAW_LOWADDR=999999
MAX_ACTIVE_RAW_ABSROM=0

# Bare numeric immediates in code, excluding #0/#$00.
MAX_ACTIVE_MAGIC_IMMEDIATES=999999

# $+N / $-N relative-branch literals (parity-sensitive).
MAX_ACTIVE_BRANCH_LITERALS=999999

# `; inferred` confidence tags.
MAX_INFERRED_ANNOTATIONS=999999

# Placeholder/filler comment phrases. Target stays at 0.
MAX_PLACEHOLDER_COMMENTS=0

# Callable/global counts are review inventories, not comment-coverage goals.
# Replace the intake ceilings with the reviewed baseline; do not add filler
# headers merely to reduce these counts. Data labels remain a strict format-
# documentation gate.
MAX_UNDOCUMENTED_PROCEDURES=999999
MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS=999999
MAX_UNDOCUMENTED_DATA_LABELS=999999
DOC

cat > "$root/docs/reverse_engineering/inventory/constant_magic_allowlist.csv" <<'DOC'
label,mnemonic,immediate,reason
DOC

cat > "$root/docs/reverse_engineering/inventory/renames.csv" <<'DOC'
old_name,new_name,reason,confidence,pass_id
DOC

cat > "$root/docs/reverse_engineering/SEMANTIC_CLAIMS.md" <<'DOC'
# Semantic Claims

Maturity-time ledger of major evidence-backed semantic conclusions for this
project. It exists so independent clean-room runs can be compared by meaning,
not just by symbol spelling or KPI counts.

This is not a per-pass chore and not a replacement for MEMORY_MAP.md,
data-format docs, raw_ram_review.csv, renames.csv, or the systems overview. An
empty ledger is expected early on and passes the pass-time check, but gold
closeout requires at least one recorded claim.

Add a claim only for major, evidence-backed conclusions: RAM/ZP ownership
families, scoped overlays, state machines and values, data formats, pointer
tables, routine contracts, subsystems, or contested/inferred semantics. Model,
scope, and the structural checker are documented in
[../../../../agent_playbook/QUALITY_REVIEW.md#semantic-claims](../../../../agent_playbook/QUALITY_REVIEW.md#semantic-claims).

Copy the template below (drop the code fence) and fill it in:

```md
## Claim: semantic-slug

Subject: AsmSymbol or External/reference-only
Kind: RAM/ZP field | scoped overlay | state machine | state value | data format | pointer table | routine contract | subsystem | other
Subsystem: subsystem name
Claim: one-paragraph evidence-backed conclusion
Confidence: high | medium | inferred | mechanical
Evidence:
- Writers/Producers: ...
- Readers/Consumers: ...
- Cross-check: ...
Caveats:
- ...
Canonical docs:
- MEMORY_MAP.md
```

No claims recorded yet.
DOC

cat > "$root/docs/reverse_engineering/${slug}_DX_Systems.md" <<DOC
# ${slug} Systems

Status: intentionally not promoted during intake.

Keep this file minimal until subsystem names, ownership, control flow, and
major formats are stable. Early findings and future-pass hypotheses belong in
\`PROGRESS_SCORECARD.md\`, inventories, \`MEMORY_MAP.md\`, dedicated proven
format docs, or working notes. Promotion criteria:
[DOCUMENTATION.md#dx-systems-scope](../../../../agent_playbook/DOCUMENTATION.md#dx-systems-scope).
DOC

echo "created ${root}"
