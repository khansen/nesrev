# NESrev

## Multi-Project Workspace

Use `projects/` for per-ROM isolation. Each project should live under its own
directory (`projects/<slug>/`) with its own `asm/`, `reference/`, `docs/`,
and `build/` directories. Project-local `scripts/`, `tools/`, `notes/`, and
`mods/` directories are optional and should be created only when they carry
project-specific content.

Create a new isolated project scaffold with:

```sh
make project-init PROJECT=<project_slug>
```

See `projects/README.md` for the standard layout, and
`agent_playbook/NEW_PROJECT.md` for the end-to-end intake flow.

Reference ROM/binary files are not tracked. Each user must provide their own
reference file under `projects/<slug>/reference/`.
NESrev recovery controls are authored build inputs: keep them under
`projects/<slug>/config/nesrev/` and reference them from `project.conf`.

Per-project verification/docs checks:

```sh
make project-verify PROJECT=<project_slug>
make project-docs-check PROJECT=<project_slug>
make project-ci PROJECT=<project_slug>
```

Per-project pass workflow (run from the repository root):

```sh
make project-pass-prep PROJECT=<project_slug>
make project-next-pass PROJECT=<project_slug>
make project-pass-start PROJECT=<project_slug>
make project-pass-closeout PROJECT=<project_slug>
```

Record the operator-selected corridor objective when starting a pass
(omitted fields warn but do not fail):

```sh
make project-pass-start PROJECT=<project_slug> TARGET=<corridor_anchor> \
  CORRIDOR="..." WHY_NOW="..." BOUNDARIES="..." EVIDENCE="..." OUT_OF_SCOPE="..."
```

These fields are persisted into
`docs/reverse_engineering/inventory/pass/current_pass_plan.json` and
`current_pass_plan.md` so the review objective does not live only in chat.

Optional variables:

- `project-pass-start`: append `PASS=<id>` to set the pass id and
  `TARGET=<corridor_anchor>` to record the selected corridor objective
  (without `TARGET` the wrapper warns and defaults to the first candidate).
  Append `CORRIDOR=`, `WHY_NOW=`, `BOUNDARIES=`, `EVIDENCE=`,
  `OUT_OF_SCOPE=` to persist the full objective.
- `project-pass-closeout`: append `PASS=<id>` to close out a specific
  pass id rather than the latest.

Use this as the default start/resume workflow for reverse-engineering passes.
`project-pass-prep` refreshes inventory and generates structured `xasm`
analysis artifacts, including owner-enriched xref JSON.
`project-next-pass` reads those artifacts and emits compact candidate
evidence for the next pass — advisory, not an authoritative recommender; the
operator selects the corridor objective — including caller context, outbound edge summary,
data-anchor hints, RAM-provenance hints, and a compact source excerpt for the
top targets. When generic labels are exhausted but strict raw low-address
operands remain, it can switch into `raw_ram_symbolization` mode and rank
unnamed RAM bytes/windows for the next semantic symbolization pass. It also
persists the computed briefing to
`docs/reverse_engineering/inventory/pass/next_pass.json`.
In `raw_ram_symbolization` mode, it also maintains a persistent review queue at
`docs/reverse_engineering/inventory/raw_ram_review.csv` so already reviewed or
deferred bytes are not re-triaged from scratch every pass.
As soon as a raw RAM byte/window is inspected and judged, flush that judgment
immediately with:

```sh
make project-raw-ram-review PROJECT=<slug> ADDR=<addr> STATUS=<candidate|unreviewed|deferred|revisit|not_semantic_yet|symbolized>
```

Optional variables: `SYMBOL=<name>`, `NOTES=<text>`, `PASS=<id>`. Append
them as additional `KEY=value` arguments on the same command line.
`project-pass-start` snapshots that brief into
`docs/reverse_engineering/inventory/pass/current_pass_plan.json` and
`current_pass_plan.md` so long passes can resume cleanly after context
compaction.
`project-pass-closeout`
scans authored docs for stale old-symbol residue before the final docs gate.

For a one-screen, read-only strategy view, run:

```sh
make project-maturity-summary PROJECT=<project_slug>
```

It reports hard maturity blockers (raw low-address / absolute-ROM operands,
noncompliant data labels), soft review inventory (raw-indirect / magic-immediate
counts, inferred annotations, placeholder comments, and callable/global-label
review inventories), recent pass yield, and the current generated candidate
evidence — top actionable corridors plus deferred/mixed clusters kept as
context. It is advisory candidate evidence, not a gate, and never fails.

At subsystem maturity and gold closeout, projects keep a semantic-claims ledger
(`docs/reverse_engineering/SEMANTIC_CLAIMS.md`) recording final evidence-backed
conclusions so independent clean-room runs can be compared by meaning. Validate
its structure (not its truth) with:

```sh
make project-semantic-claims-check PROJECT=<project_slug>
```

`project-maturity-check` also runs it — strict for projects that opt in via
`SEMANTIC_CLAIMS_REQUIRED="1"` (set by new scaffolds), advisory for legacy
projects. New projects scaffold the file; it may stay sparse until gold closeout.

Mod workflow commands:

```sh
make mod-new PROJECT=<project_slug> MOD=<mod_slug>
make mod-build PROJECT=<project_slug> MOD=<mod_slug>
make mod-patch PROJECT=<project_slug> MOD=<mod_slug>
```

Optional variable: `FORMAT=ips|bps` on `mod-patch` (default `ips`).

## Build

   make

(Compiles `NESrev.java` — the home-rolled disassembler invoked by
`make project-regenerate-asm PROJECT=<slug>`. You normally don't call
`NESrev` directly; use the project-aware target instead.)

## NESrev Recovery Controls

The disassembler accepts five optional control inputs for ROMs whose
structure it cannot recover from static analysis alone:
`codepointers.csv`, `datapointers.csv`, `codeentries.txt`,
`inlinecalls.csv`, and `dataranges.csv`. Keep accepted controls under
`projects/<slug>/config/nesrev/` and set their `NESREV_*_FILE` paths in
`project.conf`; then the base `make project-regenerate-asm
PROJECT=<slug>` command is reproducible. Command-line `KEY=value`
paths are one-run overrides only. Do not invoke `NESrev` directly.

Canonical format specifications and worked examples for all five hint
files live at
[`agent_playbook/TOOLING.md#nesrev-controls`](agent_playbook/TOOLING.md#nesrev-controls).

## Verify Binary Identity

After refactor/comment/naming passes, verify output matches the PRG ROM inside the reference iNES file:

   make project-verify PROJECT=<slug>

Full pre-commit gate (verify + process/maturity/docs checks):

   make project-ci PROJECT=<slug>
