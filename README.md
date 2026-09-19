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

Run this before asking the user to place the ROM. The scaffold creates
`projects/<project_slug>/reference/`; if the ROM is not present yet,
stop after scaffolding and ask the user to put it at
`projects/<project_slug>/reference/<project_slug>.nes`. See
`agent_playbook/NEW_PROJECT.md` for the end-to-end intake flow.

### Kicking off an operator

The process carries the working rules, so the prompt does not need to restate
them. A suggested starting prompt, in full:

> Work on `<slug>` until you need runtime traces that only I can run. End with a
> trace plan I can execute. State each gap you defer as `DEFERRALS="subject ::
> what would close it"` at closeout, adding `:: runtime` for the ones only a
> trace can settle. Commit each pass and record friction in
> `PROCESS_FRICTION.md`; otherwise don't stop for feedback.

The third field is how a gap becomes runtime-gated: `subject :: what would
close it :: runtime` obliges a trace plan, and is the only way a deferral gets
that status — the tool never infers it from wording.

Everything else is the operator's to read: the outcome standard in
[AGENTS.md#mission](AGENTS.md#mission), and the rules that replace a reviewer
during a long unattended run — blocking proof-debt signals, three strikes on a
repeated deferral, triangulating before declaring a gap runtime-gated, and what
the closing trace plan must contain — in
[PASS_WORKFLOW.md#proof-debt](agent_playbook/PASS_WORKFLOW.md#proof-debt).

Adding process detail to the prompt is usually the wrong fix. The prompt sets
the goal and the exit condition; a rule that belongs to every run belongs in the
playbooks, where it applies whether or not whoever starts the run remembers it.

### Optional tmux review handoff

External/adversarial pass review is opt-in. Start the standard two-agent
workspace from the project checkout with:

```sh
python3 scripts/agent_review_tmux.py --project <slug>
```

The launcher creates a `nesrev-review` session with Codex as implementer,
Claude as reviewer, and a separate window containing both watchers. It supplies
the role prompts and wires the pane IDs automatically. Inside tmux it switches
clients; outside tmux it attaches. Existing sessions are preserved.

Finish any login/trust prompts and wait until both agents say `READY`. Use
**Ctrl+b, w** to return to the `watchers` window and press Enter once to begin
passes and automatic review handoffs. The default objective is to continue
semantic passes until progress needs user-run runtime traces. Use `--task`
to supply a different objective. The launcher preserves configured models and
permissions, and instructs the agents never to push `projects`.

Agent-command overrides, startup/resume behavior, post-commit handoff, and
review archiving live in
[TOOLING.md#agent-review-handoff](agent_playbook/TOOLING.md#agent-review-handoff).

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
make project-prior-reuse-check PROJECT=<project_slug>
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
- `project-prior-reuse-check`: append `STRICT=1` only after reviewing and
  clearing the advisory analogue-constant shortlist.

Use this as the default start/resume workflow for reverse-engineering passes.
`project-pass-prep` refreshes inventory and generates structured `xasm`
analysis artifacts, including owner-enriched xref JSON. Compatible xasm
outputs, including the baseline parity compare, are bundled into one assembler
pass; the filtered generic-label xref summary is generated separately because
its context is computed after applying the filter.
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

`project-docs-check` runs its strict pass-time structural validation for every
project, while `project-maturity-check` additionally requires at least one
claim. New projects scaffold the file; it may stay sparse until gold closeout.

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
Use `make project-regenerate-check PROJECT=<slug>` to regenerate into a
temporary file and review drift without replacing the authored assembly;
add `STRICT=1` only when exact generator identity is the intended invariant.

Canonical format specifications and worked examples for all five hint
files live at
[`agent_playbook/TOOLING.md#nesrev-controls`](agent_playbook/TOOLING.md#nesrev-controls).

## Verify Binary Identity

After refactor/comment/naming passes, verify output matches the PRG ROM inside the reference iNES file:

   make project-verify PROJECT=<slug>

Full pre-commit gate (verify + process/maturity/docs checks):

   make project-ci PROJECT=<slug>
