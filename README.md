# NESrev

## Start a project with two agents

One command sets up an implementer, an independent reviewer, and their automatic
handoffs. Use it for a new game or to continue an existing project's pass cycle.
The default goal is **reviewed gold standard**, as defined by the
[quality checklist](agent_playbook/QUALITY_REVIEW.md#gold-standard-assessment).
The agents can stop for files, permissions, account limits, or gameplay traces
that need your help. This is not a guarantee of unattended completion.

<a id="before-your-first-run"></a>
### Before your first run

You need this repository and its [toolchain](agent_playbook/NEW_PROJECT.md#prerequisites), Python 3, tmux,
and your chosen agent apps installed and signed in. The default implementer is
Codex. The default reviewer is Claude if installed, otherwise a separate Codex
session. You can choose either app for either role; examples are below.
Their normal usage charges and limits
apply. Git must have your name and email configured so the implementer can
save commits. Bring your own reference ROM and game manual; FAQs and guides
are optional. The agents do not obtain those for you. You can explicitly
choose to proceed without a manual at startup, accepting lower semantic precision.

Open Terminal in the repository folder. Replace `my_game` in the examples
with your project’s folder name. This optional check starts no agents and
creates no project:

```sh
python3 scripts/agent_review_tmux.py --project my_game --check
```

If a required tool is missing, install it using the diagnostic or toolchain
instructions, then repeat the check. It checks local tools and Git identity;
you still complete account and permission prompts when the agents start.
Doctor also reports PDF/OCR tools. Use `make project-doctor PROJECT=my_game`
to check requirements for that project's supplied manuals and FAQs.
PDFs require Poppler (`pdftotext`, `pdftoppm`) and Tesseract so both text and
scanned pages can be read; image scans require Tesseract with recognition
language data. Plain text and HTML do not require these tools. The launcher
checks again after you confirm your files and waits with installation guidance
if anything is missing. It does not install software automatically.

Doctor also reports **FCEUX**, an optional emulator for runtime analysis. If
installed, the implementer can use Lua to simulate controller inputs, replay
movies, capture frames, and trace game state. Missing FCEUX does not block
startup or static analysis; the agent asks for installation or access if it
later needs it. Doctor does not launch the emulator; capture support is checked
when used.

### Start and let the agents work

1. Run this command with your project's folder name in place of `my_game`.
   Use lowercase letters, numbers, and underscores.

   ```sh
   python3 scripts/agent_review_tmux.py --project my_game
   ```

2. The launcher shows the local permissions it proposes. Type **yes** to
   allow routine commits and review handoffs for this checkout. It remembers
   that choice; no global settings or unrestricted bypass are enabled.
   Finish each agent's workspace-trust prompt when it starts.
   The launcher creates the project folders if needed. For a new
   project, copy your ROM to `projects/my_game/reference/my_game.nes` in this
   checkout. The file must be an iNES `.nes` image, not a bare program dump.
   Copy the manual (PDF, scans, or text) into
   `projects/my_game/docs/game_reference/manuals/`. Put any optional FAQs or
   guides into `projects/my_game/docs/game_reference/faqs/`. These source files
   stay outside Git. The implementer derives mapper and ROM sizes itself.
3. Press **Ctrl+b**, release both keys, then press **w**. Select `agents`.
   The left pane is the implementer; the right pane is the reviewer. Switch
   panes with **Ctrl+b**, then an **arrow key**. Finish any login/trust prompts
   in each pane and wait until both say **READY** and finish their turns.
4. Use **Ctrl+b**, then **w** to select `watchers`. Press **Enter** in the
   startup pane when your reference set is ready. The launcher lists the
   manual and optional FAQ folders. If no manual is available, it warns that
   the final disassembly's terminology and semantic precision will likely be
   lower, and waits. To proceed anyway, type **continue without a manual**.
   Pressing Enter alone does not skip a missing manual; an empty file or
   `.gitkeep` does not count. Your explicit choice is remembered on restart.
   Existing projects use the same check. The launcher switches back to the agents. They now
   perform intake if needed, then implement, review, fix, and archive passes
   automatically. The watchers deliver each handoff; you do not copy prompts
   between agents.

The implementer must read the supplied references and prepare the terminology
crosswalk before semantic analysis. Missing or unreadable manuals require your
input unless you explicitly chose to continue without one; the crosswalk must
record that decision and limitation. A “no references available” note alone
does not waive this step. A launcher
presence check cannot establish that a file is the correct, readable manual;
the agents check that, choose the document's OCR language, and check extracted
text against the pages during reference preparation and intake review.

Routine Git commits and review handoffs use a **pass-cycle permission profile**.
`--check` previews its exact rules without installing them; the normal launch
asks once before installation. The agents receive matching command examples,
and staging accepts explicit files in the selected project. The commit command
refuses unrelated staged changes. Review drafts are written into the project's
`tmp` folder before the handoff tool publishes them. Other commands can still
need approval, including builds under Claude, installations, network access,
and unusual Git operations.
Existing user permissions remain in effect; Codex's project rules are shared
by both Codex sessions. This does not isolate the agents from each other.
See [permission scope and recovery](agent_playbook/AGENT_PERMISSIONS.md).

For custom agent wrappers or to use your existing permission setup, add
`--permissions inherit`. This skips installation and does not remove rules
you previously installed. A running tmux workspace keeps its original settings;
new permissions take effect when you restart it through the documented recovery
procedure.

To leave the screen while work continues, press **Ctrl+b**, then **d**.
Keep the computer awake and online. Run the same launch command to reconnect;
it keeps the running agents and their current task. Detaching does not stop
agent work or usage. Avoid **Ctrl+c** or closing individual panes unless you
intend to interrupt an agent.

### Know when your help is needed

The implementer attempts runtime analysis itself before asking you to play or
trace. It may download TASVideos `.fm2` input movies to replay against your ROM,
checking that the replay reaches the intended scenario. ROMs, manuals, and FAQs
still come from you.
The supplied [FCEUX runner](agent_playbook/templates/trace/README.md#supervised-captures)
limits capture time, cleans up its emulator after failures, and checks that the
requested scenario completed before reporting success.

Questions that need human judgment, such as identifying an ambiguous sound,
are collected into a batch with short clips or screenshots and clear choices.
You might see `NEEDS INPUT: 3 questions` with a packet to open and reply to as
`Q1: A; Q2: B; Q3: unsure`. The implementer prepares the samples and continues
independent work before stopping for answers. A blocking permission or missing
file is requested immediately. You should not need to set debugger watches
or play a whole game just to answer a question.

- **NEEDS INPUT** means the implementer has stopped and gives you a specific
  next action. Supply the file or answer, then tell it to continue in the
  implementer pane. Permission prompts may appear directly in either agent.
- **GOLD STANDARD APPROVED** means the reviewer assessed the whole project
  against the quality checklist, strict CI passed, and the implementer saved
  the final review archive. An individual pass approval or green KPI report
  is not this completion signal. The final message includes the archive path.
- If an agent exits or hits a usage limit, the launcher does not restart it
  automatically. Inspect its pane. To rebuild the workspace after resolving
  the problem, end both agents' turns first, then run
  `tmux kill-session -t nesrev-review` in another terminal and repeat the launch
  command. Saved commits and review state remain; unsaved chat context does not.
- If the reviewer watcher reports **startup watcher exited before confirmation
  completed**, startup failed before both watchers were armed. Inspect the
  startup pane in `watchers`, resolve its error, and use the restart procedure
  above. Waiting longer or simply reconnecting will not restart a dead watcher.

The agents are instructed never to push `projects`. Model and effort defaults
come from each agent; you can override them separately below. Permissions
come from your existing agent configuration. Advanced command overrides and
the handoff protocol are in
[TOOLING.md](agent_playbook/TOOLING.md#agent-review-handoff).

### Choose your agents

To have Claude implement and Codex review:

```sh
python3 scripts/agent_review_tmux.py --project my_game --implementer-cmd claude --reviewer-cmd codex
```

To use Codex for both roles, even when Claude is installed:

```sh
python3 scripts/agent_review_tmux.py --project my_game --reviewer-cmd codex
```

To use Claude for both roles:

```sh
python3 scripts/agent_review_tmux.py --project my_game --implementer-cmd claude --reviewer-cmd claude
```

Each role always gets its own session. Add `--check` to any command to check
that selection without launching it. Choices apply when creating a workspace;
reconnecting keeps the agents already running. An explicitly chosen app that
is missing produces an error, rather than silently choosing another app.

<a id="choose-models-and-effort"></a>
### Choose models and reasoning levels

**No options are needed to use each agent's default model and effort.** The
launcher leaves those choices to Codex or Claude, including their saved settings.
It does not pin a model, force a reasoning level, or edit either app's configuration.

Choose independently for each role:

| Option | Choice |
| --- | --- |
| `--implementer-model` | Implementer's model name or alias |
| `--implementer-effort` | Implementer's inference/reasoning level |
| `--reviewer-model` | Reviewer's model name or alias |
| `--reviewer-effort` | Reviewer's inference/reasoning level |

For example, leave model selection to the agents and choose different effort levels:

```sh
python3 scripts/agent_review_tmux.py --project my_game \
  --implementer-effort high --reviewer-effort medium
```

To choose models too, replace the quoted placeholders with names supported by
your agents. Select each app explicitly when using its model names so the
automatic reviewer fallback cannot switch apps:

```sh
python3 scripts/agent_review_tmux.py --project my_game \
  --implementer-cmd codex --implementer-model "<codex-model>" --implementer-effort high \
  --reviewer-cmd claude --reviewer-model "<claude-model>" --reviewer-effort medium
```

The same options work with Claude implementing, Codex reviewing, or the same
app in both roles. Any omitted choice stays with that agent. Supported models
and effort levels depend on the agent version, model, and account; the launcher
passes your choices through without substituting another model or level.
Codex effort uses its [model_reasoning_effort setting](https://developers.openai.com/codex/config-reference);
Claude effort uses `--effort`.
Add `--check` to see the resulting commands without starting agents. Availability
is checked by the agents at startup. `--implementer-reasoning-effort` and
`--reviewer-reasoning-effort` are longer aliases for the effort options.

These options apply to new workspaces. Reconnecting keeps the running agents'
models and effort; use the recovery procedure above when you want to recreate
the workspace with different settings. With advanced `--*-cmd` arguments, set
each choice in only one place. Custom wrappers should receive their native
model/effort arguments inside `--*-cmd`.

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

> Work on `<slug>` toward reviewed gold standard, including runtime captures
> you can run yourself. Batch questions that need my help with prepared samples
> and replay commands. State each gap you defer as `DEFERRALS="subject ::
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

How manual and FAQ terminology enters pass planning, review, and gold approval
is described in the [reference-coverage cycle spec](REFERENCE_COVERAGE_CYCLE_SPEC.md).

Adding process detail to the prompt is usually the wrong fix. The prompt sets
the goal and the exit condition; a rule that belongs to every run belongs in the
playbooks, where it applies whether or not whoever starts the run remembers it.

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
