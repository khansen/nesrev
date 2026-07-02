# Runtime Trace Template

Use this template when static analysis reaches a real runtime-gated question:
state transitions that depend on player input, RNG, frame timing, scenario
state, or external device state.

## What To Commit

Commit repeatable project infrastructure:

- `scripts/run_trace_<backend>.sh`
- `tools/trace/<backend>_<domain>_trace.lua`
- `scripts/analyze_<domain>_trace.sh`
- `tools/trace/fixtures/*.log`
- `docs/reverse_engineering/<DOMAIN>_TRACE_PLAN.md`
- `docs/reverse_engineering/<DOMAIN>_TRANSITIONS.md`
- `QUICK_REFERENCE.md` command entries

Keep volatile artifacts untracked:

- raw logs under `projects/<slug>/tmp/traces/`
- trace helper mods under `projects/<slug>/mods/` unless explicitly curated
- emulator savestates
- emulator movies unless curated as a fixture
- screenshots and manual probe output
- crash/debug scripts used to test emulator APIs

## Backend Policy

FCEUX is the baseline backend for operator-run frame-poll traces. It is good for
transition graphs, milestones, and context snapshots. Do not rely on FCEUX write
callbacks unless the exact local build has been proven stable.

Mesen is the precision backend when writer-PC evidence matters. Prefer Lua
callbacks/watchpoints installed by the script; do not require the operator to
set debugger breakpoints manually.

## Scenario Helper ROMs

Use a local helper mod when reaching the scenario by normal play is slower or
less repeatable than the trace question justifies. Good helpers enter a phase
directly, choose a spawn script, fix starting positions, or hold/release input
so the operator can trigger one event. They must leave the routine, state byte,
field, collision path, or data consumer under test on the stock path.

Record the helper ROM and setup changes in the trace plan and reduced evidence
summary. Do not commit helper mods unless the user explicitly asks for that
specific mod to be curated.

## Adoption Steps

1. Copy the relevant runner and Lua template into the project.
2. Replace the watch list with symbol-backed addresses from the asm.
3. Add scenario milestones that prove the capture reached the intended game
   state before the analyzer accepts evidence.
4. Add helper-ROM setup only when it shortens or stabilizes capture without
   changing the behavior under test.
5. Add a domain-specific analyzer and validate it on `synthetic_trace.log`.
6. Commit the harness before using real captures for semantic names.
7. Keep analyzer-generated one-capture summaries under `tmp/traces/`; merge
   accepted evidence manually into the curated transitions doc before commit.
   If the curated doc uses a domain-specific name, set
   `CANONICAL_TRACE_DOC=docs/reverse_engineering/<DOMAIN>_TRANSITIONS.md` so
   the analyzer refuses accidental direct overwrites.
