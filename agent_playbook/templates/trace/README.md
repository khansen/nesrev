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

FCEUX is the baseline backend for agent-run frame-poll traces. It is good for
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

1. Copy the relevant runner and Lua template into the project. The FCEUX shell
   wrapper calls the shared [supervisor](../../../scripts/run_fceux_trace.py).
2. Replace the watch list with symbol-backed addresses from the asm.
3. Add scenario milestones that prove the capture reached the intended game
   state before the analyzer accepts evidence. Replace the wrapper's two
   `--require-milestone` names together with the Lua predicates. The unmodified
   template intentionally fails these checks.
4. Add helper-ROM setup only when it shortens or stabilizes capture without
   changing the behavior under test.
5. Add a domain-specific analyzer and validate it on `synthetic_trace.log`.
6. Commit the harness before using real captures for semantic names.
7. Keep analyzer-generated one-capture summaries under `tmp/traces/`; merge
   accepted evidence manually into the curated transitions doc before commit.
   If the curated doc uses a domain-specific name, set
   `CANONICAL_TRACE_DOC=docs/reverse_engineering/<DOMAIN>_TRANSITIONS.md` so
   the analyzer refuses accidental direct overwrites.

<a id="screen-captures"></a>
## Screen captures

[`fceux_screen_capture.lua`](fceux_screen_capture.lua) supports
[visual identity evidence](../../PASS_WORKFLOW.md#visual-identity-evidence).
Copy it into `projects/<slug>/tools/trace/` with a small wrapper that assembles
a fresh listing, refuses one that differs from the ROM, prepends a `watch` table
of symbol-backed addresses and runs the supervisor below with one
`--require-milestone` per capture. Each `capture(name)` writes `<name>.gd` into
`TRACE_DIR` and one milestone record holding the four nametable views
(`nt0`-`nt3`), the 32-byte palette, optional `CONTEXT` bytes and, for CHR-RAM
games, the pattern tables. `HOLD` rewrites bytes every frame to reach later
screens; record each entry in the trace plan. The unmodified template stops
with `stalled`. Convert and render the output with the
[shared graphics helpers](../../TOOLING.md#visual-evidence-tools).

<a id="supervised-captures"></a>
## Supervised captures

The copied wrapper accepts an optional output **parent directory**, not a log
filename. Each invocation creates a fresh `capture-*` child containing
`trace.log`, `emulator.log`, and `result.json`. It prints the absolute capture
path even on failure. Earlier captures remain untouched.

The supervisor resolves ROM, Lua, movie, emulator, and output paths before
launch. Lua receives absolute `TRACE_OUT` (the log) and `TRACE_DIR` (screenshots
and other capture artifacts), plus `TRACE_MAX_FRAMES`. Use these variables
because FCEUX may change its working directory. The runner starts muted with
configuration and Game Genie disabled; use its `--sound 1` option when needed.
Enabling sound does not record audio; listening batches still need audio capture.

`TRACE_TIMEOUT=180` sets the wrapper's wall-clock limit, independently of the
Lua frame limit. On timeout, Ctrl+C, or termination, the supervisor sends TERM
then KILL after a short grace period to its own emulator process group and
reaps the child. It also cleans helpers left behind after a normal exit. It
does not search for or stop other emulator sessions. This requires macOS or
Linux; detached processes that leave the group are outside that cleanup scope.
Normal execution/GUI approvals still apply. An uncatchable SIGKILL of the
supervisor itself cannot run cleanup.

Success requires all configured checks on the fresh log. A nonzero emulator
exit is a failure. When Lua has completed but the GUI remains open, the runner
allows a brief normal exit, then stops its process group and records
`stopped_after_completion` in `result.json`. That deliberate stop can have a
nonzero child status; it is not an emulator failure. The log is checked again
after cleanup before success is reported.

- JSONL mode (`--require-milestone NAME`, repeatable): a `start` record, every
  named milestone, and a final `done` record with reason `max_frames` or
  `scenario_complete`. A manual `exit`, malformed log, or missing milestone fails.
- Custom log mode (`--completion-line COMPLETE`): the final nonblank line must
  match exactly. The Lua script must assert every scenario gate before writing
  that newline-terminated line and flushing/closing the log; merely exhausting
  the frame budget is insufficient.

For a custom Lua driver:

```sh
python3 scripts/run_fceux_trace.py \
  --rom projects/my_game/reference/my_game.nes \
  --lua projects/my_game/tools/trace/scene.lua \
  --output-dir projects/my_game/tmp/traces \
  --timeout 120 --completion-line COMPLETE
```

`result.json` records the command, input hashes, limits, required checks, child
exit status, and failure reason. Exit codes are 0 for accepted capture, 1 for
emulator/validation/cleanup failure, 2 for invalid setup, 124 for timeout, and
128 plus the signal number for interruption. Only accepted captures print
`Capture complete`. The domain analyzer still owns semantic interpretation and
confidence promotion; the supervisor checks only the declared capture contract.

Existing project runners keep their behavior until explicitly migrated. Adopt
the supervisor by switching Lua output to `TRACE_OUT`/`TRACE_DIR` and declaring
the existing scenario checks in the project wrapper; do not replace an analyzer
with an unconditional completion marker.
