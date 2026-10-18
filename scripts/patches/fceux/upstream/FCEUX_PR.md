> Unsubmitted draft, last validated 2026-10-18. Recheck current upstream state,
> reproduce relevant results, and follow [the handoff checklist](README.md) before posting.

Title: Honor --no-config when saving fceux.cfg

Opening a ROM and loading a Lua script still rewrite `fceux.cfg` with
`--no-config 1`, including `SDL.LastOpenFile` and `SDL.LuaScript`. Some callers
check the option, but others call `Config::save()` unconditionally.

Reset `SDL.NoConfig` after loading `fceux.cfg` and `cfg.d`, before parsing the
command line, then check it in the shared writer before opening or truncating
the file. Older versions persisted this switch as `1`; loading that stale value
must not disable saving on a later launch without the flag. Default launches
and explicit `--no-config 0` save normally; an ordinary save replaces the stale
value with `0`.

Explicit `--no-config 1` suppresses all calls to this writer, including saves
from settings dialogs. Skipped saves return success, and option changes remain
available in memory for the session. Configurations that never register the
option still save. This concerns `fceux.cfg`, not every file the emulator writes.

Added a standalone C++ regression test covering existing/missing files, repeated
saves, in-memory changes, default launching with a stale saved flag, auxiliary
config loading, explicit overrides, generic configurations, and write errors:

```sh
cmake -S tests -B build/config-tests
cmake --build build/config-tests
ctest --test-dir build/config-tests --output-on-failure
```

The standalone test needs no Qt, SDL, ROM, or emulator process. It is not wired
into the main build or upstream CI; run it with the commands above.

Validated on macOS ARM64 with a fresh Qt release build, standalone CTest, and
eight rejected mutations plus an upstream-source negative control. Seven
completed headless runs of the revision cover stale main/auxiliary configs,
explicit flags and a missing config. Matching upstream and first-revision
controls reproduce their respective save failures. One earlier run of the new
binary timed out after frame 1 while correctly saving the config; it is retained
as a failed capture, not counted as a passing run. A separate investigation
identified a startup race in unmodified corrected-release Qt code: emulator
thread classification depends on a window pointer assigned after the thread
starts, allowing a leaked `reqEmuLock` request. That race also stalls unmodified
upstream and is consistent with this timeout; no stack or counter sample was
taken for this particular failed run. This config patch does not fix the race.

AI assistance: OpenAI Codex (GPT-6) prepared the patch and tests and ran automated
checks. Claude Opus 5.5 identified the first revision's stale-config regression
and approved this revision after independent tests, mutations, live config cases
and build-provenance checks. Human contributor review remains pending before
submission.
