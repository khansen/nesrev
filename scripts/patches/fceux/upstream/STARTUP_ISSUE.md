> Unsubmitted draft, last validated 2026-10-18. Recheck current upstream state,
> reproduce relevant results, and follow [the handoff checklist](README.md) before posting.

Title: Qt startup race can leak reqEmuLock and stall emulation after frame 1

The corrected 2.7.0 release at `8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8` can
stall after frame 1. Fresh copies of an unmodified, source-built Homebrew keg
stalled 3/3 times; repeat launches of those copies passed 3/3.

The thread sample and lldb observations below came from fresh copies of the
**revision-2 build with the separate `--no-config` patch**, not from the keg.
That patch changes shared config parsing/saving and adds tests; it does not touch
Qt threading. The unmodified keg reproduced the stall but was never sampled or
inspected with lldb. The tested environment was macOS 27.0.1 ARM64, Qt 6.12.0.

On the revision-2 copy, the sample shows the emulator thread yielding in
`fceuWrapperUpdate()`, with the GUI thread mostly waiting in its event loop.
The reviewer reported these lldb readings, twice for each state:

| State | `reqEmuLock` | `mutexLocks` |
|---|---|---|
| Stalled revision-2 copy | 1 | 0 |
| Healthy revision-2 copy | 0 | 1 |

The debugger output was displayed during review but was not saved. These values
are reviewer-reported observations, not a recovered transcript. The thread
sample and associated traces/logs are preserved in the attachment bundle.

## Source-level explanation

The thread identity predicate depends on `consoleWindow`, which is published
only after its constructor returns:

- [`main.cpp:171`](https://github.com/TASEmulators/fceux/blob/8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8/src/drivers/Qt/main.cpp#L171)
  assigns `consoleWindow = new consoleWin_t()`.
- [The constructor starts the emulator thread](https://github.com/TASEmulators/fceux/blob/8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8/src/drivers/Qt/ConsoleWindow.cpp#L203)
  before that assignment occurs.
- [`fceuOnEmulationThread()`](https://github.com/TASEmulators/fceux/blob/8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8/src/drivers/Qt/fceuWrapper.cpp#L1385)
  returns false while `consoleWindow` is null.
- [Entry and exit preemption logic](https://github.com/TASEmulators/fceux/blob/8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8/src/drivers/Qt/fceuWrapper.cpp#L1392)
  independently call that predicate to increment/decrement `reqEmuLock` for
  non-emulator threads.

That permits this interleaving:

1. The emulator thread enters a wrapper lock while `consoleWindow` is null.
   It is misclassified as a non-emulator thread and increments `reqEmuLock`.
2. The window constructor returns and `main()` assigns `consoleWindow`.
3. The same emulator thread releases the lock. It is now classified as the
   emulator thread, so the exit logic skips the matching decrement.
4. At its next outer lock entry, the emulator thread loops on the leaked request
   in `QThread::yieldCurrentThread()`, although no other thread holds the mutex.

This interleaving is inferred from the source and observed counter/stack state;
it was not recorded instruction by instruction. The source inspection was
repeated separately from the reviewer's live experiments.

## Reproduction and observations

All experiments used the same original synthetic NROM program: write decimal
42 to RAM address zero and loop. No commercial ROM is needed. The exact common
frontend arguments were:

```text
--no-config 1 --gamegenie 0 --sound 0 --videoDriver 2 --loadlua <lua> <rom>
```

The common environment was `QT_QPA_PLATFORM=minimal` and
`SDL_VIDEODRIVER=dummy`, with a fresh `FCEUX_CONFIG_DIR` per run. The reviewer also
isolated each run's home directory. `--no-config 1` alone does not isolate config
writes in unmodified upstream. The keg harness additionally used `LC_ALL=C` and
`LUA_PATH=/opt/homebrew/Cellar/fceux/2.7.0_1/share/fceux/luaScripts/?.lua`.

The scripts differed by experiment; the exact files are included in the bundle:

| Experiment | Build | Lua script and completion behavior |
|---|---|---|
| Keg-copy formula-test rows | Unmodified corrected-release keg | `formula-test.lua`: maximum speed, 60 frames, writes the RAM byte to `result.txt`, then `emu.exit()` |
| Thread sample (`resign5-l1`) | Revision 2 with config patch | `maximum-exit.lua`: maximum speed, logs each frame, asserts the sentinel after 60 frames, writes `COMPLETE`, then `emu.exit()` |
| lldb observations (`lldb-l1`, `lldb-l2`) | Revision 2 with config patch | `maximum-supervised.lua`: same trace/assertion, then continues advancing frames indefinitely; it never calls `emu.exit()` |

For the keg case, run from a fresh output directory so `result.txt` is local to
that attempt. For the other two scripts, set `TRACE_OUT` to that attempt's
absolute `trace.log` path. Supply the bundled `own-test.nes` as `<rom>`.
The keg harness imposed a 30-second bound. All launches were externally bounded;
`maximum-supervised.lua` requires external termination even on a healthy launch.

To exercise the problematic case, copy the executable to a new path, run that
copy for the first time, then compare a second launch of the same copy. Preserve
both results. Of the six revision-2 first launches, four used re-signed copies and two used
plain copies with unchanged signatures; both plain copies stalled too. Warm-up
is not a reliable remedy.
The reviewer reported:

| Case | Result |
|---|---|
| First launch of three fresh unmodified keg copies | 0/3 passed; frame-1 stall, 30-second timeout |
| Second launch of those same copies | 3/3 passed, about 0.19 seconds each |
| First emulation launch after `--help` (`kB0`, `kB1`) | 1/2 passed |
| First launch after letting the copy sit for 45 seconds (`kA0`, `kA1`) | 1/2 passed |

There were **21 emulator launches plus two `--help` warm-ups**: 13 first
emulation launches of newly written copies (including four warm-up/wait cases)
and eight repeat launches. Among the nine first launches without those four
controls, all nine stalled: six revision-2 copies and the three keg copies above.
These sets overlap; do not add the 9/9 and 3/3 figures. One stall lasted at least
60 seconds.

Why freshly written executable files favor the race is unproven. Slower startup
is a hypothesis, not a measured explanation, and these small samples do not
establish its frequency on other machines.

## Attachments

The [attachment bundle](startup-race-attachments.zip) contains the full thread
sample, its frame-1 trace, both debugger-run traces/logs, the six keg-run logs and
three successful `result.txt` files, the four warm-up/wait control logs with two
successful result files, all three Lua scripts, and the original synthetic ROM.
The reviewer confirmed from the launch commands that A copies waited 45 seconds
and B copies received the `--help` warm-up. A0 and B0 passed; A1 and B1 stalled.
Missing first-launch result files are not fabricated. The bundle
also records the debugger values as reviewer-reported observations and includes
SHA-256 checksums. Local user/session paths in the logs are replaced with generic
paths, including account-specific macOS temporary folders. Stack addresses,
symbols and sample counts are preserved. The sample already had its local paths
abbreviated by the sampling tool; its timestamps and timezone are retained.

The sampled run's trace and the stalled debugger trace end at `FRAME 1`; the
healthy debugger trace reaches `COMPLETE`. These artifact checks were performed after copying;
no new emulator or debugger run was made while preparing this report.

## Possible correction

Make emulator-thread identification independent of window publication, for
example with a thread-local flag set at the beginning of
[`emulatorThread_t::run()`](https://github.com/TASEmulators/fceux/blob/8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8/src/drivers/Qt/ConsoleWindow.cpp#L5168).
Alternatively, arrange publication before starting the thread while preserving
construction safety. Entry and exit must classify the same thread consistently.
Neither option has been implemented or validated as part of this report.

This differs from the older frame-zero null-window loop fixed by
[`01f01cc5`](https://github.com/TASEmulators/fceux/commit/01f01cc547268fbbb4ce4e98b812bf53c727edf0).
It also does not establish the cause of older timeouts that lack a thread sample
or counter read. Linux and Windows were not tested.

AI assistance: OpenAI Codex (GPT-6) checked the source and drafted this report.
Claude Opus 5.5 performed the independent fresh-copy experiments, thread sample
and debugger inspection described above.

<!-- Before publication: upload startup-race-attachments.zip and replace the
local attachment link with the uploaded URL. No raw debugger transcript exists;
do not present the reviewer-reported counters as a saved transcript. -->
