# FCEUX 2.7.0 Qt startup mutex backport

Standard FCEUX installations remain supported; NESrev does not require a custom
emulator. For the optional workaround, clone-to-setup instructions and retirement
policy, use [LOCAL_BUILD.md](LOCAL_BUILD.md). For future FCEUX or Homebrew
contributions, use the [tracked upstream handoff](upstream/README.md).
The [review instructions](REVIEW.md) and [evidence packet](evidence/README.md)
support review from a fresh clone.
The instructions below describe the original mutex-only backport and its
historical validation.

This optional backport removes a reproduced zero-frame startup spin in the
macOS ARM64 release build. It does not replace the installed emulator, change
NESrev's default executable, or retry failed captures. Independent review and
a fresh agent smoke gate adoption. The delivery record is in the
[process plan](../../../PROCESS_IMPROVEMENT_PLAN.md#fceux-startup-reliability).

## Source and scope

Base: the original target of upstream tag `fceux-2.7.0`, commit
[`a6d03e7968bd77a8156a7c9b628a673753f2f4c6`](https://github.com/TASEmulators/fceux/tree/a6d03e7968bd77a8156a7c9b628a673753f2f4c6).
The tag was subsequently moved; use this exact commit for the backport.
The [patch](2.7.0-static-mutex.patch) backports only the static-mutex hunks from
upstream commit
[`01f01cc547268fbbb4ce4e98b812bf53c727edf0`](https://github.com/TASEmulators/fceux/commit/01f01cc547268fbbb4ce4e98b812bf53c727edf0)
(2026-10-12, “More TSAN warning fixes.”). Upstream's queued signal connections
and script-manager changes are outside this backport. FCEUX source remains
under its upstream license; this is an upstream-derived patch, not vendored
emulator source.

`main()` assigns `consoleWindow` after its constructor returns, but that
constructor starts the emulator thread. The thread's `fceuWrapperTryLock()`
depends on that pointer. In the installed optimized binary, a null read enters
a loop that never reloads it. A live sample of a failed capture places every
sampled emulator-thread instruction in that loop; the UI thread remains active.
The backport makes the two mutexes static and removes the pointer dependency
from lock, try-lock and unlock. It does not claim to fix every emulator race.

## Isolated build

Build in a standalone checkout outside any other Git repository so FCEUX's
generated Git metadata describes its own source. Use the exact base above.
With that checkout selected as the working directory, apply the patch from
the NESrev checkout:

```sh
git rev-parse HEAD
shasum -a 256 src/drivers/Qt/ConsoleWindow.h src/drivers/Qt/fceuWrapper.cpp
patch --dry-run -p1 -i /absolute/path/to/nesrev/scripts/patches/fceux/2.7.0-static-mutex.patch
patch -p1 -i /absolute/path/to/nesrev/scripts/patches/fceux/2.7.0-static-mutex.patch
cmake -S . -B build -DQT6=ON -DPUBLIC_RELEASE=1 -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_PREFIX_PATH=/opt/homebrew \
  -DCMAKE_DISABLE_FIND_PACKAGE_Qt6Qml=TRUE \
  -DCMAKE_DISABLE_FIND_PACKAGE_Qt6UiTools=TRUE
cmake --build build --parallel 6
```

Refuse a different base or input hashes. The zero-context patch is specific to
these files; it is not a version-independent installer:

| Input | SHA-256 |
|---|---|
| `ConsoleWindow.h` | `660c8c2f0bbcaee16d2899d02009c61af3054249395353b8e72032fc45437ed9` |
| `fceuWrapper.cpp` | `9b9fb41f114cfbe761546ed1e5385164391f12b0f8dc58cfce35a8b2741e5eb1` |

The macOS executable is `build/src/fceux.app/Contents/MacOS/fceux`.
Use a separate executable path, record its hash, and select it with the
supervisor's existing `--fceux` option or `FCEUX_BIN` environment variable.
Drivers that invoke FCEUX directly need their own explicit selection.
Record the supervisor path and hash alongside the executable so cleanup
results can be attributed to the runner that produced them.
Do not overwrite the Homebrew binary. Unsetting `FCEUX_BIN` restores the
supervisor's normal executable lookup.

Builds without the [config-saving patch](2.7.0-no-config.patch), including this
mutex-only backport, rewrite `SDL.LastOpenFile` and `SDL.LuaScript` in
`~/.fceux/fceux.cfg` even with `--no-config 1`. Use an isolated configuration
directory for probes and compare it afterward. The combined local build includes
that config fix; it protects `fceux.cfg`, not every file the emulator writes.

The diagnostic builds used CMake 3.31.6, Apple Clang, Release optimization,
Qt 6.12.0, SDL2 compatibility 2.32.74 and bundled Lua. Optional Qt QML/UiTools
were disabled; libarchive was not discovered. These are local build results,
not validation of other operating systems or dependency combinations.

## Regression probe

From the NESrev root, use a user-supplied ROM and a fresh output parent:

```sh
python3 scripts/run_fceux_trace.py \
  --fceux /absolute/path/to/patched/fceux \
  --rom /absolute/path/to/supplied.nes \
  --lua scripts/patches/fceux/frame_advance.lua \
  --max-frames 60 --timeout 8 --completion-line COMPLETE \
  --output-dir tmp/fceux-startup-probe
```

The [probe](frame_advance.lua) uses maximum speed, advances exactly 60 frames
before its completion marker, and leaves shutdown to the supervisor. It has
no memory hooks, game-state writes, input bot, or screenshot calls. Success
requires supervisor exit 0 and every `frame=1` through `frame=60` line in order.
It proves startup/frame advancement only, not gameplay semantics.

To expose the startup window reproducibly, use disposable builds of both base
and backport. Add `QThread::msleep(250);` immediately after
`emulatorThread->start();` in `src/drivers/Qt/ConsoleWindow.cpp` in each.
Run the same probe three times per build, retaining every attempt. The original
build must time out before `frame=1`, with its emulator thread sampled in
`fceuWrapperUpdate()`'s null-pointer spin. The backport must reach all 60 frames.
Exclude this diagnostic delay from the executable selected for real captures.

A separate normal-speed probe stopped after one frame in `SpeedThrottle()` on
both unpatched and patched local builds. The cause is the base's per-thread
timestamp normalization; [LOCAL_BUILD.md](LOCAL_BUILD.md) applies upstream's fix as
a third patch. These maximum-speed tests still do not validate normal-speed
playback or listening. Existing
shutdown crashes also remain outside the backport. The supervisor continues
to distinguish its deliberate post-completion stop from an unexpected crash.
Never reclassify a failed historical smoke from later diagnostic successes.
