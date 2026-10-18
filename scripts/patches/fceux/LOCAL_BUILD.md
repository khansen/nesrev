# Maintained local FCEUX for NESrev

<a id="local-policy"></a>
## Local policy

Keep the reviewed emulator fixes local for now. No upstream PR or issue is
required to use this build. Preserve the source, patches and evidence so a later
submission or rebuild does not depend on a temporary directory.

Pin upstream commit `a6d03e7968bd77a8156a7c9b628a673753f2f4c6`, then apply these
two patches in order:

1. [Static mutex backport](2.7.0-static-mutex.patch): fixes the reproduced
   frame-zero null-window-pointer spin. This patch passed independent review
   and a subsequent live agent smoke.
2. [Config saving fix](2.7.0-no-config.patch): the independently approved
   revision-2 patch, including its standalone regression tests. Explicit
   `--no-config 1` suppresses writes; stale saved flags do not disable saving
   on later ordinary launches. The parser and header are byte-identical in
   this base and the newer base used for the independent config review.

The corrected 2.7.0 release at `8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8`
contains a separate frame-one startup race in its `reqEmuLock` preemption code.
That code is absent from the pinned base. The local build avoids that regression
by retaining the older source plus the two reviewed fixes; it does not claim
to repair the newer release's preemption implementation.

Do not build from the moving `fceux-2.7.0` tag, `master`, or an arbitrary newer
Homebrew keg. The new combined build needs its own runtime checks even though
both constituent patches were reviewed. No new independent review or agent
smoke is implied by those coordinator-run checks.

<a id="select-local-build"></a>
## Select the local build

The maintained installation is under `$HOME/.local/share/nesrev/fceux` on this
machine. It has immutable `releases/` directories, an explicitly selected
`current` symlink, a dedicated `config/`, and an `activate.sh` copy. Source and
build records live alongside the release. Homebrew's executable and links are
left intact. A Homebrew upgrade must not change `current`.

Before starting a fresh agent session, from the NESrev checkout:

```sh
. "$HOME/.local/share/nesrev/fceux/activate.sh" &&
python3 scripts/agent_review_tmux.py --project <slug>
```

Use the same activation before standalone project trace commands. The profile
checks the selected release's checksums and fails if a required file is missing
or changed. Keep the `&&`: a failed activation must stop the launch rather than
fall back to the stock binary. `NESREV_FCEUX_ROOT` can select an installation
elsewhere; the default also respects `XDG_DATA_HOME`.

The profile exports `FCEUX_BIN`, `FCEUX_CONFIG_DIR`, and the bundled Lua search
path. It also selects a small tmux adapter through `AGENT_REVIEW_TMUX_BIN`.
The adapter sets those three runtime variables on each new session explicitly;
an already-running tmux server would otherwise keep its earlier environment.
Other tmux commands pass through unchanged. The profile does not change `PATH`.
The supervisor reads `FCEUX_BIN`; a driver
that hardcodes `fceux` or passes its own `--fceux` must be corrected or given
the selected path explicitly. Confirm `result.json`'s command names the selected
release. Existing agents retain their launch environment: stop a completed
session and start fresh after selecting a different build.

Plain `fceux` still resolves through the normal shell path. The profile is not
a global replacement and must be used for each fresh session. Keep automated
captures bounded with the existing supervisor; do not add retries that conceal
failed startup attempts.

This machine also has `$HOME/.local/share/nesrev/fceux/start-review`, which
activates the profile, enters the recorded NESrev checkout and forwards its
arguments to the normal tmux launcher. Use it for fresh sessions to avoid
forgetting activation. It does not restart or alter an existing session.

<a id="rebuild-local"></a>
## Rebuild and record provenance

Build in a standalone FCEUX checkout outside the NESrev repository. Use a fresh
source and build directory; never build over the active release. The initial
local setup preserves a source Git bundle, the patched source checkout, the
patches and build logs for offline reconstruction. Check out the pinned commit,
verify the input hashes in the [backport README](README.md), and apply both
patches with a successful dry-run before each application:

```sh
git checkout --detach a6d03e7968bd77a8156a7c9b628a673753f2f4c6
patch --dry-run -p1 -i /path/to/nesrev/scripts/patches/fceux/2.7.0-static-mutex.patch
patch -p1 -i /path/to/nesrev/scripts/patches/fceux/2.7.0-static-mutex.patch
patch --dry-run -p1 -i /path/to/nesrev/scripts/patches/fceux/2.7.0-no-config.patch
patch -p1 -i /path/to/nesrev/scripts/patches/fceux/2.7.0-no-config.patch
cmake -S tests -B config-tests
cmake --build config-tests
ctest --test-dir config-tests --output-on-failure
cmake -S . -B build -DQT6=ON -DPUBLIC_RELEASE=1 -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_PREFIX_PATH=/opt/homebrew \
  -DCMAKE_DISABLE_FIND_PACKAGE_Qt6Qml=TRUE \
  -DCMAKE_DISABLE_FIND_PACKAGE_Qt6UiTools=TRUE \
  -DCMAKE_POLICY_VERSION_MINIMUM=3.5
cmake --build build --parallel 6
```

Run the commands sequentially and stop on any failure. The final option keeps
this old source configurable with CMake 4; it does not change emulator logic.
Record compiler, CMake and linked library versions. Homebrew provides those
libraries, so dependency upgrades can require a rebuild even when this source
pin stays fixed. Keep the previous working release until the replacement passes.

Expected config-patch SHA-256:
`0ac7d1f5da0e4a553d8e13fb582dbdd1a7fd9b8aed9ed62c22c7c59102b7a67c`.
Expected patched `configSys.cpp` SHA-256:
`1410e35c6c10fb9bc33d33be46aa3a1272398925d15978df7d443d51bb410de9`.

The executable is `build/src/fceux.app/Contents/MacOS/fceux`. A maintained release
contains it at `bin/fceux`, the executable `tmux-local-fceux` adapter beside it,
upstream Lua scripts under `share/luaScripts`, the license, both patches,
a provenance manifest and `SHA256SUMS`. Keep source and
validation records outside the executable directory so active files remain
unchanged. Generate checksums after final copying, and verify them before
switching the `current` symlink. Retain the previous symlink target for rollback.

<a id="local-acceptance"></a>
## Acceptance and maintenance

Before selecting a rebuilt or upgraded emulator:

- Run the standalone config tests; verify the no-config guard and stale-flag
  cases. A disposable copy with the config fix reverted must fail those tests.
- Test first launches of freshly copied binaries with the synthetic ROM, not
  just repeated launches of one executable. Use fresh config directories and
  preserve every attempt. A help-only launch does not start the emulator thread.
- Use the [bounded frame probe](README.md#regression-probe) across the local
  corpus, then replay an existing accepted gameplay scenario and compare its
  analyzer verdict, trace and screenshots. A startup probe does not establish
  gameplay semantics or listening quality.
- Verify config and ROM hashes stayed unchanged. Record executable and
  supervisor hashes, requested/observed frame counts, timeout and child exit
  separately. The config patch protects `fceux.cfg`, not every file FCEUX writes.
- Select the candidate only after those checks pass. Fresh agent permission
  smoke is required when changing launch permissions or agent command routing.
  This setup keeps the agent/helper commands and permissions unchanged; its
  tmux adapter forwards runtime environment only. Verify that forwarding on an
  already-running disposable server. Record any agent smoke separately from
  direct coordinator captures.

The tested scope is macOS ARM64 with Qt 6.12 and maximum-speed supervised
automation. Normal-speed playback/listening remains unvalidated. Existing
post-completion shutdown crashes or forced kills remain visible in
`result.json`; they are not clean emulator exits. A timeout before completion
is always a failure. Do not promise that pinning eliminates every FCEUX bug.

If startup fails, retain the capture, verify the selected path and hash, then
inspect the failed run before changing the build. Do not silently fall back to
stock FCEUX or relabel an earlier failure after a successful rerun. When a future
upstream version demonstrably fixes the relevant races and config behavior,
repeat this acceptance procedure before retiring the local patches.

<a id="local-validation"></a>
## Initial combined-build validation — 2026-10-18

Executable SHA-256:
`978e47f17f33bc2ed799b5881b06e29954890aaa904f29a2790c2c0b6765c75c`.

- Full Qt Release build and standalone config tests pass. Reverting the config
  implementation to the pinned base makes the regression assertions fail.
- Five first launches of freshly copied binaries complete the 60-frame
  synthetic-ROM probe. All 23 configured project ROMs complete the 60-frame
  startup probe; this is startup coverage, not gameplay coverage for 23 games.
- One existing 1,500-frame natural-input gameplay replay is accepted by its
  analyzer. Its trace and all six screenshots match the accepted baseline.
- ROMs and isolated configurations are unchanged. The personal configuration
  is unchanged. These captures report emulator exit `-11` during deliberate
  post-completion shutdown; none is reported as a clean emulator exit.
- Activation succeeds in bash and zsh and blocks the dependent launch when
  the selected binary is changed or missing.
- On an already-running private tmux server, the adapter forwards all three
  runtime variables into both the first pane and a split pane. The same launch
  without the adapter loses them. The test includes spaces and Lua's trailing
  `;;`; no real agent session is started or changed.

The local installation retains the commands, raw results, executable and
supervisor hashes under `records/2.7.0-nesrev1/`. Records retain their original
capture paths; `records/2.7.0-nesrev1/README.md` maps those paths to the preserved
copies. Harness setup errors are retained separately from emulator results.
These are coordinator checks of the combined build, not a new independent
review or a live agent permission smoke.
