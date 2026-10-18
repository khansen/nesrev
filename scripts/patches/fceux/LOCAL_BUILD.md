# Optional local FCEUX workaround

<a id="local-policy"></a>
## Local policy

NESrev does not require this build. Use a suitable standard FCEUX installation
for runtime work; the supervisor normally finds `fceux` on `PATH`, with
`--fceux` or `FCEUX_BIN` available for explicit selection. Cloning NESrev does
not install, build, activate or require the patched emulator. Missing FCEUX
does not block static work; runtime-dependent claims still need runtime evidence.

This opt-in workaround covers reproduced problems on one macOS ARM64 setup.
The pin is a temporary compatibility choice, not a permanent supported-version
ceiling or a requirement for other platforms. Keep the reviewed fixes local
for now; upstream submission is independent of using or retiring the workaround.
The [tracked upstream handoff](upstream/README.md) contains the patches, drafts
and shareable reproducer evidence for a future contributor.

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

To reproduce this particular workaround, use the exact commit rather than the
moving `fceux-2.7.0` tag. Newer releases are welcome: evaluate them separately
using the [upgrade and retirement procedure](#retire-local-workaround), rather
than applying these version-specific patches blindly. The combined build needs
its own runtime checks even though both constituent patches were reviewed. No
new independent review or agent smoke is implied by coordinator-run checks.

<a id="select-local-build"></a>
## Select the local build

The original maintainer's installation is under
`$HOME/.local/share/nesrev/fceux`. A fresh clone does not have that installation;
follow [setup from a clone](#setup-from-clone) only if opting into the workaround.
The layout has immutable `releases/` directories, an explicitly selected
`current` symlink, a dedicated `config/`, and an `activate.sh` copy. Source and
build records live alongside the release. Homebrew's executable and links are
left intact. A Homebrew upgrade must not change `current`.

After opting in, before starting a fresh agent session from the NESrev checkout:

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

The original maintainer's machine also has
`$HOME/.local/share/nesrev/fceux/start-review`, which
activates the profile, enters the recorded NESrev checkout and forwards its
arguments to the normal tmux launcher. That site-specific convenience wrapper
is not part of a clone or required by NESrev. The activation and normal launcher
commands above work without it. Neither refreshes an existing session.

<a id="rebuild-local"></a>
## Rebuild and record provenance

Build in a standalone FCEUX checkout outside the NESrev repository. This recipe
was validated with macOS ARM64, Apple Clang, CMake 4.4.4 and Homebrew Qt 6.12;
other environments need their own dependency setup and validation. Follow
upstream's [build instructions](https://github.com/TASEmulators/fceux/blob/a6d03e7968bd77a8156a7c9b628a673753f2f4c6/README)
for prerequisites; the example disables optional Qt QML and UiTools. Use fresh
source/build directories, never the active release.
The original installation's private source bundle and logs are useful historical
evidence, but are not required to reproduce the build from a clone. For example:

```sh
NESREV_ROOT=/absolute/path/to/your/nesrev
FCEUX_SOURCE=/absolute/path/to/a/new/fceux-source
git clone https://github.com/TASEmulators/fceux.git "$FCEUX_SOURCE"
cd "$FCEUX_SOURCE"
```

With those paths set, check out the pinned commit,
verify the input hashes in the [backport README](README.md), and apply both
patches with a successful dry-run before each application:

```sh
git checkout --detach a6d03e7968bd77a8156a7c9b628a673753f2f4c6
patch --dry-run -p1 -i "$NESREV_ROOT/scripts/patches/fceux/2.7.0-static-mutex.patch"
patch -p1 -i "$NESREV_ROOT/scripts/patches/fceux/2.7.0-static-mutex.patch"
patch --dry-run -p1 -i "$NESREV_ROOT/scripts/patches/fceux/2.7.0-no-config.patch"
patch -p1 -i "$NESREV_ROOT/scripts/patches/fceux/2.7.0-no-config.patch"
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
source/build provenance and `SHA256SUMS`. Keep source and
validation records outside the executable directory so active files remain
unchanged. Generate checksums after final copying, and verify them before
switching the `current` symlink. Retain the previous symlink target for rollback.

<a id="setup-from-clone"></a>
## Set up the optional profile from a clone

After building as above, stage a new release with the following commands. They
need only this clone and your own FCEUX source/build tree. Use a writable local
directory and retain the build logs alongside it. Stop if a command fails;
the initial `test` prevents overwriting an existing release.

```sh
export NESREV_FCEUX_ROOT="${XDG_DATA_HOME:-$HOME/.local/share}/nesrev/fceux"
FCEUX_RELEASE="$NESREV_FCEUX_ROOT/releases/2.7.0-nesrev1"
test ! -e "$FCEUX_RELEASE" || exit 1
mkdir -p "$FCEUX_RELEASE/bin" "$FCEUX_RELEASE/share" "$FCEUX_RELEASE/patches"
cp "$FCEUX_SOURCE/build/src/fceux.app/Contents/MacOS/fceux" "$FCEUX_RELEASE/bin/"
cp "$NESREV_ROOT/scripts/patches/fceux/tmux-local-fceux" "$FCEUX_RELEASE/bin/"
cp -R "$FCEUX_SOURCE/output/luaScripts" "$FCEUX_RELEASE/share/"
cp "$FCEUX_SOURCE/src/auxlib.lua" "$FCEUX_RELEASE/share/luaScripts/"
cp "$FCEUX_SOURCE/COPYING" "$FCEUX_RELEASE/"
cp "$NESREV_ROOT/scripts/patches/fceux/2.7.0-static-mutex.patch" "$FCEUX_RELEASE/patches/"
cp "$NESREV_ROOT/scripts/patches/fceux/2.7.0-no-config.patch" "$FCEUX_RELEASE/patches/"
git -C "$FCEUX_SOURCE" rev-parse HEAD > "$FCEUX_RELEASE/UPSTREAM_COMMIT"
cp "$NESREV_ROOT/scripts/patches/fceux/activate.sh" "$NESREV_FCEUX_ROOT/"
mkdir -p "$NESREV_FCEUX_ROOT/config"
python3 - "$FCEUX_RELEASE" <<'PY'
import hashlib
from pathlib import Path
import sys
root = Path(sys.argv[1])
files = sorted(p for p in root.rglob('*') if p.is_file() and p.name != 'SHA256SUMS')
(root / 'SHA256SUMS').write_text(''.join(
    hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(root).as_posix() + '\n'
    for p in files))
PY
```

Run the [acceptance checks](#local-acceptance) against
`$FCEUX_RELEASE/bin/fceux` explicitly before activation. Use fresh output/config
directories; the synthetic ROM and Lua scripts are in the tracked
[upstream attachment bundle](upstream/startup-race-attachments.zip).
Record your own platform, dependency versions, commands and results; the original
maintainer's results do not validate your build. For an initial installation:

```sh
test ! -e "$NESREV_FCEUX_ROOT/current" && test ! -L "$NESREV_FCEUX_ROOT/current" || exit 1
ln -s "$FCEUX_RELEASE" "$NESREV_FCEUX_ROOT/current"
cd "$NESREV_ROOT"
. "$NESREV_FCEUX_ROOT/activate.sh" && python3 scripts/agent_review_tmux.py --help
```

This last command checks setup without starting agents. Start an authorized
project session with the same activation followed by the normal launcher.
For later replacements, record the old `current` target before deliberately
switching it to a validated release. A shared clone never selects someone else's
absolute executable path or copies their binary automatically.

<a id="local-acceptance"></a>
## Acceptance and maintenance

Before selecting a rebuilt or upgraded emulator:

- Run the standalone config tests; verify the no-config guard and stale-flag
  cases. A disposable copy with the config fix reverted must fail those tests.
- Test first launches of freshly copied binaries with the synthetic ROM, not
  just repeated launches of one executable. Use fresh config directories and
  preserve every attempt. A help-only launch does not start the emulator thread.
- Use the [bounded frame probe](README.md#regression-probe) across available
  user-supplied ROMs, then replay an existing accepted gameplay scenario and
  compare its analyzer verdict, trace and screenshots. If a fresh clone has no
  project ROMs/scenarios yet, record synthetic-startup-only qualification; require
  project-specific gameplay acceptance before relying on semantic conclusions.
  A startup probe does not establish gameplay semantics or listening quality.
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
stock FCEUX or relabel an earlier failure after a successful rerun.

<a id="retire-local-workaround"></a>
## Reassess, upgrade and retire the workaround

The operator maintaining an opted-in installation owns this check. Reassess
when a new FCEUX release or package revision appears, before rebuilding after
a dependency upgrade, or when a relevant fix is reported. If still actively
using the pin, check at least once per quarter even without a report. This is
a maintenance responsibility, not an installed background updater or promise
that this repository monitors releases automatically.

1. Inspect current upstream releases, commits and issues, and the package's
   actual source revision. Search for both startup races and config-saving
   behavior. Record the date, platform, exact candidate version/source/binary
   hash and links, including a concrete reason if retaining the workaround.
2. Prefer testing an unmodified standard package first. Use an explicit
   candidate path and isolated settings while keeping the working installation
   available. Repeat cold-start, config and relevant gameplay checks above;
   include normal-speed/audio checks if those are part of your workflow.
   Passing `--help` alone does not qualify a runtime upgrade.
3. Once a standard release satisfies the needed behavior, adopt it even if our
   patches were never submitted or were fixed differently upstream. Do not
   require matching commit IDs or patch text. If only part is fixed, remove the
   redundant patch and separately review/test any remaining minimal patch on
   the newer base; do not carry this old pin forward by habit.
4. In a fresh shell, stop sourcing this profile and use the normal launcher.
   If reusing a shell, remove only this profile's `FCEUX_BIN`, `FCEUX_CONFIG_DIR`,
   `LUA_PATH` addition and `AGENT_REVIEW_TMUX_BIN` selection, restoring any prior
   custom values. Restart completed agent sessions; a reconnect retains their
   old environment. Check the next capture's recorded executable path/hash.
5. Keep the old release for a short rollback window, such as one successful
   reviewed runtime pass. Then remove its activation hooks and archive or
   delete the obsolete local binary at the operator's discretion. Preserve
   the historical patches/evidence, mark this workaround retired for the tested
   platform in the maintenance record, and make the standard release the
   documented recommendation. Do not silently re-enable the workaround.

Record each reassessment alongside the installation's build records with
`date | candidate/platform | evidence | decision | remaining gap | next trigger`.
Update this document when a reusable platform-level conclusion is established.
Retiring the runtime workaround does not require deleting the upstream handoff.

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

The portability follow-up checked a clean export of the tracked files, applied
both patches to a fresh pinned source checkout and reran config CTest. The setup
recipe passed with spaces in the clone and installation paths, reusing the
already validated binary to test packaging only. Both submission patches pass
their historical-base application checks; all bundle hashes and relative doc
links resolve. No new Qt build, emulator capture or agent session was run for
this documentation follow-up. Default launcher/supervisor help also works with
all local-profile environment variables absent.
