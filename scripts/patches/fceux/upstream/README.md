# Deferred FCEUX and Homebrew contributions

This handoff is intentionally tracked so a fresh NESrev clone is sufficient to
resume the work. It contains source patches, submission drafts and sanitized
reproducer evidence, not installed software. Nothing here has been submitted.
All validation and review statements describe the 2026-10-18 work; check current
upstream state before deciding whether any contribution is still needed.

The [optional local workaround](../LOCAL_BUILD.md) is a separate operational
choice. A contributor may submit either change without adopting that build,
or retire the local build without submitting either change.

<a id="contribution-map"></a>
## What belongs where

| Item | Target and preserved material | Status and scope |
|---|---|---|
| Honor `--no-config` for every `fceux.cfg` save | FCEUX: [approved source/test patch](../2.7.0-no-config.patch), [PR draft](FCEUX_PR.md) | Revision 2 independently approved; not submitted. Reset stale saved flags after both config loads, then guard the shared writer. |
| Correct Homebrew's original 2.7.0 source pin | Homebrew/homebrew-core: [approved formula patch](homebrew-corrected-release.patch), [PR draft](HOMEBREW_PR.md) | Only changes the source revision and adds formula `revision 1`. No new functional test, bottle edit or install change. |
| Frame-one `reqEmuLock` startup race | FCEUX: [issue draft](STARTUP_ISSUE.md), [attachment bundle](startup-race-attachments.zip) | Reproduced on corrected-release binaries; an inferred source interleaving explains the sampled state. No proposed fix has been implemented/tested. |
| Older frame-zero null-window spin | [Local static-mutex backport](../2.7.0-static-mutex.patch) and [reproduction](../README.md#regression-probe) | Already fixed upstream by `01f01cc547268fbbb4ce4e98b812bf53c727edf0`; do not submit the backport as a new upstream fix. |

The Homebrew patch is **not** the local combined emulator fix. Its corrected
release still exhibited the separate frame-one race and lacks our config patch.
It is a historical packaging correction, not a recommendation to adopt that
binary for NESrev captures. A newer formula/release may make it obsolete.

<a id="bases-and-evidence"></a>
## Bases, hashes and evidence

- FCEUX submission base: `8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8`.
  This differs from the older local workaround base. The config implementation
  before patching was byte-identical on both bases.
- Homebrew submission base: `1181198bec91c780340f3aabb68b2708349bec16`.
  The target file is `Formula/f/fceux.rb`; the historical tag changed from
  `a6d03e7968bd77a8156a7c9b628a673753f2f4c6` to the corrected FCEUX commit above.
- [manifest.json](manifest.json) records exact patch, draft and bundle hashes,
  the reviewed bases and sampled binary identities. The config patch hash is
  `0ac7d1f5da0e4a553d8e13fb582dbdd1a7fd9b8aed9ed62c22c7c59102b7a67c`;
  the formula patch hash is
  `02960b524280428604e3470552f6591d2bd13f51428a5c0aea5af2922867ece5`.
- The zip contains 29 files, including a checksum file covering the other 28.
  Extract it into a new directory, enter `startup-race-attachments/`, then run
  `shasum -a 256 -c SHA256SUMS`. Its ROM is an original synthetic sentinel
  program; no commercial ROM, emulator binary or personal config is included.
- The full thread sample and associated traces/logs are retained. Debugger
  counters are explicitly reviewer-reported; no raw debugger transcript was
  saved. Sampling used config-patched revision-2 copies. Unmodified corrected
  keg copies reproduced the stall but were not sampled.

Historical checks: standalone config tests passed on revision 2 and failed seven
checks on upstream and five stale-flag checks on revision 1. The designated
reviewer caught 11 mutations and ran seven successful live config cases. The
earlier config packet retained 22 attempts: 21 completed and one frame-one
timeout. A separate reviewer startup experiment had 21 emulator launches plus
two help warm-ups; see the issue draft for the overlapping first-launch counts.
The reduced formula passed source-build-backed `brew lgtm` checks on macOS.

These are dated evidence summaries. The original upstream-build logs, tested
binaries and private working copies are not distributed here. Full logs and
synthetic captures for the separate older-base combined workaround are in the
[tracked evidence packet](../evidence/README.md). A new contributor must rebuild and
rerun relevant checks rather than claim the archived review as their own work.
The two patches and bundle suffice to reproduce their tests and the startup
experiment without access to the original maintainer's home or temporary files.

<a id="resume-contribution"></a>
## Resume a contribution

1. Search current releases, formula history, open/closed PRs and issues in
   [FCEUX](https://github.com/TASEmulators/fceux) and
   [homebrew-core](https://github.com/Homebrew/homebrew-core). Recheck the tag's
   actual commit. If a fix already exists, test it and link the result instead
   of reopening obsolete work.
2. Read current repository contribution/signing rules and issue/PR templates.
   A historical approval applies only to the preserved patch, not a later port.
   Create a fresh branch from the target's current default branch. Use
   `git apply --check` before applying the corresponding patch; review a port
   manually if context or behavior changed. Never force the old source pin or
   formula revision onto a newer release just to make the patch apply.
3. For FCEUX, run the standalone C++ tests included in the patch:

   ```sh
   cmake -S tests -B build/config-tests
   cmake --build build/config-tests
   ctest --test-dir build/config-tests --output-on-failure
   ```

   They require no emulator, Qt, ROM or display. Also build the relevant frontend
   and check isolated live config cases: explicit `1` preserves an existing file
   and creates none when absent; stale `1` from the main file or `cfg.d` must not
   disable a no-flag save; explicit `0` saves; write errors remain errors. Show
   the tests fail when the guard or post-load reset is removed. The standalone
   test is not wired into upstream's main build/CI. Preserve any timeout as a
   failed capture, independently of observed config behavior.
4. For Homebrew, use its current [contribution instructions](https://docs.brew.sh/How-To-Open-a-Homebrew-Pull-Request)
   and [formula revision guidance](https://docs.brew.sh/Formula-Cookbook#formulae-revisions).
   Build from source and run the required checks in the actual tap immediately
   before submission. Leave the bottle block to maintainers. The archived
   `--help` test is deliberate: the discarded functional test failed on first
   launches. Linux was not validated by this work. Keep checklist boxes unticked
   until the submitting contributor has actually satisfied them.
5. Review and update each draft's dates, scope, evidence and AI disclosure.
   Keep FCEUX config changes, the Homebrew packaging correction and the startup
   issue separate. For the issue, reproduce on a current build where practical,
   identify exactly which build was sampled, and upload the sanitized bundle
   before replacing its local link with a public attachment URL. Inspect the
   attachment for privacy again before uploading.
6. Only then commit with the contributor's identity/signing configuration and
   submit. Record resulting URLs and final upstream commits here. No command
   in NESrev automatically submits, uploads or accepts maintainer feedback.

Homebrew's [AI policy](https://docs.brew.sh/How-To-Open-a-Homebrew-Pull-Request#artificial-intelligencelarge-language-model-aillm-usage),
checked for this handoff, requires disclosure of the tools/models, human review
before requesting maintainer review, no AI commit attribution, and personal
responses to maintainer questions/review without AI. Re-read the current policy
before submitting. Historical assistance was OpenAI Codex (GPT-6) and independent
review by Claude Opus 5.5; add any later assistance accurately.
