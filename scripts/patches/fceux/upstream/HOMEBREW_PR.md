> Unsubmitted draft, last validated 2026-10-18. Recheck current upstream state,
> reproduce relevant results, and follow [the handoff checklist](README.md) before posting.

Title: fceux: use corrected 2.7.0 release

-----

- [ ] Have you followed the [guidelines for contributing](https://github.com/Homebrew/homebrew-core/blob/HEAD/CONTRIBUTING.md)?
- [ ] Have you ensured that your commits follow the [commit style guide](https://docs.brew.sh/Formula-Cookbook#commit)?
- [ ] Have you checked that there aren't other open [pull requests](https://github.com/Homebrew/homebrew-core/pulls) for the same formula update/change?
- [ ] Have you built your formula locally with `HOMEBREW_NO_INSTALL_FROM_API=1 brew install --build-from-source <formula>`?
- [ ] Is your test running fine `brew test <formula>`?
- [ ] Does your build pass `brew audit --strict <formula>` (after doing `HOMEBREW_NO_INSTALL_FROM_API=1 brew install --build-from-source <formula>`)? If this is a new formula, does it pass `brew audit --new <formula>`?

-----

- [ ] I did not use AI/LLM to create this PR, or I disclosed the tool/model below and reviewed its output; I did not attribute commits to AI and will answer maintainer questions and review comments myself without AI/LLM.

-----

Pin the corrected [2.7.0 release](https://github.com/TASEmulators/fceux/releases/tag/fceux-2.7.0)
at `8cdbeeb248f5a13aa97a58b4a0437ae13fb6aea8` instead of the original commit and
add revision 1 for rebuilt bottles. The release note says the tag "was bumped
once due to a major bug", explaining the source change without a version bump.
The existing `--help` test, bottle block and install recipe are unchanged.

The corrected source was built locally on macOS 27.0.1 ARM64. `brew lgtm` passed
the unchanged `--help` test, strict audit, style and typecheck against that
source-built keg. Linux was not tested.

AI assistance: OpenAI Codex (GPT-6) prepared the patch and ran the source build
and checks above. Claude Opus 5.5 independently reviewed and approved the reduced
pin-and-revision patch. Human contributor review and pre-submission checks remain
pending; assistant-run checks are not attributed to the contributor.
