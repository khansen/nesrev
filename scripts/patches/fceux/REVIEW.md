# External review: optional FCEUX maintenance

Review the full PR against base commit
`d2ae27a539329e39979dab93ad9c56788d118bd8`, including all commits on
`docs/fceux-local-maintenance`. Record the exact reviewed head in your verdict.
Use a fresh clone or disposable checkout. The review must be possible using
tracked files and public upstream source; no maintainer installation, private
project corpus or conversation history is required.

The intended result is an optional, reproducible FCEUX workaround, with enough
material to submit the separate upstream changes later and a procedure to
retire the workaround when a standard release meets the needed behavior.

Start with these files:

- [LOCAL_BUILD.md](LOCAL_BUILD.md): selection, build/setup, acceptance and retirement.
- [activate.sh](activate.sh), [tmux-local-fceux](tmux-local-fceux) and
  [test_profile.py](test_profile.py): profile behavior and portable tests.
- [Evidence index](evidence/README.md): provenance, full combined-build logs,
  synthetic cold-start results, controls and reproduction commands.
- [Upstream handoff](upstream/README.md): approved patch bytes, submission
  drafts, source bases and the sanitized startup-race attachment bundle.

Inspect the whole diff and focus on:

1. **Optional setup and portability.** Normal FCEUX lookup and static work must
   remain unaffected. Check that a fresh clone can follow the setup recipe using
   public source and tracked inputs, without an existing local release.
   Check the playbooks' [recovery routing](../../../agent_playbook/RUNTIME_EVIDENCE.md#fceux-recovery):
   matching symptoms should favor a validated replacement without claiming
   every timeout has the same cause or making the custom build mandatory.
2. **Activation and tmux.** Missing or altered release files must block a
   dependent launch, including missing config directories and checksum lists
   omitting either executable. Switching `current` after activation must leave
   the selected binary, Lua path and adapter pinned to the checked release.
   Check exact environment forwarding into initial, split and respawned panes
   and new windows on an already-running private server, including spaces and
   trailing semicolons. Verify the negative controls fail for the intended reasons.
3. **Evidence and limits.** Check source pins, patch/source/artifact hashes,
   config-reset ordering and test claims. Distinguish the older frame-zero fix,
   the corrected release's frame-one race, and retained shutdown failures.
   Neither maximum-speed startup checks nor historical approvals establish
   normal-speed/audio quality, gameplay semantics or portability to other systems.
4. **Future contributions.** Can another contributor reproduce the config test,
   review the formula-only change and report the startup race from this clone?
   Check experiment/build attribution, preserved patch hashes, disclosure and
   the distinction between recorded observations and inferred explanations.
5. **Retirement.** The procedure should permit adopting a suitable standard
   release even if these patches are never submitted, and require reassessment
   rather than retaining the old source pin indefinitely.
6. **Self-contained material.** Check new documentation links, manifests and
   compressed attachments. Evidence labels must not be prerequisites pointing
   at another person's machine. Verify every shipped checksum.

Run the portable checks documented in the evidence index. Use disposable copies
for mutations and standalone config tests. The optional tmux test creates and
stops its own server; it must not touch user sessions. Do not change installed
profiles, emulator binaries, Homebrew state or personal configuration. Do not
start project agents, run live emulator captures, commit, push, merge or submit
anything upstream as part of this review. Report checks requiring further
authorization as skipped, without treating historical logs as your own reruns.

Return findings ordered by severity with file/line references and concrete
reproductions, an explicit APPROVED or CHANGES_REQUESTED verdict, and a clear
split between checks rerun, evidence inspected and checks skipped. State any
side effects. Optional improvements should be separated from blockers.
