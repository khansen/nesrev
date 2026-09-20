# Pass-cycle permissions

The tmux launcher's default `--permissions pass-cycle` previews a small local
permission profile, asks for explicit consent, and installs it before starting
agents. `--check` prints the same rules without installing them or prompting.
An unchanged profile reuses the recorded consent. Changing the project, roles,
tool paths, or generated settings requires confirmation again.

The implementer receives grants for `stage-project` and `commit-project`, which
validate explicit file paths and staged changes for the selected project,
plus `start-pass`, `reready`, `archive`, `status`, and
response publication. The reviewer receives `approve`, `request-changes`,
`status`, and review publication. Claude file-edit grants cover the selected
project for the implementer and only its `tmp` directory for the reviewer.
Codex keeps `workspace-write`, `on-request`, and human approval review; Claude
uses its normal manual permission mode. Neither receives a blanket Git, Python,
shell, or make grant. Omitted model and effort options remain omitted.

The local files are ignored by Git, including in older project checkouts:

| File | Purpose |
|---|---|
| `.codex/rules/nesrev-pass-cycle.rules` | Grants for the roles running Codex |
| `.agents/permissions/implementer.json` | Claude implementer settings, when selected |
| `.agents/permissions/reviewer.json` | Claude reviewer settings, when selected |
| `.agents/permissions/commands.md` | Exact command forms for this checkout |
| `.agents/permissions/receipt.json` | Consent and hashes of managed files |

Codex loads project rules at startup after workspace trust. **Both Codex agents
share those project rules**; role ownership is enforced by the handoff protocol
and review instructions, not a filesystem boundary. Other Codex sessions in this
checkout can also use the installed rules. Claude receives its role's settings
through `--settings`. These behaviors follow the native
[Codex rules](https://developers.openai.com/codex/rules) and
[Claude permissions](https://code.claude.com/docs/en/permissions) mechanisms.

Existing user, project, and administrator settings still apply. Broad grants
already present are not revoked, and restrictive policies may still require
approval or refuse an operation. The generated rules block direct `git push`
and `git -C <checkout> push`; matching raw add, commit, reset, restore, checkout,
switch, rebase, merge, clean, config, worktree, and branch commands require approval. These
patterns do not cover every equivalent Git invocation or indirect script.
Never push `projects`, regardless of available permissions. This profile trusts
the named handoff script, repository code it invokes, and Git hooks; it is a
convenience configuration for cooperating agents, not containment for hostile
code. Installation, network, emulator, build, and other requests may still prompt.

## Commands that match the grants

Read `.agents/permissions/commands.md` and use the commands printed in the
watcher prompts. Run them separately, without output redirection, environment
assignments, or a surrounding script. In Codex, request sandbox escalation when
the protected Git or handoff state requires it; a matching allow rule handles
that escalation without another human prompt. Do not wrap the command in a
different interpreter or silently broaden the rules to address a refusal.

The launcher fixes the Python executable, handoff script, and `--repo` path in
both grants and prompts. The implementer writes a commit message with a normal
file-edit tool to `projects/<slug>/tmp/commit-message.txt`, then uses the printed
`stage-project <slug> -- <file> <file>` and `commit-project <slug>` commands.
Staging validates the whole list before invoking Git with literal pathspecs.
It accepts existing files and exact tracked deletions under `projects/<slug>/`;
directories, globs, pathspec magic, outside paths, and symlinks are refused.
List both the old and new filenames to stage a rename. Commit checks every
staged path belongs to the selected project, reads the fixed message file, and
accepts no extra paths or Git options. Pre-existing unrelated staged changes
block the commit and remain untouched. These commands cannot establish whether
an agent actually reviewed the specified files; that remains its responsibility.

Raw Git staging and commit commands have no generated allow grant. The generated
prompt rules cover their direct and checkout-scoped forms. Upgrading an older
profile replaces its managed raw-Git grants after fresh consent; stop and restart
agents so they load the new rules. Independently configured user grants remain.

All reviewer scratch files belong in `projects/<slug>/tmp/`: review drafts,
extracts, notes, and temporary scripts. This reviewer-specific rule takes
precedence over the general implementation-helper path `tmp/projects/<slug>/`;
OS temporary directories and agent-global scratchpads are outside these grants.
Read/search original packets and source directly when possible. Create or update
scratch files with native file-writing/editing tools from the outset.
File-edit grants do not authorize shell writes: redirection (`>`), `mkdir`,
`cp`, and `mv` may still prompt even inside the permitted directory. Request
approval for necessary shell operations; do not broaden permissions or switch
tools to evade a refusal.

Reviewers publish their draft Markdown through the handoff tool. The generated
`import-artifact --kind review --source <draft>` command copies it into the
current review round, then `approve` or `request-changes` records the verdict.
Implementer responses use `--kind response` before `reready`. Import rejects
the wrong turn, sources outside project scratch space, empty/non-Markdown
files, and destination symlinks. A draft can replace its current-round copy
while that role still owns the turn. Verdict and archive checks are unchanged.

## Recovery and custom setups

If a routine command still prompts, compare it with the generated guide and
check workspace trust and the agent's loaded permissions. Do not allow a
generic interpreter, `env`, shell, or all Git commands just to silence it.
Claude's `/permissions` lists its loaded rules. Codex's `execpolicy check`
can test an exact argument list against specified rule files; it is not an
audit of every loaded setting or of scripts' behavior.

The launcher refuses to overwrite unowned or edited permission files and rejects
symlinked permission paths. Inspect and move the conflicting file aside, then
rerun setup and review the new preview. A partially failed installation can
need the same cleanup; it does not start agents. No global files are changed.

`--permissions inherit` skips profile management and supports custom wrappers
and native options beyond model/effort selection. It leaves existing rules
intact, including a previously installed pass-cycle profile. To remove that
profile, stop its agents and remove only the files listed above; then launch
with `--permissions inherit`. Keep unrelated `.codex` and `.agents` content.
Changing settings or relaunching does not update a running matching tmux
session: reconnect preserves its agents. Use the README's restart procedure
at a safe handoff point. A trust prompt or organizational policy is never
automatically bypassed by the launcher.
