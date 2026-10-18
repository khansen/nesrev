# Pass-cycle permissions

The tmux launcher's default `--permissions pass-cycle` previews a small local
permission profile, asks for explicit consent, and installs it before starting
agents. `--check` prints the same rules without installing them or prompting.
An unchanged profile reuses the recorded consent. Changing the project, roles,
tool paths, or generated settings requires confirmation again.

The implementer receives grants for `stage-project` and `commit-project`, which
validate explicit file paths and staged changes for the selected project,
plus `start-pass`, `reready`, `archive`, `status`, and
response publication. Both roles
receive `checkout-status` for live inspection and `find-project-symbols` for
source searches without shell loops, plus `trace-project` and `analyze-project`
for project evidence tools.
The reviewer receives `approve`, `request-changes`, `status`, and review
publication. Claude file-edit grants cover the selected
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
code. Trace drivers, analyzers and their dependencies, including tools the agent writes
during the pass, are trusted code with desktop access outside the Codex sandbox;
the grants do not constrain their effects or input/output paths. An analyzer
name does not make execution read-only. Installation,
network, direct emulator launches, builds, and other unlisted requests may still prompt.

## Commands that match the grants

Read `.agents/permissions/commands.md` and use the commands printed in the
watcher prompts. Run them separately, without output redirection, environment
assignments, or a surrounding script. In Codex, request sandbox escalation when
the protected Git or handoff state requires it; a matching allow rule handles
that escalation without another human prompt. Do not wrap the command in a
different interpreter or silently broaden the rules to address a refusal.

The launcher fixes the Python executable, handoff script, and `--repo` path in
both grants and prompts. For live branch, HEAD and working-tree inspection,
use the argument-free `checkout-status` command printed in the guide and
handoffs. It returns JSON with `root`, `branch`, `head` and `changes` (Git
porcelain-v2 records), works before review initialization, and disables Git's
optional index refresh. Detached HEAD has a null `branch`; an unborn branch
has a null `head`. The existing `status` command reports saved review state.
Direct `git branch`, `git config` and `git worktree` still prompt, including
read-only forms: a narrower allow cannot override a matching Codex prompt rule.
Use the approved inspection command from the outset; it accepts no arbitrary
Git options, paths or command suffixes.

Use native Read/Grep tools for ordinary inspection. For repeated symbol-use
searches, use the guide's `find-project-symbols <slug> <project-file> <symbol>…`
command instead of a compound shell loop. It accepts 1–64 literal whole-symbol
tokens and one explicit UTF-8 project file, prints matching lines as JSON,
and writes nothing. Paths outside the selected project, symlinks, directories,
and shell/regex expressions are refused. No matches is a successful empty
result. Other analysis commands can still require approval.

Both roles use `trace-project <slug> run_<scenario>.py -- <arguments>`
for desktop captures and `analyze-project <slug> analyze_<scenario>.py -- <arguments>`
for existing evidence analyzers. Each selects a regular, non-symlinked Python tool under
`projects/<slug>/tools/trace/`, replaces the helper process with that driver from
the repository root without a shell, and forwards arguments literally. The driver
retains the helper's PID and receives signals directly; callers observe its exit
or signal status. The first `--` separates helper arguments from driver arguments;
an additional `--` is passed to the driver. It accepts
no arbitrary interpreter or script path. Capture drivers must use the supervised
`scripts/run_fceux_trace.py` lifecycle and explicit scenario acceptance. This
helper validates dispatch, not the driver's implementation or capture evidence;
changing drivers and dependencies retain the trust described above. Codex must
request escalation on the exact printed helper command, rather than directly
launching the driver and repeatedly requesting a new prefix. Claude reviewer
settings include both grants; Codex roles share project rules as described above.
Runtime discovery remains implementer-owned; independent reviewers may replay
bounded evidence scenarios. Ad-hoc Python, shell loops, and scratch scripts
remain outside these grants. Do not relocate a refused scratch script to the
trusted tool directory to bypass approval. Reusable analyzers belong in the
project's reviewed tooling. This profile does not disable Claude's sandbox or
override restrictive user or administrator settings.

Keep commands that may prompt separate from routine reads. If a supported form
still prompts, record the exact command, loaded permission mode and observed
intervention. Do not treat an escalation request as proof that a human approved.
Report unknown when the harness does not expose whether a human approved.
Do not switch permission modes to make a scoped smoke test pass.

The implementer writes a commit message with a normal
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

<a id="live-permission-smoke"></a>
## Live permission smoke test

After a permission change, use fresh agents and a known, bounded capture
scenario before authorizing another batch. The launcher can run only these
probes, without selecting a pass or starting either handoff watcher:

```sh
python3 scripts/agent_review_tmux.py --project my_game --smoke-only /tmp/smoke.json
```

The specification names existing source and trace inputs; it does not contain
arbitrary shell commands. For example, adapt these names to the project:

```json
{
  "inspection": {
    "path": "projects/my_game/asm/my_game.asm",
    "symbols": ["UpdateActors", "SpawnProjectile"]
  },
  "trace": {
    "driver": "run_actor_scene.py",
    "arguments": ["--scenario", "known-room"]
  }
}
```

Prepare any listing/xref inputs required by that driver first. `--check` with
the same specification validates setup without launching agents or captures.
The smoke mode requires `pass-cycle`, refuses to reconnect to an existing
session, and keeps saved review state unchanged. Smoke sessions are tagged with
`@nesrev_review_smoke=1`; a normal launch refuses to reconnect to them and prints
the command to stop the session first. After both agents say READY,
confirm readiness in the startup pane. Both inspect the checkout; by default
the reviewer runs the symbol search twice and the implementer runs the real
capture twice to exercise grant reuse. Help/version output cannot substitute
for a capture.
Each agent reports commands, exits, evidence paths, mode and interventions,
then stops. The launcher does not automatically certify success or release a
pass; the operator checks those results against the session/tool logs.

To exercise the reviewer path, add `"trace_role": "reviewer"` and an optional
`"analysis"` object with `"driver": "analyze_actor_scene.py"` and an `"arguments"`
array naming an existing capture and scratch output. The selected trace role
runs analysis then capture, twice in order; the other role runs only source
searches. This avoids competing emulator launches between roles. The default
trace role remains implementer for older specifications. Analyzer help/version
output is refused, just like capture help. Stop on the first failed command
or scenario. A trace driver that only checks supervisor completion needs a
scenario-validation wrapper before use here: it must reject missing gameplay
evidence and report the new capture's semantic acceptance. Reanalyzing an old
capture does not validate the new replay.

Acceptance requires both captures' scenario checks, both analyses when supplied,
and both source searches
to succeed under the intended unchanged modes, without manual per-command
approval. Setup trust/consent is separate. Preserve any failure or intervention
as evidence; a mode change invalidates the unattended result. Stop this smoke
session before launching the next separately authorized semantic task.
Compare every executed command with the generated standalone command, including
the interpreter, helper path, project and arguments. Existing broad grants may
allow a different spelling without a prompt; that does not validate this profile.
An approval log that says only `rule` cannot identify which rule matched.
Record emulator startup stalls separately from permission decisions: a capture
timeout after Lua initialization with no frame advancement is an emulator stall,
not evidence of a permission refusal. Preserve it and stop the smoke for assessment.
Smoke sessions created before this marker was introduced must also be stopped;
the launcher cannot identify those untagged sessions as smoke-only.

<a id="recovery-and-custom-setups"></a>
## Recovery and custom setups

`--permissions bypass` explicitly selects native bypass for both roles:
Codex gets `--dangerously-bypass-approvals-and-sandbox`; Claude gets
`--dangerously-skip-permissions`. This is broad execution access, not the scoped
profile. No profile consent is requested and no managed permission files are
created, removed, or rewritten. `--check` prints the selected native commands.
Model/effort options remain independent. Other native options, including
competing permission modes, require `--permissions inherit`; unknown agents
are refused rather than assigned a guessed bypass flag.

Bypass prompts use the current project's handoff and staging/commit helpers,
not a possibly stale saved command guide.
Every bypass watcher delivery appends the current permission instructions,
explicitly overriding saved guide directions in pending older handoffs. The
original prompt and review state are preserved; a missing context file blocks
delivery rather than silently falling back to the old directions.

Review ownership, verification, the startup reference choice, and the no-push
rule still apply. Authentication, trust, administrator restrictions, usage
limits, and missing evidence can still block work; bypass is not an
unattended-completion guarantee. Reconnecting keeps the running mode; restart
to change it.

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
