# Agent Session Operations

The review lifecycle lives in [TOOLING.md](TOOLING.md#agent-review-handoff).
These procedures cover coordinator evidence and authorized continuation of a
bounded task. They do not grant permission for further game passes.

<a id="coordinator-observations"></a>
## Preserve observed friction

Before archiving, reconcile agent reports with available session evidence.
Launcher configuration describes requested permissions; it does not establish
the effective mode throughout the run. Record an observed prompt or mode change
even if the final report says no intervention occurred. If the approver or the
cause of a mode change is unknown, say so. Absence of captured evidence does not
prove uninterrupted unattended operation.

Write a dated Markdown observation under `projects/<slug>/tmp/`. Identify the
run, role, relevant command or short terminal excerpt, what it proves, and what
remains unknown. Preserve bounded evidence before scrollback expires; omit
secrets and unrelated session content. For example:

```markdown
Observed: 2026-10-27, reviewer, demo-pass-2.
Evidence: the terminal displayed a permission prompt for a CSV inspection.
Later evidence: the reviewer displayed Auto mode.
Limit: who approved the command or changed modes was not captured.
The report's claim of no mode change is not supported by these observations.

## Learning Candidates
_None._
```

Import it before archiving, using the current run ID from `status`:

```sh
python3 scripts/agent_review.py import-artifact --kind observation \
  --run-id <current-run-id> --source projects/<slug>/tmp/observation.md
```

This coordinator command requires a matching run ID and a Markdown source in
the current project's tmp directory. It changes no state, round, ownership, or
verdict. Import observations one at a time per run. New files use
`observation-<sequence>-<sha256>.md`; archives and learning candidates preserve
that numeric import order. Reimporting identical content reuses the existing
artifact; changed content creates another without overwriting or moving the
earlier observation. Include a date and correction reference when supplementing
a previous note. Legacy hash-only notes retain filename order before sequenced
notes; their original import order cannot be reconstructed from those names.

The complete observation appears in the review archive even when its
`## Learning Candidates` is `_None._`. Only unresolved process candidates belong
in that section; the normal [friction lifecycle](PROCESS_FRICTION.md) applies.
Observation import preserves evidence but does not certify its truth or detect
contradictory prose automatically. No new agent permission grants accompany it.

For an already committed archive, append a dated amendment under the
[historical-record contract](DOCUMENTATION.md#historical-records). Do not
regenerate it to erase the original report. Newly generated prompts list existing
observation files explicitly, with no observation instruction when none exist.
Saved handoff prompts remain frozen; explicitly point an already-running agent
to observations imported after its prompt was generated.

<a id="continue-agent-pair"></a>
## Continue with the same pair

Reuse the pair when the user authorizes another pass on the same project and
the agents retain useful context. Restart when changing startup settings or
when session health requires it. A fresh context is optional, not a pass boundary.

1. Confirm both agents are idle, the prior run is `APPROVED`, and its archive is
   committed. Finish pending handoffs before changing the task. Approval alone
   does not authorize another pass beyond the user's limit.
2. Locate the active `workspace.json` from the watcher pane commands:
   `tmux list-panes -s -t <session> -F '#{pane_id} #{pane_start_command}'`.
   Read its repository root and role-to-pane mapping. The shared `task.md` is
   beside it. Confirm these are the intended live agent panes, not shell prompts.
3. Preserve a copy of the previous task, then update `task.md` with the new
   corridor, pass limit, references, and stopping condition. Keep its common
   handoff instructions. Leave previous archives and `current.json` intact.
4. Write a short `reviewer-next.md` beside the task directing the reviewer to
   read the updated task, acknowledge `READY`, and await the next committed
   handoff. Deliver it with the notifier below. Wait for that acknowledgement.
5. Deliver the updated task to the implementer. Confirm it starts the intended
   pass and stops at the new limit. Existing watchers continue handling verdict
   transitions; no manual state rewrite or permission change is needed.

Replace the example pane IDs and workspace path with values from that session.
Run from its repository root. First notify the reviewer:

```sh
env AGENT_REVIEW_TMUX_REVIEWER=%21 scripts/agent_review_tmux_notify.sh \
  reviewer TASK_UPDATED .agents/logs/<workspace>/reviewer-next.md
```

After the reviewer acknowledges, notify the implementer:

```sh
env AGENT_REVIEW_TMUX_IMPLEMENTER=%20 scripts/agent_review_tmux_notify.sh \
  implementer IMPLEMENTING .agents/logs/<workspace>/task.md
```

These status words label notifications; they do not alter review state. Running
the launcher again with a new `--task` only reconnects and does not perform this
update. Never paste a continuation into a busy agent or an unverified pane.
