# Local Agent Review Handoff Protocol - Specification

Status: implemented v1 design record. This document records the context,
protocol boundary, implementation decisions, empirical defects, and remaining
open questions for local project-pass review handoff. If it disagrees with
[AGENTS.md](AGENTS.md) or a playbook, the playbook wins.

The motivating first deployment is Codex as implementation agent and Claude
Code as reviewer, but the protocol should be role-based. Codex-to-Codex,
Claude-to-Codex, Claude-to-Claude, or another local agent pairing should work
as long as one participant owns implementation and the other owns review for a
given run.

The build path was taken after packet, state-machine, durability, and tmux
handoff trials showed the needed v1 surface was small and repo-local. No
third-party coordinator was adopted for v1, and the earlier prior-art spike is
now optional future comparison rather than a prerequisite. The implementation
stays deliberately boring: Git remains the source of truth for code and
commits, `.agents/` stores ignored runtime state, durable review judgements
and learning candidates are committed under the reviewed project, and a small
worker/notifier loop coordinates two already-running local agent sessions. The
user may start the sessions and worker loops manually; v1 automates post-pass
handoff, not login or session startup. Do not introduce MCP or a custom service
in v1 unless the file/state approach fails a concrete requirement.

## 1. Context

The current process has materially improved active-project pass quality:

- proof-debt signals moved work from generic corridors toward identity passes
- crosswalk mappings and semantic claims started moving after many flat passes
- deferrals are now captured, closed, and capable of firing repeat signals
- process hardening caught false-cleanliness bugs in gates and pass artifacts
- reviewer feedback turned an operator workflow miss into a playbook fix

The remaining weakness is not lack of local rules. It is that a single
implementation agent can follow locally plausible paths for many passes before
an outside reviewer notices the aggregate drift. The review of a large
semantic-pass batch demonstrated that "human self-review" by the operator is
necessary but not sufficient for unattended or high-scrutiny runs: the operator
is optimized to finish the pass, while the reviewer is optimized to attack the
evidence and process claims.

External adversarial review is therefore an opt-in layer over ordinary solo
closeout, and it has become the chosen workflow for the current automated-pass
trial. Without the handoff helper, that layer is manual:

- the user asks a reviewer agent to review a commit or branch
- the user copies the reviewer findings back into the implementation agent
- the implementation agent fixes or explains
- the user repeats the cycle

That works, but feedback comes late and the user becomes the message bus. The
goal is quicker feedback after each pass or small batch, without weakening the
Git-centered workflow.

## 2. Design Goals

Required properties:

- **Git is authoritative.** The reviewed code state is identified by a local
  Git commit range, usually one committed semantic pass. The working tree is
  not the source of truth.
- **Review is not diff-only.** Every pass review inspects the commit range
  plus the project's aggregate signals, so slow drift is visible before a large
  retrospective batch review.
- **Scope is narrow.** This protocol covers semantic project-pass review.
  Process, tooling, and playbook changes use ordinary branch/PR-style review
  outside this protocol.
- **One agent owns implementation.** The implementation agent makes code/doc
  changes and commits them.
- **One agent reviews adversarially.** The reviewer agent prioritizes bugs,
  false claims, missing verification, process drift, and weak evidence.
- **The pairing is configurable.** The first profile can be Codex implementer
  plus Claude reviewer, but role names must drive the protocol.
- **State is observable.** A human can inspect `.agents/` and Git history to
  see whose turn it is, what was reviewed, and why the loop stopped.
- **The loop terminates.** The protocol reaches `APPROVED` or stops after a
  configurable maximum number of review rounds.
- **No hidden service.** v1 uses files plus local Unix tooling. A manually
  started worker loop, tmux hook, or other simple notifier can prompt the next
  actor when state changes, but state files remain authoritative.
- **No MCP in v1.** File handoff and Git ranges are enough until proven
  otherwise.

Non-goals for v1:

- automatic semantic judgment
- automatic merge or push
- remote CI orchestration
- starting, logging in, or supervising agent sessions
- replacing `project-pass-closeout`, `project-verify`, or existing gates
- letting the reviewer mutate implementation files in the normal path
- building a long-running daemon or database-backed service

## 3. Scope and Rejected Ranges

Use this protocol when a committed semantic disassembly pass is selected for
external/adversarial review. A sole implementer may still complete a pass
through normal self-review, closeout, gates, and commit without invoking this
protocol.

- The reviewed unit is a local `base..head` commit range, usually one pass
  commit.
- PR, branch, merge, or remote-review lifecycles are not a fit unless the tool
  can be driven directly by arbitrary local refs or SHAs.
- The reviewer is read-only over implementation files. The reviewer may run
  checks, inspect generated artifacts, read aggregate project signals, and
  challenge evidence, but should not mutation-test semantic edits by changing
  project files.
- Every review under this protocol consumes a compliant project-pass review
  packet, including the Required Contents in
  [`PROJECT_PASS_REVIEW_PACKET_SPEC.md`](PROJECT_PASS_REVIEW_PACKET_SPEC.md).
  The reviewer may inspect the repository directly when the packet raises a
  question or omits needed context.
- Review rounds should stay small. A default absolute cap of 3 is appropriate
  unless a human explicitly raises it for a specific pass. This is an
  assumption to measure during the trial, not a proven property.

Rejected ranges:

- If the range touches `scripts/`, `tests/`, `agent_playbook/`, `AGENTS.md`,
  `Makefile`, root process/spec files such as `*_SPEC.md`, `.agents/`, or
  shared project wrapper/tooling files, reject it from this protocol and use
  ordinary process review.
- If the range mixes project-pass files with process/tooling files, split the
  work before review. A human override may force project-pass treatment only
  when the process-looking path is demonstrably project-local data, not a
  shared gate, wrapper, playbook, or test.
- Reviewer mutation testing belongs to process review, not project-pass
  review. A project-pass reviewer should verify read-only by rerunning gates
  and inspecting evidence, not by changing project files.

## 4. Implementation Record and Prior-Art Status

The v1 interactive-session decision is settled: the target is coordination
between already-running implementation and reviewer sessions. The protocol does
not automate session startup; the user can start both sessions and worker loops
manually. It moves state, packets, prompts, review artifact paths, and verdicts
between running agents after each pass so the user stops serving as the message
bus.

In this spec, coordinator means the local state/notification helper that moves
the next prompt, packet path, review artifact path, and verdict between already
running agents. It is not the reviewer, and it does not decide whether a pass is
correct.

The project-pass review packet contract lives in
[`PROJECT_PASS_REVIEW_PACKET_SPEC.md`](PROJECT_PASS_REVIEW_PACKET_SPEC.md).
That packet is the executable form of the protocol-required review evidence. It
is useful manually and remains orthogonal to coordination: the coordinator may
run the packet generator, but it must not decide whether the pass is correct.

Implemented v1 pieces:

- `scripts/project_pass_review_packet.sh` and
  `make project-pass-review-packet` generate the review packet.
- `scripts/agent_review.py` implements the file-backed state machine,
  one-command pass handoff, packet validation, review/rereview transitions,
  watcher contract, and durable review archive command.
- `scripts/agent_review_tmux_notify.sh` implements the v1 tmux notifier for
  already-running, bracketed-paste-aware agent panes.
- `agent_playbook/TOOLING.md` documents the operational flow.
- Durable review judgements are committed under
  `projects/<slug>/docs/reverse_engineering/reviews/pass-<id>.md`; packets,
  prompts, `.seen` markers, and `current.json` stay ignored under `.agents/`.

The local build path was chosen before a full third-party prior-art spike. The
reason is empirical, not theoretical: the smallest useful implementation was
four repo-local components that had to understand this repo's packet contract,
project-pass path boundary, archived-review placement, and tmux handoff
preconditions. Those requirements became concrete through local trials faster
than a generic coordinator comparison would have. Prior-art inspection remains
useful future work, but it is no longer a prerequisite for v1.

Candidate tools that may still be useful as comparison paths:

- built-in review commands from locally installed agent CLIs, for example
  Claude Code `/code-review`; useful as reviewer-engine comparisons, not a
  complete running-session coordinator by themselves.
- `orchestra` - a generic Codex/Claude orchestrator with writer/reviewer
  review loops; compare if noninteractive review becomes acceptable.
- `agentmux` - a tmux-oriented coordinator for long-running Codex and Claude
  sessions; compare if the local tmux notifier proves too small.
- `codex-review` - a Claude Code plugin with persisted review rounds and
  Codex as reviewer.
- `codex-plugin-cc` - an OpenAI Claude Code plugin exposing Codex review
  commands.
- `codex-claude-companion` - Codex-side Claude review integration.
- `multiagents` - a broader MCP/broker-style multi-agent runtime; likely too
  heavy for v1, but useful as a contrast case.

Built-in code-review commands may be useful as reviewer engines inside a
wrapper, but they are not sufficient as complete coordinators unless they can
consume a compliant project-pass review packet and produce the required
`APPROVED`/`CHANGES_REQUESTED` artifact contract.

Criteria used to judge either the local implementation or a future external
replacement:

- It works on an arbitrary Git worktree and does not require repo-specific
  code.
- It supports configurable roles: implementation agent and reviewer agent.
- It can run with Codex reviewing Claude, Claude reviewing Codex,
  Codex-to-Codex, or other pairings when the CLIs exist locally.
- It keeps implementation changes owned by the implementation agent.
- It gives the reviewer a read-only or review-only path by default.
- It persists structured findings or review artifacts on disk.
- It has an observable state model and logs that a human can inspect.
- It terminates at approval or after a configurable maximum review round
  count.
- After the user manually starts the sessions and worker loops, it can hand a
  ready pass to the reviewer and return findings to the implementer without
  human copy/paste. Any form that requires a human to trigger each review round
  must be evaluated separately and cannot satisfy unattended pass review.
- It has a preflight for the chosen transport: required local agent CLIs when
  used, visible session or worker-loop handles, authentication when a one-shot
  CLI is part of the path, and writable state/log locations before a batch
  starts. Missing reviewer session, worker loop, or auth is a setup failure,
  not a review result.
- It can pass through this repo's existing instructions and verification
  commands without hiding exact command output or exit codes.
- It treats a local Git commit range as the reviewed unit. PR or branch review
  support is not sufficient unless the tool can be driven with arbitrary local
  refs or SHAs such as `<previous-approved-head>..<new-pass-commit>`.
- It can expose aggregate project state to the reviewer, either directly or
  through a wrapper that runs the repository's pass-summary commands.
- It can expose baseline and allowlist diffs, and can rerun the gates those
  ledgers affect.
- It can expose the complete reviewed range, not only a selected pass summary,
  and can label verification evidence with the exact SHA it describes.
- It keeps the reviewer read-only over implementation files.
- It can operate without creating, merging, or pushing review branches.
- It does not require MCP, a custom network service, or a heavyweight daemon
  for the first deployment.
- It does not auto-commit, auto-push, auto-merge, or invoke remote CI as part
  of the local review loop.
- Its install source and version can be pinned, vendored, or otherwise made
  auditable.
- Any network access and credential use are explicit, limited to the configured
  agent CLIs unless approved, and visible in logs or invocation wrappers.

Future adopt/wrap/fork/build outcomes:

- **Adopt** when an existing tool satisfies the acceptance criteria with
  configuration only.
- **Wrap** when a tool satisfies the core loop but needs a thin repo-local
  transport wrapper or prompt adapter.
- **Fork or patch upstream** when the missing behavior is generic and small.
- **Build locally** was the v1 outcome. Revisit only if a future external tool
  can replace the local pieces without losing packet fidelity, durable archive
  placement, or already-running-session handoff.

Packet and coordinator trials established different facts. Packet trials
validated the reviewer-engine side: the reviewer could consume the range,
aggregate context, gate evidence, and a known-bad case. State-machine and tmux
trials validated the coordinator side: turn-taking, fix handoff, re-review,
round counting, termination, archive durability, and notification delivery.

Empirical defects found during those trials are part of the design record:

- a packet omitted one commit in the reviewed range
- gate evidence in an early packet described the pre-injection SHA, not the
  review head
- a known-bad phantom rename was findable from a packet, and a clean packet was
  approved
- whole-ledger rename validation produced historical noise; range-scoped
  reconciliation was the useful packet signal
- review SHAs were orphaned by routine project rebases
- packet generation in a fresh worktree failed because the untracked reference
  ROM was absent; `ready`/`reready` now reject packets whose verify gate is
  missing or nonzero
- `.agents/` was visible when the review head predated the tracked ignore
  rules; `init` writes runtime-state patterns to `.git/info/exclude`
- review prompts initially assumed `scripts/agent_review.py` existed at the
  review head; prompts now use the actual invocation path when needed
- `reready` initially accepted stale packets and process-path drift; it now
  validates packet head and project-pass path boundaries for the advanced
  range
- review archives could initially escape the repo through unsafe project or
  `--out` paths; archive output is now slug-validated and repo-contained
- tmux prompts initially submitted multi-line text line-by-line; the adapter
  now uses bracketed paste
- a stale tmux pane initially leaked prompt buffers; target preflight and
  cleanup now cover the failure path

## 5. Implemented State Model

Store runtime protocol state under `.agents/`. The directory is the handoff
workspace, not a source-code workspace, and v1 keeps it ignored. `init` also
writes the runtime-state patterns to `.git/info/exclude` so detached project
history checkouts that predate the tracked ignore rules do not expose `.agents/`
as untracked noise.

Ignored runtime files include:

- `.agents/current.json`
- `.agents/runs/`
- `.agents/logs/`

The runtime files should be easy to delete and recreate. They should not be
required to reproduce the codebase; Git history and committed project artifacts
remain canonical.

Durable review judgements are not stored under `.agents/`. After approval,
`archive --pass-id <id>` writes the review and response history to
`projects/<slug>/docs/reverse_engineering/reviews/pass-<id>.md`, keyed by pass
id rather than SHA so routine project rebases do not orphan the record. The
archive still records review-time SHAs as provenance, but labels them as
review-time identifiers that may become unreachable after a rebase.
Non-empty `## Learning Candidates` sections from the implementation note,
review artifacts, and response artifacts are copied to
`projects/<slug>/PROCESS_FRICTION.md` as raw process-learning candidates for
later triage. `_None._` is the explicit no-op marker. Promotion from that queue
to playbooks or scripts uses process review, not the project-pass review round.

V1 did not add tracked `.agents/` role files. Agent-facing workflow
instructions live in `agent_playbook/TOOLING.md`; the generated prompt files in
`.agents/runs/<run_id>/prompts/` carry the per-turn instructions.

### 5.1 State File

`.agents/current.json` is the single current-turn pointer.

```json
{
  "protocol_version": 1,
  "status": "IMPLEMENTING",
  "project": "<slug>",
  "branch": "projects",
  "review_base": "08420109e",
  "review_head": "6595c8869",
  "implementation_commit": "6595c8869",
  "round": 1,
  "max_rounds": 3,
  "review_agent": "claude",
  "implementation_agent": "codex",
  "run_id": "2026-08-23-<slug>-pass-104",
  "packet": null,
  "implementation_note": null,
  "last_review": ".agents/runs/2026-08-23-<slug>-pass-104/review-01.md",
  "last_response": null,
  "prompts": {},
  "allow_unresolved_lxxxx": false
}
```

Required fields:

- `status`: one of the states below
- `project`: validated project slug
- `branch`: branch being reviewed
- `review_base`: first commit excluded from the review range
- `review_head`: commit included at the end of the review range
- `round`: current review round, starting at 1
- `max_rounds`: absolute loop guard; default 3 for project-pass review
- `run_id`: filesystem-safe directory name under `.agents/runs/`

Optional fields may record pass id, checks, or session endpoint ids.
`allow_unresolved_lxxxx` records that generated packets should use relaxed
semantic-pass verification; it can be set at `init` or inferred after a
generated strict packet fails on expected unresolved `LXXXX` labels.
Transport-specific session handles are optional hints, not authoritative state.

### 5.2 States

Core states:

- `IMPLEMENTING` - the implementation agent is making changes. The reviewer
  should not review yet.
- `READY_FOR_REVIEW` - the implementation agent has committed an
  implementation unit and written the handoff note.
- `CHANGES_REQUESTED` - the reviewer found actionable issues.
- `READY_FOR_REREVIEW` - the implementation agent committed fixes or a written
  response classifying each finding as fixed, disputed, or intentionally
  deferred for human decision.
- `APPROVED` - the reviewer found no blocking issues for the reviewed range.

Terminal failure state:

- `REVIEW_ROUNDS_EXHAUSTED` - `round > max_rounds` or the next requested
  transition would exceed the configured cap. A human must decide whether to
  continue, override, split scope, or abandon the batch.

Allowed transitions:

```text
IMPLEMENTING          -> READY_FOR_REVIEW
READY_FOR_REVIEW      -> APPROVED
READY_FOR_REVIEW      -> CHANGES_REQUESTED
CHANGES_REQUESTED     -> READY_FOR_REREVIEW
READY_FOR_REREVIEW    -> APPROVED
READY_FOR_REREVIEW    -> CHANGES_REQUESTED
CHANGES_REQUESTED     -> REVIEW_ROUNDS_EXHAUSTED
READY_FOR_REREVIEW    -> REVIEW_ROUNDS_EXHAUSTED
APPROVED              -> IMPLEMENTING          (new run, round reset)
```

The next semantic pass must not start unless status is `APPROVED` or a human
records an explicit override outside v1. `APPROVED` and
`REVIEW_ROUNDS_EXHAUSTED` are terminal for the current review run, not for the
overall protocol.

## 6. Review Unit

The normal diff unit is one committed semantic pass:

```text
review range = <previous approved head>..<new pass commit>
```

The normal review unit is broader than that diff. Each review must inspect a
compliant project-pass review packet, including the Required Contents in
[`PROJECT_PASS_REVIEW_PACKET_SPEC.md`](PROJECT_PASS_REVIEW_PACKET_SPEC.md),
and judge whether the pass moves the aggregate story forward or only remains
locally defensible.

This prevents the failure mode where many individually reasonable passes
accumulate into visible drift that no one pass reveals alone.

For unattended or long-running project-pass batches, add a periodic cumulative
review unit:

```text
cumulative review range = <last aggregate review head>..<current head>
```

The cadence is an open tuning decision, but the protocol must support it.
External tools that can review one diff but cannot expose aggregate project
state should be wrapped or rejected for this use case.

For a re-review:

```text
review range = <original review_base>..<latest fix commit>
```

The reviewer should review the whole cumulative range during re-review, not
only the last fix commit. That prevents a fix from obscuring an earlier
unresolved finding.

The implementation note should include:

- path to a compliant project-pass review packet, or the packet contents inline
  when no separate file is used
- branch and commit range, matching the packet
- pass id or task objective
- files intentionally changed
- known advisory warnings
- any process friction recorded
- process, harness, or tooling learning candidates, or `_None._`
- any explicit non-goals or deferred work

The review output should include:

- verdict: `APPROVED` or `CHANGES_REQUESTED`
- findings ordered by severity
- stable finding IDs and severity for every blocking finding
- file/line references or commit/range references
- verification gaps or false-green concerns
- process issues
- process, harness, or tooling learning candidates, or `_None._`
- aggregate drift or proof-debt concerns
- baseline or allowlist delta concerns
- questions that block approval, if any
- non-blocking observations separated from findings

## 7. Implemented Commands

The local implementation adds one small script:

```sh
python3 scripts/agent_review.py <subcommand> [options]
```

Implemented subcommands:

- `start-pass` - normal post-commit handoff entry point: infer the default
  `HEAD~2..HEAD` range for pass 0 or `HEAD~1..HEAD` for later passes, create
  the implementation note, initialize state, generate and validate the packet,
  write the reviewer prompt, and print status. It accepts optional
  learning-candidate text for the generated note.
- `init` - create `.agents/current.json` and `.agents/runs/<run_id>/`
  for the current branch and commit range.
- `ready` - validate clean committed state, write/update the implementation
  note, optionally generate and validate a packet, and set
  `READY_FOR_REVIEW`.
- `request-changes` - validate a review file, set `CHANGES_REQUESTED`, and
  point the implementation agent at the next prompt.
- `approve` - validate a review file, set `APPROVED`, and notify the
  implementation agent through state.
- `archive` - after approval, write durable review and response artifacts to
  the project docs tree, keyed by project/pass id while preserving review-time
  SHAs as non-durable provenance. It also copies non-empty learning candidates
  to the project's process-friction queue.
- `reready` - after the implementation agent fixes or responds, bump the
  round, set `READY_FOR_REREVIEW`, optionally regenerate and validate the
  packet, and point the reviewer at the next prompt.
- `status` - print state, commit range, last artifacts, and next actor.
- `watch` - optional polling loop for manually started agents or humans; not
  required for correctness.

The script should reject:

- unknown states
- invalid transitions
- missing review range
- ranges that touch process/tooling/playbook paths unless a recorded human
  override classifies them as project-pass work
- dirty implementation files when moving to `READY_FOR_REVIEW`
- `round` greater than `max_rounds`
- packets that do not declare the current review head
- packets whose Project Verify Gate section is missing or nonzero, except that
  a generated strict packet may be regenerated once with
  `ALLOW_UNRESOLVED_LXXXX=1` when the only observed verify failure is expected
  unresolved `LXXXX` labels
- review files that omit a verdict
- attempts to mark approval without a review artifact
- unsafe run ids, project slugs, or archive output paths

The script should avoid making commits. The implementation agent remains
responsible for committing implementation or response changes.

## 8. Tmux Handoff Transport

The implemented v1 transport is optional and tmux-based. The user still starts
Codex, Claude, and any worker loops manually; this layer only feeds the next
turn once state changes. The state file remains authoritative, and the protocol
still works manually through `status`, `ready`, `approve`, `request-changes`,
`reready`, and `archive`.

```sh
python3 scripts/agent_review.py watch --role <role> \
  --notify scripts/agent_review_tmux_notify.sh
```

Expected behavior:

- `watch` invokes `<notifier> <role> <status> <prompt-file>` and passes
  `AGENT_REVIEW_*` environment variables.
- `scripts/agent_review_tmux_notify.sh` sends the prompt to the configured
  already-running tmux pane for the target role.
- The adapter uses tmux bracketed paste so multi-line prompts arrive as one
  input in paste-aware agent TUIs.
- `AGENT_REVIEW_TMUX_SUBMIT=0` pastes without the final submit Enter for dry
  runs.
- The adapter validates the target pane and cleans up tmux buffers on failure.
- Failed notification does not mark `.seen`; the watcher can retry.

The transport is convenience. It does not start, supervise, or detect readiness
of agent sessions. Target panes should be idle at a paste-aware agent prompt
before automatic submission is enabled. If a pane is mid-task, the adapter
cannot detect that; this is the main inherent risk of the v1 transport.

The transport should never infer approval or requested changes from chat text.
Only the state script should change `.agents/current.json`.

## 9. Agent Instructions

V1 uses generated per-turn prompts and `agent_playbook/TOOLING.md` instead of
tracked `.agents/IMPLEMENTER.md` or `.agents/REVIEWER.md` files. The role
rules below remain the protocol contract for generated prompts, future
adapters, and any later role-file split.

Implementation-agent instructions:

- Before starting a new pass, check `.agents/current.json` if present.
- Do not continue when status is `READY_FOR_REVIEW`, `CHANGES_REQUESTED`, or
  `READY_FOR_REREVIEW` unless the transition says the implementer owns the next
  action.
- After a pass commit, run
  `python3 scripts/agent_review.py start-pass --project <slug> --pass-id <id>`
  when external/adversarial handoff is enabled for a normal single-pass range
  so note creation, initialization, packet generation, and status reporting are
  one operation. `start-pass` accepts range and run-id overrides directly; use
  lower-level `init` plus `ready --generate-packet` only for a hand-authored
  implementation note.
- If the reviewer requests changes, commit fixes or write a response that
  classifies every finding as `fixed`, `disputed`, or `deferred`; then run
  `reready`.
- Do not edit the review artifact except to add a response file.

Reviewer-agent instructions:

- Treat the review range as the unit under review.
- Prioritize correctness, false claims, missing verification, process drift,
  and weak evidence.
- Do not modify implementation files. The reviewer may run checks, inspect
  artifacts, read aggregate signals, and challenge evidence, but project-pass
  review is read-only.
- Write findings to the review artifact, not only to chat.
- Use `CHANGES_REQUESTED` for actionable defects and `APPROVED` only when no
  blocking issue remains.
- Keep non-blocking observations separate from findings.

Shared instructions:

- Git commits and project artifacts are canonical.
- `.agents/current.json` controls turn-taking only.
- Stop at `APPROVED` or `REVIEW_ROUNDS_EXHAUSTED`.
- A human override must be explicit and recorded.

## 10. Normal Workflow

One-pass external-review happy path:

1. The implementation agent runs a semantic pass, verifies, closes out, and
   commits.
2. The implementation agent runs:

   ```sh
   python3 scripts/agent_review.py start-pass --project <slug> --pass-id 105
   ```

   This creates `.agents/runs/<slug>-pass-105/implementation.md`, initializes
   `.agents/current.json`, generates and validates
   `.agents/runs/<slug>-pass-105/packet-round-01.md`, and writes the reviewer
   prompt. Use lower-level `init` and `ready --generate-packet` only for a
   hand-authored implementation note; `start-pass` accepts range and run-id
   overrides directly.

3. The manually started worker loop or transport wakes the reviewer.
4. The reviewer reviews `HEAD~1..HEAD`, writes
   `.agents/runs/<slug>-pass-105/review-01.md`, and runs:

   ```sh
   python3 scripts/agent_review.py approve \
     --review .agents/runs/<slug>-pass-105/review-01.md
   ```

5. The implementation agent archives the review:

   ```sh
   python3 scripts/agent_review.py archive --pass-id 105
   ```

6. The implementation agent commits the archive artifact, then may begin the
   next pass.

After the user starts both sessions and worker loops, this happy path should
not require the user to copy findings, paste responses, or manually wake either
agent. Human intervention is reserved for setup failure, disputed findings,
exhausted rounds, or explicit override.

Changes-requested path:

1. The reviewer writes findings and runs `request-changes`.
2. The implementation agent fixes the issues, commits the fix, writes
   `.agents/runs/<run_id>/response-01.md`, and runs `reready --generate-packet`.
3. The reviewer re-reviews `<original base>..HEAD`.
4. The loop ends at `APPROVED` or `REVIEW_ROUNDS_EXHAUSTED`.

## 11. Failure Modes

Dirty tree at handoff:

- `ready` should refuse a dirty implementation tree unless all changes are
  explicitly marked as untracked/ignored review artifacts.
- `archive` also requires a clean tracked tree before creating the tracked
  review artifact; commit the archive before starting the next handoff.

Stale state:

- `status` should compare `review_head` to `git rev-parse HEAD` and warn when
  the branch moved without a state update.

Stale verification evidence:

- A packet or implementation note must not present gate results from an earlier
  commit as proof that `review_head` is green. If historical gate output is
  included for context, it must name the SHA it describes and the packet must
  either rerun the gate at `review_head` or state why no current result exists.
- `ready` and `reready` validate that the packet declares the current review
  head and that its Project Verify Gate section reports exit status 0. If
  generated strict packet evidence fails on expected unresolved `LXXXX` labels,
  they regenerate once with `ALLOW_UNRESOLVED_LXXXX=1` and persist that mode.

Reviewer modifies implementation files:

- Any reviewer-created dirty implementation file is a protocol violation. A
  human can decide whether to keep, discard, or ask the implementation agent to
  port the change.
- Mutation testing belongs to ordinary process review outside this protocol,
  not project-pass review.

Rebase invalidates recorded SHAs:

- This is observed behavior, not a theoretical risk: routine project rebases
  can orphan earlier review SHAs within days, leaving artifacts that still
  describe a useful review but no longer point at reachable commits.
- `status` should verify that `review_base`, `review_head`, and any recorded
  approved heads still resolve with `git cat-file -e`.
- If a rebase or history rewrite orphaned a reviewed SHA, the script should
  report stale state and require a human decision: remap the run to replacement
  SHAs, keep the artifact as historical prose only, or discard the runtime
  state.

Notification transport fails:

- State remains valid. The human or agent can run `status` and continue
  manually.

Max rounds exceeded:

- Set `REVIEW_ROUNDS_EXHAUSTED` and stop. Do not keep asking agents to debate.
  A human may raise the limit, split scope, or continue only through a recorded
  override.

Disputed finding:

- A `disputed` response keeps the item visible for re-review. If the reviewer
  repeats the same finding and the implementation agent still disputes it,
  route to human override rather than consuming rounds indefinitely.

Conflicting human instruction:

- A direct human instruction wins, but should be recorded in the run directory
  when it overrides the state machine.

Missing reviewer session:

- `ready` can still write state and handoff files. The worker loop or
  transport should report that no reviewer endpoint is attached rather than
  silently dropping the wake-up.

Missing untracked project inputs:

- Packet generation and `project-verify` can fail in fresh worktrees when
  required untracked reference files, such as ROMs, are absent. This is a setup
  failure, not a review result. Regenerate from a checkout that has the project
  sources and required untracked files.

Tool path absent at review head:

- Review heads on the `projects` branch may predate `scripts/agent_review.py`.
  If the script is invoked by absolute path from a tool-bearing worktree, the
  generated prompts must preserve that path so reviewer commands are runnable
  from the checked-out review head.

Tmux pane not ready:

- The tmux notifier verifies the target pane exists and uses bracketed paste,
  but it cannot prove the agent TUI is idle. Automatic submission into a busy
  pane is outside v1's detectable boundary. Use `AGENT_REVIEW_TMUX_SUBMIT=0`
  for cautious dry runs or when pane readiness is uncertain.

## 12. Implementation Status

Completed v1 pieces:

- Project-pass packet generator landed first and is specified separately in
  [`PROJECT_PASS_REVIEW_PACKET_SPEC.md`](PROJECT_PASS_REVIEW_PACKET_SPEC.md).
- Range-level L-label reconciliation was added after the blind packet trial
  showed that phantom rename rows and benign label deletions need different
  packet signals.
- `scripts/agent_review.py` landed with `init`, `ready`,
  `request-changes`, `approve`, `reready`, `status`, and `watch`; `start-pass`
  was added after live loop friction showed manual note/init/ready setup was
  too easy to perform out of order.
- `archive --pass-id` landed separately after the durability decision: commit
  only irreproducible review judgements and implementer responses; keep
  packets and runtime state ignored; identify the durable record by
  project/pass id while treating recorded SHAs as review-time provenance.
- `scripts/agent_review_tmux_notify.sh` landed as the v1 transport for
  already-running tmux panes.
- `agent_playbook/TOOLING.md` documents the packet, state machine, archive
  behavior, tmux notifier, and operational preconditions.
- `AGENTS.md` owns the `Review a committed project pass` route, and generated
  reviewer prompts reference that row instead of carrying a duplicate playbook
  bundle.
- The protocol is opt-in over ordinary self-review-only pass closeout; it is
  mandatory only when a run elects external/adversarial review or a future
  project policy explicitly requires it.
- Generated prompts and archives now support a learning loop: reviewers and
  implementers can record `## Learning Candidates`; archive copies non-empty
  sections to `projects/<slug>/PROCESS_FRICTION.md` for later process triage.

Deliberately not implemented in v1:

- starting, logging in, supervising, or health-checking agent sessions
- MCP or a custom daemon
- automatic semantic judgement
- automatic merge, push, or remote CI orchestration
- tracked `.agents/` role files or templates
- automatic cumulative-review cadence
- pane-readiness detection beyond tmux target existence

Remaining rollout work:

- Run a larger unattended Zelda batch with per-pass Claude review in the loop.
- Stop on `CHANGES_REQUESTED`, failed gates, packet/transport failure,
  repeated low-yield/process friction, or the chosen checkpoint size.
- After the batch, decide whether the protocol becomes mandatory for
  unattended project-pass work and whether a periodic cumulative-review cadence
  is needed.

## 13. Validation Record

Automated tests now cover:

- `start-pass` creates the implementation note, initializes state, generates
  and validates a packet, writes the reviewer prompt, and prints status
- `init` creates a valid run directory and state file
- `init` rejects process/tooling ranges
- `ready` rejects dirty tracked state
- `ready` rejects packets with stale review heads, missing verify-gate
  sections, or nonzero Project Verify Gate status
- `ready --generate-packet` auto-regenerates expected unresolved-`LXXXX`
  strict verify failures in relaxed mode, and does not relax other verify
  failures
- `request-changes` requires `Verdict: CHANGES_REQUESTED`
- `approve` requires `Verdict: APPROVED`
- `reready` advances the review head, increments rounds, rejects stale packets,
  and rechecks project-pass path boundaries
- exceeding `max_rounds` sets `REVIEW_ROUNDS_EXHAUSTED`
- tampered `run_id` and project slug values are rejected on state read
- archive requires `APPROVED`, records reviews and responses, excludes packets
  and prompts, and rejects paths outside the repository
- archive copies non-empty `## Learning Candidates` sections from the
  implementation note, reviews, and responses to the project's
  `PROCESS_FRICTION.md`, while `_None._` sections are ignored
- long-running `watch` can start before `init`, waits for state, and does not
  repeat the same notification after `.seen`
- reviewer prompts route through the `Review a committed project pass` row in
  `AGENTS.md`
- tmux notifier uses bracketed paste, honors `AGENT_REVIEW_TMUX_SUBMIT=0`,
  rejects missing targets before loading buffers, and cleans buffers on
  paste-time failure

Manual and live validations performed:

- A known-bad packet with a phantom `renames.csv` row was rejected by the
  reviewer; the corresponding clean packet was approved.
- Generated packets were used on real Zelda passes and matched the hand-built
  contract, including range counters and gate evidence at `review_head`.
- A re-review loop reached approval at round 3 with a fresh packet at the
  advanced head.
- Durability was validated by archiving multi-round review and response
  artifacts under the project docs tree.
- Real tmux 3.7c probes found and then verified the bracketed-paste and stale
  pane fixes.
- Passes 113 and 114 completed with the tmux handoff, reviewer polling,
  approval archive, and review-archive commits.

Still unvalidated:

- A long unattended batch in which the implementation agent continues through
  many passes without user nudging.
- Whether the default round cap of 3 is right for project-pass re-review.
- Whether periodic cumulative reviews should be scheduled by count, signal, or
  reviewer request.

## 14. Resolved Decisions and Open Questions

Resolved for v1:

1. `.agents/current.json`, `.agents/runs/`, prompts, packets, `.seen` markers,
   and logs are ignored runtime state.
2. Review verdicts/findings and implementer responses are durable project
   provenance and are archived under
   `projects/<slug>/docs/reverse_engineering/reviews/pass-<id>.md`.
3. Review artifacts are keyed by pass id in project history rather than by a
   separate SHA log, because routine project rebases can orphan SHA-keyed
   runtime artifacts. Review-time SHAs are still recorded as provenance, but
   the archive labels them as non-durable identifiers.
4. `REVIEW_ROUNDS_EXHAUSTED` is a first-class terminal state for the current
   run.
5. The reviewer may write protocol review files under `.agents/runs/`, but
   project-pass review remains read-only over implementation files.
6. `ready` and `reready` check tracked dirty state only; unrelated untracked
   local files are tolerated.
7. Re-review covers the original base through the latest head.
8. V1 transport is tmux notification between already-running, paste-aware agent
   panes.
9. Session startup, login, supervision, and readiness detection are out of
   scope.
10. Reviewer prompt routing is owned by `AGENTS.md`, through the `Review a
    committed project pass` row. Prompts and packet specs reference that row
    rather than duplicating its playbook bundle.
11. The prior-art spike was not run before v1. The build path was chosen and
    reviewed through local branches because the required pieces were small,
    repo-specific, and empirically hardened by packet/state/tmux trials.
12. Noninteractive reviewer engines and third-party coordinators remain
    optional comparison paths, not prerequisites.

Still open:

1. What should the normal enforcement scope be: every semantic pass, only
   unattended batches, or projects that opt in through `project.conf`?
2. What is the right checkpoint size for unattended batches before human
   summary review?
3. What cadence should trigger cumulative aggregate reviews: every N passes,
   every N proof-debt warnings, every scorecard checkpoint, or only when the
   per-pass reviewer requests one?
4. Is the default round cap of 3 right for project-pass re-review?
5. Should v2 add an explicit human override command, or is stopping for direct
   user instruction sufficient?
6. Is the rejected-path rule complete enough after more real passes, especially
   for project-local generated artifacts whose paths resemble tooling?
7. Should a future transport add agent readiness detection, or is the tmux
   "pane idle before submit" precondition acceptable?
8. Should a future external coordinator be spiked now that the local protocol
   exists, and if so should it be evaluated as a replacement, comparison
   reviewer engine, or fallback transport?
