# Agent Session Operations

The review lifecycle lives in [TOOLING.md](TOOLING.md#agent-review-handoff).
These procedures cover coordinator evidence and authorized continuation of a
bounded task. They do not grant permission for further game passes.

<a id="proportionate-verification"></a>
## Proportionate Verification and Review Evidence

These rules cover tooling, process and structured-pass correction rounds and
review handoffs, for both implementers and reviewers. Preserve required gates
and discriminating regression controls; scale the surrounding work to the change.

Project passes still run `make project-verify PROJECT=<slug>` after every edit
batch and run the required closeout gates; the
[claimed-green rule](../AGENTS.md#safety-rules) is unchanged.

- **Small corrections get small packets.** Supply the diff, exact tested file
  hashes, relevant check/control results, failures and limitations, and hash-pinned
  references to prior evidence. A new review round alone does not require fresh
  archives, copies of unchanged evidence, or a new bespoke verifier.
- **Reuse verification and sealing code.** Pass paths, expected hashes and claims
  as data to existing helpers. Extend a shared helper only when a real requirement
  is missing; do not turn a small correction into a tooling-framework project.
- **Rerun checks according to impact.** Rerun affected checks after the final
  relevant edit. Label unchanged results as carried forward, naming their tested
  inputs. Broaden testing for changed dependencies, failures, unresolved concerns
  or an explicit acceptance requirement. This does not waive mandatory checks.
- **Bound integrity work.** Check relevant inputs, outputs and protected state
  the operation could affect. Do not recursively re-hash the entire historical
  packet chain on every correction. Perform comprehensive checks at required
  acceptance boundaries or when an integrity concern warrants them. Preserve
  existing seals and failed attempts; record authorized state changes separately.
- **Preflight harness changes cheaply.** Check imports, paths, input schemas,
  case routing and expectations on the smallest representative input before a
  costly replay, observing the shared-run locking rules. Distinguish harness
  failures from product failures; neither counts as a passing check.
- **Record round timing.** Each claims index records the first recorded work time,
  the review-handoff time and total heavy-job elapsed time from its receipts,
  including failed attempts. State timestamp precision and mark missing timing
  unknown. Separate coordination waits where measured; do not infer model thinking
  time or exact turn duration from gaps between reviews.
- **Explain why a finding blocks this task.** In tooling/process correction
  rounds, a Required finding must identify an unmet acceptance requirement, a
  defect that would break the task under its promised operating conditions, or
  evidence that cannot support the claimed result. Long sessions, compaction and
  termination count when promised. Additional tests for otherwise correct code
  and diagnostic polish stay parked unless a concrete risk makes them necessary.
  This criterion does not narrow game-pass naming, readability, documentation or
  other quality requirements, and does not waive existing gates or controls.

Reviewers should request additional evidence for a concrete unresolved claim or
risk, rather than requiring the full acceptance package again for every fix.
Apply the same impact rules to reviewers' own reruns, including the independent
checks needed to establish their verdict.

<a id="decision-checkpoints"></a>
## Decide when to reassess

Before substantial tooling/process integration or a detour, the agent driving
the work writes a short decision record in the task or PR plan: the outcome
that justifies the work, acceptance criteria, expected effort and uncertainty,
parked scope, and explicit reassessment triggers. Separate completing the
immediate task from building reusable infrastructure. Set an effort or review
round checkpoint and triggers for a repeated failure class or a subproblem
becoming its own project; a universal numeric budget is not required.
The record names the alternatives considered, including continuing the existing
workflow, and explains why the selected work should take priority.
Judge that priority against the [process objective](../docs/MANIFESTO.md),
including the capability or operating limitation the work is meant to address.

The driving agent calls the checkpoint when a trigger is reached, before
starting another correction round. The reviewer can raise it independently.
The owner decides whether to continue, change scope or stop. A passed review
round does not establish that continuing is worthwhile. Record the decision;
unused budget does not authorize retries, inference or additional work.
At milestone completion, use the existing
[retrospective guidance](DOCUMENTATION.md#milestone-retrospectives).

<a id="delivered-inputs"></a>
## Review delivered inputs and observe the real path

Before the first live run of a new integration, and after relevant input changes,
read each role's complete assembled input: base prompt, handoff text and owner
message. Apply the existing
[role-consistency checks](../docs/structured-pass/CODEX_CLIENT.md#admission-and-execution)
to those delivered bytes, not just the changed fragment. Check combined
instructions for conflicting duties, call sequences and stop rules.

Observe the smallest authorized real-client execution early enough to inform
fixtures and acceptance checks, including the intended successful path and the
changed failure behavior. Record the actual protocol and configuration; label
synthetic assumptions and provider differences. Use
[proportionate verification](#proportionate-verification) to determine subsequent
checks. A smoke result establishes only what it exercised.

<a id="stop-classification"></a>
## Classify results before choosing a remedy

Persist observations before parsing or classifying them, including partial
output, canary observations and process/cleanup results where collected. A
parser refusal must not discard the evidence needed to understand the stop.
Keep failed attempts intact and distinguish missing observations from negative
observations.

| Result | Response |
| --- | --- |
| Completed turn with handoff | Follow the authoritative handoff state; exit zero alone does not prove completion. |
| Normal return without handoff | Show unfinished work and wait for explicit owner continuation. |
| Budget or deadline stop | Report the exhausted allowance; an extension is an owner decision. |
| Containment breach | Stop affected execution and block reuse pending investigation and review. |
| Unfamiliar evidence | Stop, preserve observations and investigate whether the behavior fits the accepted contract. |
| Inconclusive evidence | Stop without claiming acceptance; identify the missing proof for the next decision. |

Classify from the available evidence before prescribing a change. An unfamiliar
result does not authorize a wider allow rule, and an inconclusive result does
not authorize a retry or weaker proof. Keep operational failure, evidence
failure and unfinished task state distinct. Proposed durable changes still use
[process-learning triage](REVIEW_AUDITS.md#process-learning-triage).

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
