# Reproducible Claude permissions and inspection assessment

Status: offline implementation authorized on 13 November 2026. New execution
grants and live sessions require separate owner approval. The checkpoint is
four active agent hours and one implementation review round; it is a bound,
not permission to extend the work automatically.

## Outcome and scope

The [baseline assessment](retros/2026-11-13-fresh-game-process-baseline.md)
identified twenty reviewer approvals. Its subsequent audit found that the
reviewer also inherited 107 local allow rules. The prompted/unprompted split
therefore describes one machine's accumulated configuration, not a portable
repository profile. The historical counts and wait times stand; the estimate
that fifteen alternative requests could reclaim 36.4 minutes is not a measured
or portable improvement.

The next outcome is reproducible permission configuration, followed by measured
inspection coverage. This supports the [process objective](MANIFESTO.md) without
claiming confinement: repository wrappers, project analyzers and their
dependencies remain trusted code. Continue using the existing launcher; no
structured integration, new inspection framework or project rebase is needed
to prepare and test this change.

Alternatives considered are leaving inherited grants in place, adding inspection
guidance alone, or broadening interpreter permissions. None establishes a fresh
machine's effective profile. Source selection comes first; operational guidance
waits for actual permission observations.

## Offline steps and decisions

1. For both managed Claude roles, pass `--setting-sources project` with the
   generated role settings. Retain project instruction loading, including
   `AGENTS.md`; exclude user/local settings and their grants, plugins, hooks and
   model preferences. Refuse untracked (including ignored), modified, deleted or
   symlinked files under `<root>/.claude/`, except the excluded
   `settings.local.json`. Accepted files must match both HEAD and the index;
   record their hashes and the root `AGENTS.md` hash in the receipt. Recheck
   after consent before installing. Leave the original files untouched and
   preserve `inherit` and `bypass` behavior.
2. Require explicit model and effort arguments for managed Claude roles. Record
   those arguments, the permission mode, selected settings file, excluded
   sources and remaining ambient inputs in the consent receipt and workspace
   record. Receipt version 2 requires fresh consent when replacing version 1.
   Offer `default` and explicit opt-in `dontAsk` with the same generated grants.
   Prepare the finite wrapper proposal below; add no new grants before approval.

These are configuration checks, not observations of a running model. The first
implementation used an empty source selection. Independent offline review of
Claude Code 2.1.322's bundle confirmed that this maps to no sources, but also
disables project instruction loading, including `AGENTS.md`. That choice was
incorrect and is replaced by `project`. The offline CLI check now tests
`--setting-sources project --version` and rejection of `invalid-source`; this
exercises argument validation, not instruction delivery. The unit suite checks
both roles, argument transport, guarded project files, receipts, explicit
choices, consent migration and unchanged inheritance using disposable checkouts.

Managed policy still applies. The receipt's `observed_setting_sources` is null;
record actual loading separately during the authorized live check. Auto-memory,
account connectors, environment inputs, ancestor instruction files and Codex's
ambient rules remain baseline limitations. Project `CLAUDE.md` and project rules
remain eligible for loading along with `AGENTS.md`; the `.claude/` guard is
limited to the selected checkout, not its ancestors. No MCP-isolation claim is
made and `--strict-mcp-config` is not added. Excluding user settings also excludes their enabled plugins; a live check
must confirm the resulting tool set rather than assume it matches the old run.
Committed project settings can still supply grants, hooks and plugins; inspect
the recorded files before approving the profile.

## Wrapper grants proposed for owner approval

The implementation changes source selection, not the existing allow list. The
following finite additions are proposed for the reviewer only. Substitute the
one selected, validated project slug; render each whole command as an exact
`Bash(...)` rule, with no trailing wildcard or `:*` suffix.

| Exact proposed command | Purpose and allowed variation |
| --- | --- |
| `make project-regenerate-check PROJECT=<slug>` | Default regeneration comparison and 200-line preview. No extra assignments. |
| `make project-regenerate-check PROJECT=<slug> ALLOW_TRAILING_BYTES=1 REGENERATE_DIFF_MAX_LINES=4000` | Observed bounded preview form; the trailer override additionally requires the project's audited intake decision. |
| `make project-regenerate-check PROJECT=<slug> ALLOW_TRAILING_BYTES=1 REGENERATE_DIFF_MAX_LINES=100000` | Observed extended comparison form. This does not grant the custom classifier formerly piped after it. |
| `make project-hidden-code-scan PROJECT=<slug>` | Existing candidate inventory with default thresholds; no extra assignments. |

The only proposed explicit variable values are the pinned project slug, the
audited trailer value `1`, and preview limits `4000` and `100000` in the exact
forms above. These are not arbitrary free-form values. No `STRICT`, `MIN_SIZE`,
`THRESHOLD`, `MAX_START_OFFSET`, `SHELL`, `MAKEFLAGS`, path override, extra target,
`-f`, `-C`, `-e`, `--eval`, or command suffix is granted. Ordinary default values
still come from the reviewed repository/configuration and frozen environment.
Other project gates remain explicit decisions if independent reruns need them;
this proposal does not grant all Make targets.

These wrappers execute trusted Makefile, shell, project configuration and tool
code. They can regenerate/build files and write temporary or derived outputs;
they are not filesystem-read-only operations. Make environment and repository
code remain part of that trust. Scratch Python, arbitrary interpreters,
converters and broad shell tools receive no new rule. Existing trace/analysis
dispatch grants remain trusted execution, not a guarantee that every custom
computation prompts. Do not relocate scratch code to bypass a refusal.

## Inspection cases to measure

These are hypotheses under the narrowed configuration, not native decisions:

| Audited work | Candidate route | Remaining question |
| --- | --- | --- |
| Source windows, inventory files, 86-row CSV | Native `Read` with offsets/limits | Is the tool present and does it preserve useful evidence without excessive output? |
| Literal symbols in the selected project | Existing exact `find-project-symbols` route | Confirm both initial and repeated requests; its grammar does not cover regexes or other projects. |
| Raw-operand and cross-project searches | Available native search or simple shell search | No native Grep was offered in the old run. Without its ambient grants, shell behavior is unmeasured. |
| Reference sections | Existing source-matched text extract and native PDF reads | Intake already produced the extract, but the handoff did not identify it. Freshness and discoverability must be demonstrated. |
| Fresh hashes, binary checks and regeneration classification | Explicit approval or a separately reviewed operation | Existing file reading is not equivalent to computation; neither broad Python grants nor a renamed helper is an acceptable shortcut. |

The old prompt reasons were `no-rule-match` (10), `too-complex` (7),
`assigned-variable` (1), `cd-git-compound` (1), and `subcommandResults` (1).
Pipes and semicolon chains sometimes succeeded. Do not replace those observations
with a blanket claim that compound commands prompt, or predict the new profile
from the old classifications. Include the observed `2>&1 | head -150` and
classifier-pipe forms in the live checklist: an exact Make rule does not grant
the pipe's consumer, and its permission behavior remains unmeasured.

## Separately authorized live steps

After the owner accepts the grant delta and authorizes provider use, run a short
Opus 5.5 session with an explicit effort choice and frozen client/profile hashes.
Measure the inspection cases under the narrowed sources first, then compare
`default` and `dontAsk` with the same grants. These are steps 3–4 of the accepted
scope and cannot be completed by offline tests. No fresh trial window or project
pass is implied. A feature-branch worktree can host the smoke while the saved
project review remains untouched.

Acceptance requires completed routine inspection with equivalent evidence and
zero `user_temporary` permission decisions. Also count denied requests, missing
operations, repeated attempts and unfinished tasks: `dontAsk` must not win by
refusing necessary work. Record tool availability and actual settings sources,
and verify each role actually receives the hash-matched root `AGENTS.md` in
its initial context or an explicit read before inspection. Missing instruction
evidence fails the smoke even if the prompt count is zero. Check that the old
broad Python/Make permissions are not effective. Keep
prompt counts primary; wait duration is secondary and depends on supervision
cadence. Preserve observations before classification under the existing
[session rules](../agent_playbook/AGENT_SESSION_OPERATIONS.md#stop-classification).

The driving agent records results and calls the checkpoint; the owner decides
whether to proceed. Stop when the effort or review-round bound is reached, the
same failure class recurs, or source isolation becomes a separate project.
Live authorization wait does not authorize another task. The saved review state,
client settings and project ancestry stay unchanged until a separate restart
decision. This plan does not authorize any grants, login, inference or restart.
