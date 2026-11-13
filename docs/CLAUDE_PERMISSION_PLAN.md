# Reproducible Claude permissions and inspection assessment

Status: the four exact reviewer grants and offline setup are authorized on
13 November 2026. Review the generator change before preparing the disposable
smoke worktrees. Live sessions remain unauthorized. Keep the four-active-hour,
one-review-round checkpoint; a bound does not extend itself.

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
   Generate only the four approved wrapper forms below for the Claude reviewer.
   Upgrading an installed profile requires fresh consent; live use is separate.

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

<a id="wrapper-grants-proposed-for-owner-approval"></a>
<a id="exact-reviewer-wrapper-grants"></a>
## Exact reviewer wrapper grants

The initial source-selection change left the generated grants unchanged. This
follow-up adds the four authorized forms below to the managed Claude reviewer
only. Codex and implementer grants are unchanged. The generator substitutes the
validated project slug and renders each whole command as an exact `Bash(...)`
rule, with no trailing wildcard or `:*` suffix.

| Exact generated command | Purpose and allowed variation |
| --- | --- |
| `make project-regenerate-check PROJECT=<slug>` | Default regeneration comparison and 200-line preview. No extra assignments. |
| `make project-regenerate-check PROJECT=<slug> ALLOW_TRAILING_BYTES=1 REGENERATE_DIFF_MAX_LINES=4000` | Observed bounded preview form; the trailer override additionally requires the project's audited intake decision. |
| `make project-regenerate-check PROJECT=<slug> ALLOW_TRAILING_BYTES=1 REGENERATE_DIFF_MAX_LINES=100000` | Observed extended comparison form. This does not grant the custom classifier formerly piped after it. |
| `make project-hidden-code-scan PROJECT=<slug>` | Existing candidate inventory with default thresholds; no extra assignments. |

The only explicit variable values are the pinned project slug, the
audited trailer value `1`, and preview limits `4000` and `100000` in the exact
forms above. These are not arbitrary free-form values. No `STRICT`, `MIN_SIZE`,
`THRESHOLD`, `MAX_START_OFFSET`, `SHELL`, `MAKEFLAGS`, path override, extra target,
`-f`, `-C`, `-e`, `--eval`, or command suffix is granted. Ordinary default values
still come from the reviewed repository/configuration and frozen environment.
Other project gates remain explicit decisions if independent reruns need them;
the generator does not grant all Make targets.

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

## Offline smoke setup after generator review

Use a local-only scratch branch from the frozen project-branch head, with the
reviewed tooling commit merged into that scratch branch. Do not merge or rebase
the actual project branch. Record both inputs and the resulting snapshot.
Require the `projects/` subtree to match the frozen project head, and require
`git diff <reviewed-tooling-commit> <scratch> -- scripts tests agent_playbook
AGENTS.md Makefile` to be empty. An unresolved difference stops preparation.

Create two fresh detached worktrees from that same snapshot outside the main
checkout, under `/private/tmp/`, one per permission mode. Inspect ancestor
instruction files. Copy the selected project's supplied ROM, reference PDFs and
existing text extract into each tree; never symlink them. Hash-match each copy.
Do not copy `.agents` state, permission settings or client history. Keep project
identities, input paths, snapshot hashes and expected case results in the private
smoke manifest, not this shared plan.

Run the regeneration check and hidden-code scan offline in disposable preparation
copies under the shared lock. Confirm their expected results and that both leave
tracked files byte-identical; derived outputs alone may change. Freeze equal
starting inputs for both sessions after prechecks, including any prepared build
artifacts. A failed dependency or unexpected tracked change stops before launch.
Install only generator-produced reviewer settings with consent, and retain the
receipts. No hand-edited grants or new global configuration.

## Fixed reviewer inspection script

Only Claude's reviewer role runs. Start two cold Opus 5.5 sessions sequentially,
`default` then `dontAsk`, at explicit `high` effort. This differs from the
historical trial's `xhigh`; command choices and cost are not a controlled
comparison with that trial. Execute the generated reviewer argv verbatim in a
dedicated pane. First deliver a fixed context-loading message that permits only
`READY_FOR_SMOKE` and no tool use. Verify the instruction block in the resulting
client input records, then deliver the fixed inspection prompt. The acknowledgment
is not delivery evidence. Start no implementer, handoff watcher or normal pass
launcher. This measures the generated reviewer
profile, not the complete handoff cycle.

Before live authorization, expand the following cases to exact paths, commands,
source windows and expected results in a hash-pinned prompt and manifest. The
prompt forbids pass work, verdicts, Git changes, grant edits and command rewrites.

| Case, in order | Fixed request and evidence |
| --- | --- |
| Governing instructions | Coordinator verifies the complete root `AGENTS.md` in client input records as specified below, before inspection proceeds. |
| Source windows | Native `Read` for the two pinned assembly windows. Preserve the returned lines. |
| Literal search | Generated `find-project-symbols` with three pinned symbols, repeated once. Compare matching lines with offline expectations. |
| Single-file regex | `grep -n -E '^[[:space:]]*BIT[[:space:]]' <asm>` as one Bash call. Record results or refusal; exit 1 means no matches, not an execution failure. |
| Cross-project regex | `grep -l -E '^NMI:' projects/*/asm/*.asm` as one Bash call. Compare the complete path list with the frozen corpus. |
| References | Native reads of the first 160 lines of the copied text extract and pages 1–2 of the manual. Missing tools or content remain evidence gaps. |
| Regeneration | Exact 4,000-line regeneration form, using the audited trailer override where applicable. Record wrapper exit, summary and preview. |
| Inventory | Exact hidden-code scan, followed by native `Read` of its CSV. Compare with offline expectations. |
| Pipeline | The same regeneration form with `2>&1 \| head -150`. Distinguish permission refusal, command failure and truncated output; the Make grant does not grant the consumer. |
| Ungranted computation | `shasum -a 256 <copied-rom>` with no added hash-tool grant. A refusal leaves the fresh hash missing. |

The plain regeneration form and the 100,000-line custom-classifier pipeline are
not exercised in this short smoke. The selected ROM requires its audited trailer
override, and the historical classifier describes an earlier source snapshot.
Do not claim live coverage of those forms. Plain search receives no new grant;
its behavior under the client's built-in read-only policy is a measured unknown.

For a permission prompt, record it and deny once; do not approve execution, add a
rule, retry, substitute a tool or rewrite the command. Continue to the next fixed
case after a recorded refusal. This deny-once action is coordinator assistance,
not unattended behavior. Report all cases, including unfinished ones. A denied
computation remains missing evidence even if all other inspections finish.

## Instruction-delivery measurement

Preserve the transcript before parsing. Decode the client's `attachment` and
`api-request-blob` records and locate the block introduced by
`Contents of <absolute-smoke-root>/AGENTS.md`. Extract the full file block using
the observed framing, encode it as UTF-8 and compare its SHA-256 with the copied
file. Do not strip whitespace, normalize line endings, reconstruct absent text,
or substitute the reviewer's assertion or echoed text. Record the source record
and block boundaries. Require a complete matching block before inspection; any
observed conflicting copy for that exact root also fails the session. Missing,
truncated, mismatched or unfamiliar input records stop for assessment. The
offline extraction check must reject synthetic missing and altered blocks before
any live authorization.

Auto-memory is keyed by path: these fresh worktrees start without the main
checkout's memory index. Record this difference, plus any other memory observed
in client input records. Workspace-trust acceptance can create a project entry in
`~/.claude.json`; count it as an operator action separate from command permission
prompts. Neither memory nor trust is evidence of confinement.

## Live authorization, measures and stop rules

The live request follows generator review and completed offline preparation. It
must bind the two worktrees, code/client/profile/input hashes, exact prompt and
stop procedure. The proposed window is 30 minutes total from the first client
launch, with at most 15 minutes per session and no retries or automatic extension.
Arm the guard before launch and recheck the deadline immediately before each
client starts. A quota/authentication problem, instruction-delivery failure,
configuration drift, unexpected tracked edit or deadline ends the experiment.
Permission refusals are measured cases, not permission to modify the setup.

For each mode record completed cases and their evidence, prompt counts and
`permissionDecision` reasons, denials, missing operations, coordinator actions,
waits, elapsed time and per-role token/cache categories. Keep observations before
classification under the existing
[session rules](../agent_playbook/AGENT_SESSION_OPERATIONS.md#stop-classification).
Zero `user_temporary` decisions do not establish success when evidence is missing.
Report routine-case completion separately from the ungranted computation, while
retaining that gap in the overall result. Do not claim reduced interruptions
against the historical twenty prompts: tasks and effective permissions differ.

Copy transcripts and records from the temporary worktrees and client session
paths into the private baseline evidence folder before removing the worktrees;
macOS can age `/private/tmp` out. Then remove only the scratch worktrees and
scratch branch. Preserve both successful and failed observations.

The driving agent records results and calls the checkpoint; the owner decides
whether to proceed. No live session or trial restart is authorized by the offline
work. Regardless of smoke outcome, the next project segment requires preserving
the paused checkpoint, rebasing the actual project branch onto master, and
restarting with a new run ID and separately authorized window. Before that
restart, check offline whether managed settings can disable auto-memory and
present the memory choice explicitly; do not silently change it during this smoke.
