# Codex implementer adapter

Status: opt-in implementer adapter, exercised with Codex CLI 0.167.0 on macOS
arm64, using a subscription login and `gpt-6-astra` at `xhigh`. The accepted
contract allows four extra tools to be visible, but any attempted use halts the
phase. It is a facts-only callable contract, not facts-only tool exposure.
Each real corridor still needs owner authorization and admission against its
reviewed configuration. Offline tests alone do not admit a client.

## Established evidence and limits

The authenticated access preflight passed all 17 phases in one attempt:
functional repair and same-thread resume, nine of nine forbidden-tool probes,
and three live compaction checkpoints followed by successful facts calls.
The implementer/reviewer role gate passed, native inspection reported zero
enabled skills, and every phase completed process cleanup with no survivors.
The canary positive control detected access; no phase recorded canary access
or a code-mode host in its sampled process tree.

After admission, this adapter completed repair, publication and closeout in a
real pass on a local project branch. The existing Claude reviewer approved the
result, external review accepted it, and the service applied it locally after
its gates passed. This establishes the exercised opt-in workflow; remaining
operation coverage, runtime workers and default rollout retain their separate
gates in the [rollout plan](ROLLOUT_PLAN.md).

The live evidence covers one client version on one platform. There is no
Windows or Linux client-execution evidence. Process sampling is not a syscall
trace and can miss short-lived processes. The canary detects access only through
its FIFO; an empty log is not proof of every possible filesystem denial. Usage
figures are lower bounds, particularly when a phase is interrupted. Offline
tests use stand-ins and synthetic fixtures and require no installed Codex binary,
credentials or provider calls.

`scripts/structured_codex_client.py` prepares a separate Codex implementer
profile against an existing structured corridor. Its workspace lives inside the
profile, outside the OS-managed temporary directory. The service retains the
published generations, candidate history, review reports and role permissions.
Codex starts its own thread; it cannot resume another provider's conversation.
The takeover prompt must direct it to read service state and the pending report.

The adapter does not modify the service, reader pins, old client profile or
old usage records. First launch refuses a changed editor-state handoff. Its files live outside `scripts/structured_pass/` so adding
the adapter does not change source-reader identity. Preparation reads the
existing editor-state pin and starts unauthorized. It accepts an advanced
corridor, including one with published candidates.

## Preparation

Run `python3 -B scripts/structured_codex_client.py prepare` with explicit
`--root`, `--session`, `--prompt`, `--message-file`, `--client`, `--interpreter`,
`--service-root`, `--heavy-lock`, `--model` and `--effort`. Paths in the resulting
profile are absolute. Use a new profile root. Optional `--media` accepts pinned
PNG images for `view_image`; PDF intake needs separate, reviewed preparation.
The model receives the pinned prompt through `model_instructions_file`.

The isolated `auth-config` directory starts empty. Authentication uses a
subscription login with file credential storage in that directory. Never seal,
archive or publish this directory. Login is a separate owner action; preparation
does not copy another client's credentials. `check --root <profile>` checks
local pins and configuration only. It accepts the client-managed
`auth-config/skills/.system/` directory, while refusing other skill entries and
symlinked skill roots. `skills.bundled.enabled=false` disables that content;
native inspection must show zero enabled skills after startup and reopen.

The client environment sets `GIT_CEILING_DIRECTORIES` to the profile root.
Its workspace therefore cannot discover an enclosing repository. Offline
capture checks the actual Git invocations and requires null session Git
metadata; `--skip-git-repo-check` alone does not prevent discovery.

## Access boundary

The required MCP server exposes only `facts.operation`, with its role fixed to
implementer. Configuration disables `shell_tool`, `unified_exec_tty`, daemon
auto-start and guardian approval, plus browser/computer access, web search,
plugins/apps, subagents, code mode, memories, goals and automatic skill discovery.
Only `mcp_servers.facts.tools.operation.approval_mode` is set to `approve`.
The global approval policy remains `never`. A hook allow does not override the
client's separate MCP approval gate; the offline functional check must obtain
the actual service response, not merely complete a client turn.
`unified_exec=false` is requested but ignored without managed requirements. Its
internal enabled state is an accepted exception; the shell boundary is
`shell_tool=false` plus proof of the actual offered tools. The native feature
list still must match its allowlist. `agents.enabled=false` removes collaboration
tools, and the facts namespace is direct-only, omitted from deferred/code-mode
surfaces. The pinned model catalog nevertheless forces code-mode tools. No model
catalog override is applied by this adapter. The
named permission profile denies filesystem reads by default, grants the
platform's minimal runtime paths and the isolated reference workspace read
access, and denies command network access. It grants no writable paths.

A pre-tool hook denies every local tool except the exact service tool and
unchanged, explicitly pinned reference images. Broken hook input, policy or log
exits 2 to deny; an ordinary hook error would not suffice. Hosted tool features
are disabled separately because hooks do not cover them. The configuration and
hook are hash-pinned. Trust bypass applies only to these reviewed hook programs;
the command does not bypass sandboxing or approval policy.

Acceptance records the actual offered tools, feature settings and hook
configuration. Test every offered forbidden tool on launch and resume, with
source, store, Git and credential canaries watched throughout. Verify that
alternate MCP, file/edit/shell, self-reconfiguration and child-session routes
are absent from the offered declaration or refused before execution. Distinguish
an absent route from a live denial probe. Offline hook tests cannot substitute
for actual-client evidence. A boundary failure stops admission.

The offline gate captures rejected requests at a loopback stub with no login.
It requires the direct facts operation plus exactly `functions.exec`,
`functions.wait`, `functions.request_user_input` and
`functions.request_user_input_async`. Only facts is callable. It also pins the
whole declaration, including schemas, descriptions and array order, using
UTF-8 `json.dumps(declaration, sort_keys=True)` with default separators and ASCII
escaping, without a trailing newline. SHA-256 must equal
`8df1bc0a8356e4d28df87aba94957298f5113bc1264763d99b70174bb2e1d6ba`.
The installed code-mode host binary is pinned although its feature is off.
Nested capability headings are not parsed as an access allowlist.
The shell-on control must add
`exec_command` and `write_stdin` to code-mode declarations. A custom-provider
capture does not prove the ChatGPT-authenticated catalog exposes the same set.
Live phases export names, declaration hashes and identifiers from the matching
thread's `additional_tools` records. Any declaration difference, including an
authenticated-catalog difference, halts acceptance. This evidence path depends
on the pinned code-mode catalog; non-code-mode models are not supported.
Same-thread resume replays the launch declaration; each phase audits that
record without requiring a newly appended declaration.
Resolve calls against the preceding, hash-checked declaration in that same
session. An explicit namespace/name pair must be declared. Without a namespace,
the bare name must identify exactly one declared tool; no suffix or joined-name
matching is allowed. The call kind must also match: `custom_tool_call` for a
custom tool, `function_call` for a function. Only the `mcp__facts` / `operation`
pair with `function_call` is allowed. Unknown, ambiguous and wrongly typed calls
halt. Audit records retain both the observed spelling and resolved identity;
joined names are display labels only. The hook requires the pinned declaration
even if no call record has arrived yet.
Raw rollouts stay
private; they are not review artifacts. Incremental-tool defaults remain on so
the native session retains these records.

Correlate every facts call with a hook allow row. The read loop polls both the
hook log and matching private session even when stdout is silent. A deny row
or any non-facts call stops the phase during the turn. A final audit remains
mandatory. Before permitting facts, the hook also checks the private session
for earlier forbidden calls, preventing a fast follow-on facts call from
beating the polling interval. Incomplete trailing records wait for a newline;
the final audit still requires complete records. Missing or ambiguous session
evidence refuses a facts call.

Authenticated compaction passed with the pinned client: three remote-v2
checkpoints, successful facts calls after each, and a refused `exec` on the
compacted thread. The separately authorized synthetic profile used a lowered
threshold; ordinary profiles retain the model default. Do not extrapolate this
result to another client, provider or checkpoint format. Unknown events and
unfamiliar checkpoint shapes continue to halt.

Track descendants by parent chain, retaining their PID, process group and
observed start time. Children can lead separate groups. Persist discoveries
while running and retain identities after reparenting. Cleanup observes and
stops every still-owned group, including the exact session's implementer bridge.
An enclosing daemon with a different parent chain is not part of the phase.
Polling cannot prove absence of arbitrarily short-lived processes.
Cleanup failures are recorded and prevent resume. Event detection cannot undo
tool effects; preflight must independently prove pre-execution denial.
Record the actual offered tools and phase process tree; no child
Codex, daemon, bridge or hook may survive phase cleanup.

<a id="admission-and-execution"></a>
## Admission and execution

Pin both the client and installed code-mode host by SHA-256. Before calling
`prepare()`, compare the installed binaries with the hashes from the accepted
preflight profile; after preparation, require the new `launch.json` to record
those same hashes. `prepare()` records whatever binary is at the supplied path,
so profile self-consistency alone does not prove that the client was preflighted.
This comparison belongs in the trusted operator's admission procedure.

Do not upgrade the package manager or its client packages during a pass.
Upgrades deleted pinned version directories twice during the exercised workflow.
Keep the exact binaries and paths available until closeout. A missing or changed
binary stops admission or resume; restoring verified identical bytes preserves
the pin, while substituting another build requires review of the new configuration.

Audit every prompt and resume message against the operations offered to its
role. Demand only offered operations and keep negative probes consistent with
the missing-operation stop rule. An earlier functional prompt required an
unoffered reviewer operation while also forbidding it; the model correctly
stopped instead of completing the repair. Test cross-role refusals outside the
model's task, through a disposable fixture and the configured bridge. Distinguish
a required candidate entry such as `{kind:"closeout"}` from permission to call
the separate `closeout` service operation.

`run --root <profile>` requires the shared heavy-run supervisor, a separate
`authorization.json`, a matching launch hash and a future wall deadline.
Authorization records the owner's decision and purpose (`access_preflight` or
`pilot_takeover`). A takeover also pins access-preflight and transition-review
records by path and hash. The operator must assess those records before writing
authorization; a record hash alone is not an approval verdict.

Token and response counts are reporting-only under the separately approved
`none_usage_reporting_only` policy. The adapter records native turns and token
usage, including cached input tokens. It does not call tool items or messages
"responses", equate Codex turns with another client's responses, or reset old
usage. The wall deadline remains a separate owner decision.

Each phase persists its thread ID, raw JSONL, stderr, authorization hash and
result. Resume uses the same thread, prompt, configuration and pinned message.
Unstable-feature warnings are suppressed. Before the first turn, the parser
records only the exact pinned hook-trust warning (at most twice) and code-mode
unavailable warning (at most once), after thread initialization. Recording the
latter is diagnostic, not permission to admit the extra tools. Unknown, repeated
or misplaced warnings still halt. Tests replay a real rejected-request stream.
Quota errors, partial or unsupported events, unexpected tool events, changed
pins and timeouts halt execution. Interrupted/uncertain usage blocks automatic
retry; operator recovery requires a recorded decision. The adapter records the
client PGID immediately after creation, before waiting for any event. SIGTERM,
SIGHUP and SIGINT raise into cleanup, which signals the separate client group
and recorded descendant groups with TERM then KILL. The supervisor alone cannot
reap those separate groups. The intermediate status is `stopping`; a completed
halt record follows cleanup, and a cleanup failure remains explicit.
SIGKILL cannot execute cleanup; later runs and halt reconciliation refuse any
live recorded descendant, prior group, or bridge matching the full bridge-path,
absolute-session and `implementer corridor` command suffix. Reconcile under the lock before
retry, without clearing state or blindly killing a potentially reused PGID.
Reconciliation uses the process snapshot: a recorded group remains unresolved
when members survive and its leader is absent or matches its recorded start
time. A leader with a different start time identifies a reused number, which
is ignored. Missing identity evidence still refuses a live group. After cleanup
and reconciliation succeed, the run is marked `processes_reconciled`; later
runs skip those historical records but still check for the session's bridge.
Start times use the operating system's displayed precision.
A successful phase does not automatically
start another role or apply files to the project checkout.

A halt during a denial probe fails that preflight attempt. Preserve it; do not
clear its state to continue. Recovery records the failed attempt, then requires
review and a separately authorized fresh synthetic profile to repeat launch
and resume. A pilot halt requires its own transition review.
Recovery evidence includes the hook log and each run's stderr when present.

An explicitly authorized sacrificial probe is the exception: its expected
denial and halt may pass that negative probe only. It never passes a functional
repair or permits reuse of the halted profile. The acceptance protocol must
correlate client refusal evidence with the one expected call: a matching session
output, a hook denial or an exact per-call router error within the phase's time
bounds. Keep client refusal distinct from a halt that precedes the client's
refusal record. The latter requires independently checked disabled-host or
hook-denial configuration and live proof that the hook runs; an adapter halt
alone is insufficient. Both classes require reconciled cleanup, no sampled code
host, no canary access, no allowed forbidden call and no facts completion.

`run --probe-message <path>` requires purpose `access_preflight` and a `probe`
authorization with the exact absolute `path`, `sha256`, forbidden `tool`, and
boolean `resume` matching the phase. Any probe or override in `pilot_takeover`
refuses before process start. It changes no normal message or launch pin.
Only denial probes are individually capped at 180 seconds within the shared
owner-authorized deadline. Functional repair and benign launch phases use that
shared deadline; pilot phases also have no separate cap. Before a resume probe,
finish the benign launch under authorization without a probe, then record the
resume-probe authorization using the same deadline. A timeout
means incomplete timing coverage, not proof of an access defect. Neither
deadline nor a halt authorizes automatic retry.

Compaction is audited from the private rollout as well as the public stream.
The observed fallback and remote-v2 paths write `compacted` checkpoints without
adding a public JSON event. The scanner validates the checkpoint shape and every
replacement tool declaration, keeps all earlier calls, and refuses forbidden
calls in replacement history. Quoted summary text remains text. An unfamiliar
checkpoint shape or compaction item halts for review; parser changes during a
live preflight window are not allowed. The remote wire item is `compaction`,
not the app-server schema's `context_compaction` spelling.
Its optional `internal_chat_message_metadata_passthrough` field must contain
exactly one nonempty string, `turn_id`. Unknown fields still stop the phase.

`prepare --compaction-probe` pins a 16,384-token threshold. Admission requires
purpose `access_preflight`, `compaction_probe: true`, and `compaction_protocol`
with a readable `path` and matching `sha256`. A takeover cannot use this override.
Ordinary profiles leave the model threshold at its default. The synthetic
capture forces compaction using scripted token-usage metadata; it does not
measure actual model context pressure or prove live subscription behavior.
Live success still requires observed compaction and post-compaction facts calls.

The ordinary project-pass launcher and existing Claude adapter are unchanged.
