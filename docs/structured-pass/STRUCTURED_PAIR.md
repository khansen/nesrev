# Supervised structured pair

The [FG-1 launcher slice](FG1_LAUNCHER_SLICE.md) connects the existing corridor,
handoff watcher and subscription adapters. The supported pairing is Codex
implementer / Claude reviewer on the admitted macOS arm64 platform. Offline
tests do not establish live client admission. The hook-disabled reviewer test
and the refreshed native declarations require the separately authorized smoke.
The latest admission attempt passed the hook-disabled read-boundary check and
delivered a reference image, then stopped on a missing client-visible argument
contract. The [production correction and declaration captures](ARGUMENT_CONTRACT.md)
require review before another sealed smoke.
The preparation check is an integrity check, not a claim that media are usable.

## Preparation and authority

Prepare the corridor and both client profiles with the same declared inputs,
task, run ID and shared heavy-run lock. Client packages, interpreter, explicit
model and effort come from the preparation record. Keep profiles and workspaces
outside every Git checkout; the service and retained store remain separate.
The launcher checks workspace ancestry again before each invocation. A `.git`
file, directory or symlink, or a bare repository ancestor, refuses admission.

`structured_pair_launcher.py --root <pair> prepare --session <corridor>
--implementer <codex-profile> --reviewer <claude-profile> --task <task-file>`
creates an unauthorized pair. The task must equal the Codex profile's initial
message, and both declared-input assemblies must carry that same task and
catalog. Optional `--application-repo` pins the trusted application destination.
No agent can choose that destination.

The pair pins its code, profiles, task, notifier and complete implementer,
reviewer and retained-review tool declarations. Codex separately pins the full
native declaration, including the client's offered but forbidden tools; those
remain audited and denied. A changed declaration requires fresh admission.
Existing sealed profiles are not rewritten.

After live authorization and isolated login, the operator supplies an explicit
record to `authorize --record <file>`. It contains `owner_message`, absolute
epoch `deadline`, `invocations`, `responses` (Claude only), `turn_seconds` and
`purpose`. Functional use retains the Codex adapter's `pilot_takeover` admission
and its pinned `access_preflight` and `transition_review` evidence. The smoke
uses `access_preflight`. Preparation never creates this grant.

The same absolute deadline is installed in both adapters. It includes waiting
for the other role, validation and the shared lock. Claude response IDs and
Codex native turns/tokens remain separate measures; neither is converted into
the other. There is no implicit token allowance or forecast of quota.

## Launch and delivery

```sh
python3 -B scripts/agent_review_tmux.py --workflow structured \
  --prepared /absolute/private/pair --check
python3 -B scripts/agent_review_tmux.py --workflow structured \
  --prepared /absolute/private/pair --session structured-pass --no-attach
```

The check is offline and does not check subscription login. Launch creates
placeholders, records both pane IDs, rechecks the expiry, then starts supervised
workers. Each watches only `<corridor>/handoff`, bound to the recorded run ID.
The ordinary launcher and its checkout review state are not used.

The implementer receives the pinned initial task. Subsequent turns come from
`agent_review.py watch --notify`, at a two-second interval. The notifier checks
the role, run, head and exact prompt bytes, records them, and serializes turns
before starting the existing adapter under the heavy-run lock. Duplicate
notification identities are refused. The watcher releases service locks before
the notifier starts; transient busy refusals wait within the original deadline.
Other watch errors stop the pair. Coordinator busy refusals are retained for
the smoke's count, alongside bridge refusals in client records.

The watcher passes its polled identity in `AGENT_REVIEW_NOTIFICATION_TOKEN`,
including the published head even when the status is unchanged. Before waiting
for the turn lock, the notifier records that identity and the prompt hash it
observes at entry in `notifications/`. After obtaining the lock, it checks the
current identity. A superseded notification is recorded as dropped and returns
success without starting a client or spending an invocation; the watcher polls
again and delivers the new identity. Accepted notification records refer to the
authoritative turn record. A changed run, an out-of-handoff message path, an
already-delivered identity or unexplained prompt drift within one identity still
refuses. Dropping duplicates after a lost seen marker remains deferred.

Codex receives each recorded message on the existing native thread. Message
records bind the profile, run, thread and exact bytes. The access-preflight
probe override remains separate. Claude receives the same message after its
existing allowance notice; both the raw message and complete delivered input
are retained. Historical intake text stays on demand, labeled as historical.

Signal and deadline supervision is armed before subprocess creation and checked
again immediately before starting it. The existing process-tree helper observes
and reconciles descendants, including separate groups. Raw streams, process
identities and failures remain in the record. Supervision cannot prove absence
of arbitrarily short subprocesses, and it does not add an OS boundary to a
native client.

## Stops, continuation and application

`status` reports checked service state and the launcher record. A successful
client exit counts as handoff only if the authoritative service advanced to the
other role. An unchanged state is `unfinished`; both watchers stop. The operator
can use `continue <role> --message-file <file>` to record steering and invoke
one more turn within the remaining allowance. If that produces a handoff,
`resume-watchers` restarts only dead panes. It never resends a completed turn.

`extend --record <file>` is a separate operator action, with `owner_message`, a
later `deadline` and optional additional `invocations` and Claude `responses`.
It retains the previous authority, counters and turn results. It does not clear
an interrupted adapter, uncertain usage, a failed watcher or unreconciled
processes. Those stops require investigation and an explicit recovery decision;
relaunching is not recovery. An extension alone starts no client.

The client adapters retain detailed quota, tool/audit and stream errors. The
pair treats failed or unfamiliar adapter output as recovery-required, rather
than inferring a safe retry from error prose. An exhausted invocation or wall
allowance cannot start a client. `halt.json` prevents peer reuse after a failed
watcher. No automatic quota retry, next pass or new deadline is provided.

Qualified closeout is checked through the existing controller and stops the
pair as `closed`. Application remains a trusted operator step:
`apply` requires an authorization record with `apply: true`, a prepared target,
current approval and closeout, and an unexpired window. It invokes the existing
application journal under the heavy-run lock. Dirty queues, changed preimages
and retry recovery retain that journal's existing rules. No push is performed.

## Evidence limits

Synthetic client streams test the real adapters, watcher, message transport and
service transitions without provider calls. Unit tests already under the shared
lock omit only a nested heavy-run acquisition; the standalone offline tmux
exercise must also cover the generated notifier and production heavy-run path.
Neither substitutes for live initialization, offered-tool, media, hook-disabled
denial and same-thread observations. A model refusal without a tool attempt is
missing evidence. A failed live attempt does not authorize another attempt.
