# Structured pass correction: offline result

20 November 2026. The complete native wrapper now passes through application
on a synthetic fixture. The correction is ready for final code review after
the checks recorded below. It has made no provider calls and has not completed
a real semantic pass. The [scope](FG1_OFFLINE_CORRECTION.md) and earlier
[checkpoint](FG1_OFFLINE_CORRECTION_CHECKPOINT.md) and
[continuation](FG1_OFFLINE_CORRECTION_CONTINUATION.md) records remain available.

## Delivered contracts and recovery

The fixed `operation-reference` input is generated from the field definitions
that edit/query dispatch enforces. It covers 18 edit kinds, nested and
conditional shapes, accepted values and role-local sources. All required
arguments across the implementer, reviewer and retained-reader profiles are
classified. Captured reference bytes survive restoration and hash checks.
Corridor guidance uses the existing declared inputs; the redundant corridor
`guidance` operation is removed. Retained guidance exposes its accepted names.
Existing captures do not acquire a generated reference retroactively; prepare
fresh sessions for the corrected contract.

The native implementer fetched the 58,948-byte synthetic reference in eight
pages before editing. The accepted real input inventory projects 21 text items
against 32, 622,480 total text bytes against 2 MiB and a 59,676-byte reference
against 256 KiB per item. That inventory is a projection, not a fresh project
preparation. No limit increased. Both description fields remain below 4,096
characters; implementer headroom is 69 top-level and 281 argument characters.
The [contract documentation](ARGUMENT_CONTRACT.md) records the current native pin.

| Profile | Top-level characters | Argument characters | Listing bytes |
|---|---:|---:|---:|
| Implementer | 4,027 | 3,815 | 8,854 |
| Reviewer | 3,403 | 3,106 | 7,344 |
| Retained reader | 1,211 | 2,278 | 4,137 |

Removing corridor `guidance` frees 123 argument characters and no top-level
characters. The measured reference uses the existing paged input route.

Recovery uses `error_class`: correctable requests can be rebuilt from current
facts or a missing earlier step; busy locks are transient; boundary, integrity,
provenance, drift, internal errors and exhausted limits are terminal. There are
75 correctable, 3 transient and 124 terminal public codes. Typed request
diagnostics distinguish a submitted preimage error from captured-file drift
even where an older code is shared. Unknown codes fail closed. No class
authorizes another client invocation. Unpaged oversized results remain terminal.

The native recipe made two identical bad-preimage requests, received actionable
correctable refusals, then corrected the request and completed publication.
The final audit records the repetition as one learning candidate with count two,
without argument payloads in the summary. Lifecycle tests also cover correcting
a stale generation. Review identities resolve each adjacent required edge,
including after more than one publication.

## Supervisor correction

Darwin snapshots use libproc/sysctl, removing the setuid `ps` dependency that
Seatbelt refused. The independent review reproduced an exec race: argv reads
can return `EIO` while process metadata remains valid. The corrected helper
falls back to `(comm)` for any argv `OSError` or malformed argv buffer.
It retains the complete PID, parent, process-group and start-time row.

Enumeration, process metadata, argument-capacity and missing-self failures
remain fatal. Diagnostics name the stage, MIB, PID and errno, with explicit
non-applicable fields. Linux keeps the existing `ps` path. Seven supervisor
tests cover injected failures, fatal attribution, live equivalence and sandbox
execution. Restoring the old narrow fallback fails both regression controls.
The nondeterministic race probe is review evidence, not a CI requirement.

## Complete native wrapper

One freshly authorized loopback ran the actual pre-window status commands,
detached tmux launcher, watcher notifications, native clients, audits,
application preview, `apply_closed` and cleanup. The five turns were
implementer, reviewer, implementer, reviewer, implementer; their results were
four handoffs followed by closed. The recipe made 41 facts calls and 46 local
API requests. Every captured declaration matched the expected production listing
or native pin. All responses were scripted on loopback with dummy homes.

Application committed four expected files to the disposable repository,
including the retained review. Their paths and bytes matched the approved
preview. The complete wrapper exited successfully after 34.7 seconds. Cleanup
took 0.11 seconds, with no survivors or tmux session.

The actual post-application and post-cleanup snapshot passes the write check.
Removing the tmux rule fails on exactly `pair/tmux.json`. No arg0 entries remain
after the three implementer invocations; the three removals are recorded as
home observations. The earlier authenticated snapshot replay remains covered
by 30 controls, including cache additions, changes and removals and strict
credential/settings/session/workspace/target boundaries. New or retargeted
escaping symlinks still refuse. The exception changes write auditing only.

This is net-snapshot evidence, not continuous tracing. Synthetic quality wrappers
prove lifecycle plumbing, not real-project quality gates. Scripted clients prove
delivery and recovery mechanics, not whether a real model will discover the
correct operations or make sound semantic judgments.

## Failures, accounting and review

Failed attempts remain intact. The first five-turn run closed successfully but
an added recurrence audit incorrectly reused the smoke's success-only parser.
The corrected audit was replayed against those retained outputs before the owner
authorized another attempt. That attempt stopped on the argv exec race during
reviewer startup. After the reviewer supplied the offline diagnosis and the
deterministic fix passed, the owner authorized the final successful attempt.
No failed run is relabelled as passed.

Sixteen native invocations were charged, including failures, against the
owner-amended ceiling of sixteen. Non-inference status commands are separate;
all work stays within the eight-hour active bound. No real login, provider call,
game edit or live grant occurred. The owner's head, working files and four
stashes match the protected baseline. Private records retain exact timing,
source hashes, invocation receipts, raw streams, failure controls and cleanup.

Before the fixture correction, the structured suite passed on macOS arm64:
409 tests, one opt-in skip.
An earlier full-suite run failed the synthetic same-status notification race
test with a fake-client exit. Review subsequently confirmed the cause: its fake
client treated `REVIEW_STATE_BUSY` from a concurrent watcher poll as fatal.
The loaded control reproduced that error in one of 20 runs before the fix.
Both fake clients now retry only that exact error for at most five seconds;
other errors still fail immediately. A deterministic test covers successful
retry, the deadline and refusal to retry other errors. Production code and the
native acceptance evidence are unchanged. The failed runs remain retained.
The same loaded loop passed 20 of 20 runs after the fix: four parallel workers
with separate scratch locks, five runs each, both race tests in every run.
The structured suite then passed once on the corrected fixture: 410 tests,
one opt-in skip, in 232.1 seconds on macOS arm64.

The `make test` result is carried forward from `061cf1726`: playbook and
repository-hygiene gates, 692 shell tests and 1,206 Java tests passed on macOS
arm64. The documentation gates were rerun after the final result-text edit.
Exact logs and receipts are in the review packet.
Code review comes before publication; Linux and macOS CI on the final head come
before merge. After merge, fresh preparation and a reviewed packet precede the
separately authorized single unscripted pass. There is no automatic pass two.
