# Offline correction: continuation checkpoint

20 November 2026. **Stopped; not ready for publication or another live grant.**
The production changes pass their structured tests, but the complete native
wrapper acceptance has not passed. This record continues the
[first checkpoint](FG1_OFFLINE_CORRECTION_CHECKPOINT.md) under the
[approved scope](FG1_OFFLINE_CORRECTION.md).

## Authorization and implementation

The owner authorized replacing Darwin process inspection with libproc/sysctl.
The supervisor retains PID, parent PID, process group, start time and command
rendering. It keeps unreadable or exiting processes visible with a process-name
fallback, excludes environment bytes from argv, and raises on enumeration or
required-metadata failures. Linux retains the existing `ps` implementation.

Equivalence tests compare stable processes against system `ps`, including
spaces, tabs, newlines and non-ASCII arguments. Other-user metadata remains
visible even when argv cannot be read. Separate controls cover exited process
names and failure to enumerate. The same snapshot code runs inside the
loopback-only sandbox. These checks pass, but do not explain the later `EIO`.

The recovery rule is now explicit: unchanged-state requests with a correction
available from delivered facts or an earlier step are correctable; busy locks
are transient; access, integrity, provenance, drift, internal failures and
exhausted limits are terminal. Stale-generation and preimage mistakes have
real lifecycle correction tests. Unpaged oversized results remain terminal.
The next task wording uses `error_class` rather than `retryable` to distinguish
request correction from replacement invocations. Repeated identical correctable
requests produce payload-free learning summaries.

Both native declaration fixtures were refreshed from actual loopback captures.
The argument reference covers all 18 edit kinds and their nested shapes.
The full-wrapper implementer fetched the complete reference in eight pages
and resolved candidate identities from the delivered contract. Removal of
corridor guidance frees 123 argument-description characters; top-level help
is unchanged.

| Profile | Top-level characters | Argument characters | Listing bytes |
|---|---:|---:|---:|
| Implementer | 4,027 | 3,815 | 8,854 |
| Reviewer | 3,403 | 3,106 | 7,344 |
| Retained reviewer | 1,211 | 2,278 | 4,137 |

Each description stays below 4,096 characters. The implementer has 69 and
281 characters of headroom respectively. Existing catalog, item and response
limits are unchanged. The first checkpoint's inventory projection remains
labelled as a projection, not fresh real-project preparation.

## Native observations and stops

The first complete five-turn recipe reached publication, change request,
rework, approval and closed state through the actual tmux launcher and watcher.
It made 41 scripted facts calls, including two identical bad-preimage requests
followed by a valid correction. All five native turns succeeded. The added
recurrence audit then stopped before application: it had reused the smoke's
success-only parser, which rejects a failed tool call even when its service
result explicitly permits correction. This was a harness defect.

That run remains failed. A corrected audit was tested against its retained
streams, accepting the two correctable refusals while rejecting terminal,
unknown and transport failures. The recurrence summary records one repeated
request with count two. The original result and wrapper were preserved.

The owner then authorized one fresh five-invocation loopback, increasing the
total ceiling from ten to fourteen. Its implementer handed off, but the outer
supervisor raised `OSError: [Errno 5] process sysctl failed` during the reviewer
turn. The wrapper stopped and cleanup succeeded. No application ran. The
exception does not identify the MIB or PID, so it cannot yet justify treating
the failure as an unreadable-argv fallback.

A bounded no-inference investigation did not reproduce `EIO`: 100 ordinary
snapshots and 243 sandboxed snapshots while 679 trivial processes started and
exited completed. Expected unreadable-argv errors used the existing fallback.
This does not prove the original failure transient or safe to ignore. The
next correction needs to distinguish failed enumeration/metadata from a
failed argv read before changing recovery behavior. No new native invocation
was started after this stop.

## Write rules and cleanup

The spent authenticated-home snapshot replay passes 30 controls. It accepts
the tmux file and records the cache addition and three arg0 removals for review.
Removing the tmux rule refuses the replay. Added, changed and removed protected
paths still refuse, as do escaping symlink additions or retargeting.

The first five-turn run's actual post-cleanup snapshot also passes the write
check. Removing its tmux rule fails specifically on `pair/tmux.json`. No arg0
entries remain after the three implementer invocations. This establishes the
launch-through-closeout writes and cleanup, **not application**. A separate
direct service recipe applies successfully, but is not credited as complete
wrapper acceptance.

Both native attempts have no surviving processes or tmux sessions. Cleanup
took 0.10 and 0.44 seconds. The owner checkout's head, working files and four
stashes match the protected baseline. No provider calls or real project edits
occurred. Dummy profiles and failed evidence are retained for review.

## Verification and next decision

The final production code passed **406 structured tests, one opt-in skip**, in
195.6 seconds on macOS arm64 under the shared lock. Eight deliberate faults
were caught: terminal stale-generation and preimage responses, terminal unknown
operation, correctable unpaged overflow, a missing edit kind, a bypassed owner
shape check, dropped recurrence reporting and cleanup that falsely succeeds.
The initial fault harness tried a classification-only mutation that typed
request diagnostics correctly overrode; the corrected fault targets the
actual response. A separate harness selection mistake is also retained.

`make test` and cross-platform CI have not run for this unfinished correction.
Production and test edits remain uncommitted. The failed native result is not
overridden by the passing suite or audit replay.

Eleven of fourteen native invocations are charged. The separately authorized
fresh attempt is spent, with no automatic replacement. Approximately 1.5 active
hours have been charged against eight, conservatively including command waits;
the private timing record provides the exact handoff figure. Review the
supervisor failure before another correction round. Full-wrapper application
acceptance and the ordinary repository gates still precede publication. No
semantic pass or live grant is authorized by this record.
