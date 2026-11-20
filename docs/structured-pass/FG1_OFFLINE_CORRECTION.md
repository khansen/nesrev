# FG-1: offline correction before another pass attempt

20 November 2026. **Offline implementation authorized within the bounds below.**
The owner approved implementation after review of the amended scope. The
client-home write policy below is authorized; another live attempt is not.

The [offline result](FG1_OFFLINE_CORRECTION_RESULT.md) now includes the complete
native wrapper through application. The [early checkpoint](FG1_OFFLINE_CORRECTION_CHECKPOINT.md)
and [continuation checkpoint](FG1_OFFLINE_CORRECTION_CONTINUATION.md) preserve the
failed attempts and owner-authorized corrections. Code review, repository gates
and both CI platforms precede merge; a live pass still requires a fresh grant.

The [readiness work](FG1_READINESS_RESULT.md) merged in PR #198. The subsequent
authorized unscripted attempt stopped after four facts calls, before any
candidate, review or application. The catalog supplied the guidance inputs,
but the implementer guessed an unsupported name on the separate `guidance`
route. Its refusal repeated the argument keys without explaining the value,
and `retryable: false` was interpreted as requiring a stop. Post-run inspection
also found that the write rules omitted the launcher's own `pair/tmux.json`.
The accepted private result seal is
`b6003834b54b9e7f05508e0da1a9f2e86c9336a99e2395731f3614b1fefcd7cd`.
The grant is spent. The protected checkout is unchanged.

## Outcome and bound

Remove these three measured blockers before requesting the same single
unscripted pass again. Completion means discoverable arguments, actionable
refusals and a successful offline run through the actual launch/application
path. It does not establish real-model understanding or semantic-pass success.

**Estimate: 4–8 active hours; hard bound 8; checkpoint at 2 hours; one review
round.** This is a judgment estimate, not a forecast from smoke usage. Record
active work, execution and waits separately. The original native allowance was at
most **10 credential-free inference loopback invocations**, at most 300 seconds each,
using only scripted responses on loopback and no provider calls. Failed
invocations count. Budget five for a complete rework/approval/closeout recipe;
the remainder covers declaration captures and explicitly diagnosed corrections.
There are no automatic replacement attempts, and a repeated failure class stops
for reassessment. Native pre-window `login status` commands perform no inference;
they are recorded separately and excluded from the ten, but their execution
counts toward the active-time bound. No account login is needed or authorized.

The owner subsequently authorized the Darwin libproc/sysctl supervisor change
and two specific fresh recipes, raising the total invocation ceiling first to
14 and then to 16. The final result uses all 16, including failures; it grants
no further invocation. The eight-hour bound and no-provider restriction remain.

The alternative is the ordinary attended workflow. Patching the next live task
with another argument hint leaves the reusable service defect in place. A new
scheduler, analysis engine or broader worker boundary is outside this slice.

## 1. Complete the delivered argument contract

Extend the shared [contract generator](../../scripts/structured_pass/operation_contract.py)
and its dispatch-owned definitions across corridor implementer, corridor
reviewer and `source-v2` retained reviewer. Every required argument must identify
an authored value with its type/constraints, a reachable source in that role's
own results, or an enumerated accepted set. Include conditional requirements
and required fields inside structured queries and edit operations. Calling an
opaque JSON object "free text" does not satisfy this rule.

**Chosen edit-operation route:** generate an `operation-reference`
record from the owners' per-kind field definitions and deliver it to the
implementer through existing `inputs`/`input` pagination. Convert inline shape
checks into shared data that dispatch itself enforces; the reference is generated
from that data, with no second schema. Cover every kind accepted by `preview`,
including the authored-document and mixed families, exact field sets, conditional
fields, nested shapes and value sources. A coverage test must fail if an accepted
kind or shape has no matching reference entry. Pin and capture the generated
record with the declared inputs so it survives restoration. Existing catalog,
item and response limits still apply; pagination is not a limit exemption.
Test that the catalog advertises the ID and paged reads reconstruct the generated
reference exactly, including after restoration.
The declaration needs only a short pointer to this fixed ID, available before
the first `preview`. Correctable errors are backup guidance, not the primary
delivery route. Reviewer permissions remain unchanged.

Propose removing the redundant `guidance` operation from the two corridor
declarations and dispatch profiles: fixed-ID `input` already supplies the
declared guidance. Retained guidance must expose the accepted names from
[its existing owner](../../scripts/structured_pass/guidance.py). Inventory
`document.path`, navigation/evidence views and their conditional selectors as
well as identity arguments. A source must be reachable from that profile;
another role's transcript or an undocumented path convention does not count.

A static coverage test must fail for any offered required field lacking this
classification. Couple enums and shape constraints to dispatch, and retain
real lifecycle tests that resolve advertised sources from separate role
histories, including multiple review rounds. Mutations must catch an omitted
field, a changed accepted value set and an inaccessible or wrong source.
Do not create a second hand-maintained schema merely to make the test pass.

Keep each description within 4,096 characters and the tool listing within its
existing byte cap. Measure the complete representation at the checkpoint:
the implementer's top-level description currently has only 69 characters free.
Report the space recovered by removing corridor `guidance` as well as the final
sizes, including the reference pointer. Shorten repetition, not required
instructions. Capture both pinned clients' delivered declarations and refresh
native fixtures and all affected service
pins together. Loopback proves delivery, not model comprehension.

## 2. Make refusals actionable

Classify every public error deliberately: **correctable** means change the
request, **transient** means retry unchanged within the deadline, and
**terminal** means stop. Unknown/internal errors remain terminal. A test must
flag any newly added public code without a classification. Schema and value
errors must name the offending or missing field and its accepted values,
constraints or delivered source, using the same definitions as dispatch.
Do not echo sensitive payloads or disclose forbidden paths in diagnostics.

Update tool instructions and the pass task to distinguish correcting one's own
malformed request from retrying a client invocation. The former is allowed
within the existing turn and budgets; the latter still needs authorization.
The new error class decides behavior, whether the legacy `retryable` flag is
retained or removed. Report repeated identical correctable refusals as friction
from the retained call records; this does not authorize replacement invocations.
Preserve access, integrity, freshness and quality refusals; ordinary validation
failure still follows the existing candidate-rework workflow.

Controls must demonstrate a malformed request followed by a valid correction,
an unchanged retry for a busy lock, and a terminal boundary/integrity refusal.
Exercise field-level diagnostics for the failed guidance case where that route
remains offered, plus wrong enum, missing key and extra-key cases.

## 3. Derive write rules from the actual wrapper path

Use disposable synthetic repositories and isolated dummy client homes to run
the next packet's `run_pass.py` entry path: native pre-window status checks,
detached tmux launch, real watcher notifications, review/rework, closeout,
application and cleanup. Include Git metadata and first-use initialization.
Only the scripted API transport and dummy authentication setup may differ;
list those differences explicitly. Do not bypass status, tmux, audit or
application to obtain a pass. If the native status path cannot run offline,
report that limitation at the checkpoint before treating a substitute as proof.

Record before/after path classes relative to each root, with the observation
supporting each rule. This includes `pair/tmux.json`, native pre-window writes,
the standard Git exclude append, archives and import/application recovery.
Existing component evidence may support unchanged internals, but cannot replace
the positive control: **the complete wrapper run must pass `layout.check`.**
Removing the tmux rule must fail that control. Unexpected strict-path writes
must still fail. Net snapshots remain net observations, not continuous tracing.

**Owner-selected exception:** record added, changed and removed unknown
non-credential paths inside the isolated `auth-config` homes for review instead
of stopping the pass. This is a write-audit exception, not permission to read or
write more through agent tools.
Credentials and settings, and all workspace, session and target paths, remain
strict, including protected paths nested under those homes. Define protected
path classes before the run; ambiguous paths and special files do not qualify.
Adding or retargeting an escaping symlink remains a stop. Removal of the recorded
arg0 launcher symlinks is reviewed as removal of those directory entries, without
following them or granting access to their targets.
Retain path/change metadata without credential contents.
Controls must accept and report cache additions, changes and removals while rejecting
credential, settings, session, workspace and target changes. The spent packet's
rules and results stay unchanged.

Add a fixed authenticated-home regression control using the spent r2 attempt's
`live/LAYOUT_START.json` and the result's `LAYOUT_AFTER_CLEANUP.json`, pinned with
that attempt's original bound roots and identities. Replay those observations
through the new rules: `pair/tmux.json` is accepted by its launch rule;
`models_cache.json` and removal of arg0 `.lock`, `apply_patch` and `applypatch`
are recorded for review; no unknown change remains outside `auth-config`.
Removing the tmux rule must fail this replay. Dummy-home rehearsal does not
replace this authenticated evidence, and this replay does not replace the full
wrapper positive control.

## Checkpoint, publication and next grant

At two hours, return the complete argument coverage inventory, error-class map,
description sizes, generated edit-reference coverage and delivery, the fixed
snapshot replay result and intended native replay path, with the smallest working
positive control obtained so far and a remaining estimate. Stop for a missing
capability, required source exposure, a limit increase, a new transaction or
scheduling framework, an offline authentication obstacle, repeated failure or
exhaustion of either allowance. Do not widen the corridor or repair real project
content to make the fixture pass.

Production changes belong in a project-neutral tooling PR with the affected
tests, deliberate faults, full structured suite and required repository checks.
Review the code before publication and require Linux and macOS CI on the final
head before merge. Packet write rules and their observations remain private.
Keep the stable retained gate tools, pre-login toolchain verification, pinned
interpreter, AC power, open lid and detached `caffeinate` launch requirements.
The broader gate-tool path-selection follow-up remains separate.

After merge, prepare fresh identities and a new packet for review. The accepted
old result, both packets and their write witnesses remain available. No separate
live smoke is proposed: the next pass would be the first real-model use of the
changed declaration and recovery guidance, stated explicitly in its grant.
It requires fresh owner authorization; neither this scope nor a successful
offline rehearsal consumes or supplies that grant. There is no automatic pass 2.
