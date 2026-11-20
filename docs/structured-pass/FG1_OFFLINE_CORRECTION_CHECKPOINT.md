# Offline correction: early implementation checkpoint

20 November 2026. **Stopped for reassessment; not ready for publication or a
new live grant.** This is an early checkpoint against the
[approved scope](FG1_OFFLINE_CORRECTION.md), not completed acceptance.

Two offline executions failed when their process supervisor tried to execute
`/bin/ps` inside the explicit loopback-only network sandbox. The second attempt
used escalated outer execution and failed the same way. It reached the actual
wrapper and completed both native pre-window status checks, but started no
inference turn. The scope says a repeated failure class stops for reassessment;
no replacement native attempt followed.

The executable has a set-user-ID mode. Its interaction with this sandbox is a
possible cause, not an established diagnosis. The first failed capture left a
client process that was identified and terminated separately. The second
attempt's cleanup also hit the process-inspection refusal; subsequent cleanup
outside that sandbox found no survivors or tmux session. These failed runs and
the later reconciliation records are retained separately.

## Implemented, with acceptance still incomplete

The uncommitted implementation now generates an `operation-reference` input
from dispatch-owned field tables. It covers all 18 accepted edit kinds,
conditional and nested fields, query shapes, document choices, and argument
classifications for corridor implementer, corridor reviewer and retained
`source-v2` reviewer. The record uses the existing capture, hash and paged-read
paths. A restored-read test checks its contents and rejects changed bytes.

Corridor profiles no longer offer the duplicate `guidance` route. The retained
profile still offers it with its owner's accepted names. Static tests catch a
missing required-argument classification, a missing edit kind or nested field,
and a changed owner schema. They do not establish that every declared source is
reachable in every lifecycle state; that remains part of final acceptance.

The provisional public-error map contains 47 correctable, 3 transient and 152
terminal codes; unknown errors remain terminal. The bridge supplies
`error_class` and safe argument diagnostics. Focused tests cover correction
after a malformed call, a transient busy refusal and a terminal integrity
refusal. Field-level diagnostics are not yet complete across all scalar/value
checks. The final task wording and repeated-correction friction report also
remain unfinished. This is not yet the complete actionable-error contract.

A direct synthetic lifecycle exposed another real source-mapping defect:
after a second publication, the review operation needs each adjacent required
edge, rather than the entire pass base-to-head comparison. Its delivered
sources now select ticket/head/base from the same
`status.handoff.coverage.required_edges` pair. A test publishes two generations,
uses those advertised paths, and fails when the old pass-base mapping is
restored. This changes help and its pin, not review access or dispatch keys.

The reference also explains an existing condition: `validation_evidence`
provides failure diagnostics; successful gate results are in
`candidate_status.gates`. The synthetic recipe uses that existing successful
result rather than treating unavailable failure evidence as a missing feature.

## Measured delivery and size

| Profile | Top description | Argument description | Tool listing bytes |
|---|---:|---:|---:|
| Corridor implementer | 4,027 / 4,096 | 3,815 / 4,096 | 8,854 |
| Corridor reviewer | 3,403 / 4,096 | 3,106 / 4,096 | 7,344 |
| Retained reviewer | 1,211 / 4,096 | 2,278 / 4,096 | 4,137 |

Removing corridor `guidance` recovers 123 characters in the argument contract
and none in the top-level help. The new reference/recovery instructions and
review-edge sources use part of that space. No size limit changed.

The generated synthetic reference is 58,948 bytes. Both corridor roles read it
byte-for-byte through the actual bridge: 15 pages at the default 4,096-character
page size, or 8 pages at 8,192 characters. The largest measured wire response is
11,344 bytes, below 24 KiB. These are whole-reference downloads, not search
questions credited against the eight-request search limit.

Projection onto the accepted input inventory gives 21 text items of 32 allowed,
622,480 aggregate text bytes of 2 MiB allowed, and a 59,676-byte reference below
the 256 KiB item cap. The catalog would have 29 records: three default pages or
one page with limit 40. This is an inventory projection, not fresh real-project
preparation.

The pinned native implementer delivered the updated declaration exactly; its
new hash is
`450e64f25b89c9f4c33cdf9420c8f1e182e1ab17fbd031c21a202f855fcd63ff`.
The native fixture and code pin were updated together. The reviewer capture
failed in supervision and is not credited. Its committed fixture is therefore
still stale. Neither changed declaration is live-admitted.

## Write rules and the smallest positive control

The fixed replay of the spent attempt's original snapshots and bound identities
passes the proposed rules. The explicit launch rule accepts `pair/tmux.json`;
the model-cache addition and three arg0 entry removals are recorded for review.
No unknown change remains outside the isolated non-credential home exception.
Thirty controls cover that replay, removal of the tmux rule, cache additions,
changes and removals, protected paths, and escaping-link additions/retargets.
The replay fails without the tmux rule. The old packets are unchanged.

A five-phase direct bridge recipe completed publication, requested rework,
second publication, approval and closeout, then applied to a disposable
synthetic repository. It used 39 calls and the actual service, handoff, archive,
import and application code. Quality wrappers were synthetic. It did not use
native clients, the watcher or the tmux entry and is explicitly insufficient
to satisfy the scope's full-wrapper positive control.

The attempted full wrapper retains the spent wrapper bytes and uses real
pre-window native status checks. Its explicit substitutions are a disposable
synthetic target, offline authority for that target only, dummy authentication,
scripted loopback transport and the proposed write policy. Authentication was
not bypassed. Both pinned clients' actual status commands accepted the dummy
setup without provider traffic. Process supervision then failed before native
inference. The final `layout.check` positive control remains **not run**.

The arg0 result is also **unproven**. Three entries created by pre-window status
remain after cleanup: one lock and two launcher symlinks. No three-implementer-
turn sequence occurred, so this checkpoint cannot claim those entries disappear
after a complete run. Adding or retargeting escaping links remains a refusal.

## Tests, accounting and continuation

The eight focused discovery tests pass. The full structured suite on the
checkpoint implementation ran 400 tests in 199.9 seconds: **3 failures, 1
opt-in skip**. Its failures are retained:

- the native reviewer capture fixture is stale;
- an existing exact-error assertion still expects the old payload;
- an unpaged oversized response receives generic correction advice, contradicting
  the existing no-action contract. Class and advice must reflect whether the
  caller has a possible correction, rather than merely changing the assertion.

No repository-wide green claim is made. Repository gates and final fault
acceptance remain outstanding. Implementation, tests and checkpoint docs are
uncommitted; nothing was published. The protected checkout and four stashes
match the baseline. No live credentials or real project content were changed.

Three of ten native inference-loopback invocations are charged: two successful
implementer declaration captures and one failed reviewer capture. Four native
status commands are separately recorded. The wrapper consumed no additional
inference invocation. Provider calls are zero. The private effort record charges
the full work interval, including checkpoint reporting; no approval wait is
excluded. Seven invocations remain, including the five required for the full
recipe.

Before another native invocation, reassess the supervisor's process-inspection
failure with a no-inference probe. Any revised isolation must preserve the
loopback-only network boundary and reliable process reconciliation. Then use
fresh disposable preparation, complete the reviewer capture, and run the real
wrapper positive control with the arg0 check. Finish the diagnostics, task and
friction reporting, resolve the suite failures, and run final acceptance before
publication. Estimated remaining work is 3–6 active hours, conditional on that
supervision diagnosis; it is not authorization for an extra attempt or broader
boundary. The existing hard time and invocation bounds remain unchanged.
