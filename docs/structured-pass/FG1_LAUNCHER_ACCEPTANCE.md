# FG-1 launcher and client admission: accepted

19 November 2026. Independent review accepted the r5 live result at code head
`1df4aaeca`. **FG-1 step 3, launcher and client admission, has passed.** This is
the bounded milestone in the [launcher slice](FG1_LAUNCHER_SLICE.md), not step 3
of the broader [rollout plan](ROLLOUT_PLAN.md). It does not complete a game pass
or make structured operation the default.

## Delivered capability

The opt-in [supervised pair](STRUCTURED_PAIR.md) connects the existing service,
handoff watcher and adapters for Codex implementer / Claude reviewer. It carries
recorded messages, resumes Codex on the same thread, checks shared expiry before
spawn, and classifies handoff or unfinished work from authoritative service
state. Transient locks keep polling; a notification superseded during a turn is
recorded and dropped before consuming an invocation.

Admission exposed two production gaps that are now corrected. Codex receives
selected images through the [fixed-ID facts route](FACTS_IMAGE_ROUTE_RESULT.md),
with no native image-tool or code-mode grant. Both clients receive generated
[argument keys and identity sources](ARGUMENT_CONTRACT.md) from the dispatch
contract. These changes preserve role, input-integrity and response-size checks.

## Live evidence

The owner authorized manifest
`1282628167c0398a8fcea49c3485d171d24fb3a6db03a05bb9832026889c89cd` after packet
review and completed isolated login before the clock. The four-phase recipe had
first run against the pinned clients on loopback through the real watcher. Its
scripted identity resolver read the delivered contract; the live run used real
models. The live attempt took **84.608 seconds**, with zero retries, within the
1,800-second shared and 300-second per-invocation limits.

| Phase | Tool calls | Observed result |
| --- | ---: | --- |
| Claude with the hook disabled | 11 | Eight protected Reads denied by the restricted-path check, including an alternate spelling; two permitted media Reads and facts status succeeded. Zero hook rows. |
| Initial Codex turn | 9 | Inputs, image and visual answer succeeded; preview, confirm, validate and publish completed. Both candidate-consuming calls used the returned identity as `cid`. |
| Notified Claude review | 6 | Five facts calls and one permitted image Read; two review pages, correct visual answer and accepted request-changes. Six hook allows, no denials. |
| Notified Codex resume | 2 | Same thread, changed message; status and complete retained report read; deliberate unfinished stop. |

The eight denial events each match a real Read by call ID and name, with reason
`--restricted: path outside the working directory`. Error text alone, a model
refusal, a missing file or don't-ask mode does not count as this boundary evidence.
This closes the previously open hook-disabled item for the exercised paths and
pinned client. It does not establish protection for every client-owned exemption.

Both visual answers matched the private illustration key after image access.
Codex's full native session output held the exact selected 1,268,179-byte PNG;
its truncated stdout representation was not used for the byte check. No answer
key, reference payload, project identity or personal path is included here.

Two accepted notifications produced turns `handoff`, `handoff`, `unfinished`.
The final handoff was `CHANGES_REQUESTED`. There was no approval, closeout,
application or game work. All four shared-lock receipts finished with exit zero.
No client approval prompt, routine tool refusal or coordinator busy refusal was
observed. Cleanup took **0.083 seconds**; recorded process identities and the tmux
session were gone. Seven protected canaries and the owner's working state were
unchanged.

## Pins, usage and retained records

The tested clients were retained outside package-manager installation folders:
Codex **0.167.0**, `gpt-6-astra` / `xhigh`, and Claude **2.1.319**,
`claude-opus-5-5` / requested `high`. Codex's native turn contexts attest its
selection; Claude's initialization and assistant messages attest the model,
while effort remains a launch setting. Claude offered Read plus facts, in
`dontAsk` with no additional directories. Codex's native declaration matched
`43fb852102975edfb7bda7a4def191e98bd1a29d40a03583bf3c376cb9551584`.
The three service declarations are recorded in the
[identity-source contract](ARGUMENT_CONTRACT.md#identity-sources-19-november).

Claude charged 3 and 5 responses, **8 of 40**. Its two runs reported respectively
1,150 and 1,323 output tokens, with 0 and 260 thinking tokens. Codex's final
cumulative counters were 206,380 input tokens, including 184,832 cached input,
803 output and 57 reasoning output. Resume added 60,358 input and 67 output.
Cumulative completions are not additive; the increments reconcile against
native per-request usage. These trivial scripted-task figures **must not be used
to estimate an unscripted pass**. No inference-cost saving is claimed.

Private packet `fg1-launcher-smoke-r5-20261119` retains the authorization,
streams, native sessions, phase reducers, image check, usage, notifications,
receipts and cleanup. The reviewed post-run evidence index is
`a14c0dbd4dd5711d884cf134181bea23f12060e4767197be4f418dd04a8af587`.
Earlier unsuccessful attempts remain preserved; this acceptance does not
retroactively pass them.

Two sealed internal runtime files changed: editor state and the handoff Git
exclude file. The latter gained exactly the standard ignore block installed
when the first handoff is initialized. Four external runtime pins changed:
pair state, implementer state and two Claude budgets. All other pinned files
held. The unsealed reporting helper initially missed the exclude change and
summed cumulative token counters. Its correction record preserves both errors;
no sealed reducer, prompt, rule or live result was changed.

After result acceptance, all twelve isolated profiles from the four live smoke
packets were checked and logged out using their native clients. The first two
packets were already logged out; the last two still had active logins. Status
before and after was recorded without credentials or account details. Logged-out
configuration homes were removed, and the remaining temporary roots were moved
to private retained storage with byte checks. Existing packet seals remain
historical identities; relocation records explain their retired external paths.

## Remaining boundary

The [retrospective](../retros/2026-11-19-structured-launcher-admission.md) records
the engineering and coordination lessons. The charged effort through accepted
live result was **32,142 seconds, about 8 hours 56 minutes**, against 16 hours.
It is conservative recorded effort, not a precise time sheet; final upstream
preparation and checks are recorded separately. The PR must carry final-head
structured and repository-suite results before merge.

This smoke establishes the exercised access, readability, identities, notification
and resume path on one pinned configuration. It does not prove an unscripted
semantic corridor, real-game gate outcomes, sustained context/compaction,
runtime-worker integration or native-client OS confinement.

After upstream review, the separately scoped readiness check must:

- Resolve reviewer-accessible sources for candidate, revision and validation
  attempt identities on operations the real pass may need. The live coverage
  head/base sources worked; that does not close every reader identity.
- Distinguish handoff round from verdict sequence with a multi-round contract
  test. The current single-round lifecycle cannot distinguish their equal values.
- Respect the 4,096-character description limit. Implementer top-level help is
  4,027 characters and its argument contract is 3,586; do not silently truncate.
- Derive expected runtime changes from a rehearsal on the actual prepared layout,
  including handoff initialization, rather than an assumed file list.
- Refresh preparation and the complete input/write/closeout/application matrix,
  then obtain separate authorization for one unscripted pass. Operator-selected
  corridor and analogues remain explicit manual setup.

No parked item is implemented by this acceptance record. The objective remains
one substantive unfamiliar-game pass with independent review and local application,
without coordinator content repairs. Conditional runtime, policy-writing and
other missing operations retain their existing stop rules.
