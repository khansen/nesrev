# Slice 3: preserve learning candidates through structured closeout

15 November 2026. **Proposal; implementation not authorized.** Input delivery
merged in [PR #195](https://github.com/khansen/nesrev/pull/195); its
[retrospective](../retros/2026-11-15-structured-input-delivery.md) records the
outcome and limits. The destination remains [one complete first semantic
corridor](FRESH_GAME_PASS_SCOPE.md), not completion of the validation game.

## Outcome and reason for doing it next

Unresolved process observations from either role must survive review, closeout
and application in the existing project friction queue, without the owner
copying prose between files. Empty observations must remain a normal no-op.
Import creates candidates for later triage, never new implementation work or
policy automatically.

The [post-intake measurement](FRESH_GAME_PASS_MEASUREMENT.md#dependency-matrix)
found this need in the retained trial and the new intake. The ordinary
[`update_process_friction`](../../scripts/agent_review.py) already collects
learning sections, filters receipted content and updates the queue. Structured
[`archive_document`](../../scripts/structured_pass/structured_handoff.py)
retains verdict reports, but neither structured
[closeout](../../scripts/structured_pass/launcher.py) nor
[application](../../scripts/structured_pass/application.py) imports their
learning sections. Application currently transfers generation changes and the
review archive only. First-publication implementer observations also need an
explicit retained source; a reviewer report alone cannot stand in for them.

This is the import subset of [D9](STEP_2_COVERAGE.md#documents-ledgers-and-trusted-writes),
not completion of its entire import/triage operation. The existing operator
[triage and receipt workflow](../../agent_playbook/PROCESS_FRICTION.md) remains
unchanged. No autonomous triage, receipt editor or general root-document route
is proposed.

| Alternative | Effect on the first complete pass |
| --- | --- |
| Fixed import at structured closeout/application | Reuses existing identity and receipt rules; removes a known manual transfer before the live run. Recommended. |
| Launcher first; leave observations in reports | Makes a loop available sooner, but leaves the known queue-transfer gap or requires owner/coordinator file edits. The accepted launcher estimate remains 8–16 hours. |
| Coordinator invokes ordinary import manually | Useful implementation reference, but a bespoke step would remain in every closeout. Prefer making that same fixed action part of the service lifecycle. |
| Return to the ordinary workflow | Already imports candidates, but does not test the structured process selected for FG-1. |

## Narrow contract

At the first checkpoint, freeze the mapping from each role's observations to
retained artifacts. Include the implementer's initial observations, rework
responses and all recorded reviewer verdicts; do not read arbitrary host paths
or rely on a final transcript summary. Reuse existing report/response fields
where they suffice. If initial implementer observations need a new field or
operation, admit only bounded text with role, run and generation supplied by
the service. It cannot edit a verdict, impersonate another role or choose a
destination. Retain the original bytes and their hashes.

Use the ordinary learning-section parser, content identity, receipt filtering
and queue writer rather than a second interpretation of candidate text. Keep
project, pass, source artifact and archive provenance. Candidates from rework
remain evidence; they are not accepted rules. Existing manual queue text and
receipted entries must survive unchanged. No candidate quota or semantic
deduplication is introduced.

Freeze the derived queue update with the approved closeout evidence, and carry
it through the trusted application journal with the archive. Check source hashes,
queue and receipt preimages, current generation and approval before applying.
A conflicting target edit must refuse, not overwrite. Interrupted application
must be recoverable without duplicate imports or a success receipt for missing
output. Repeated closeout/application of the same evidence must be idempotent.
Rebased source commits must not recreate already-triaged content, using the
existing project-scoped content identity.

Only the fixed wrapper owns queue/receipt content. Ordinary document operations
continue refusing those paths. Import must not manufacture triage receipts or
change dispositions. The initial design may use a private derived closeout
artifact rather than a new agent-visible queue mutation; freeze that choice at
the checkpoint before extending application.

## Offline acceptance

- Through both role bridges, retain one implementer observation before any
  rework, a response observation and observations from a requested-changes and
  an approving review. After restart, complete closeout and apply to a disposable
  checkout. Every intended candidate and its original source evidence survives.
- Use retained workload examples privately, plus committed project-neutral
  fixtures. Compare candidate identities and queue output with the existing
  ordinary importer; do not duplicate its normalization logic as the oracle.
- Explicit empty observations create no queue work. Repeating import, closeout
  and application creates no duplicates. Previously triaged content stays out,
  including after changed run IDs or rebased commit IDs; genuinely new content
  stays discoverable.
- Preserve unrelated manual queue content and existing receipts. Refuse malformed
  receipts, forged identities, altered source text, wrong role/run/generation,
  stale approval, arbitrary paths and overlapping target edits before committing.
- Inject failure between writing the derived queue/archive and recording or
  committing application. Retry must finish the same recorded write set exactly
  once, or refuse with recoverable evidence; never silently drop observations.
- Deliberate controls must catch omission of implementer-only evidence, bypassed
  source hashes, disabled receipt filtering, duplicate-on-retry and a dropped
  queue write. Keep existing structured approval, application and ordinary
  friction tests passing. Do not change semantic gates or client permissions.

This proves fixed lifecycle behavior offline. Actual unsolicited observations,
agent compliance and intervention cost remain live-pass measurements. It does
not prove autonomous triage or unattended recovery across every failure class.

## Estimate, checkpoint and stops

**Estimate 2–4 active hours; hard bound four hours; offline only; one review
round.** The estimate is inherited from the dependency measurement, not measured
implementation cost. Record actual effort and separate waits. No provider calls,
live clients, semantic pass, installation or changes to the owner's project.

**At one active hour, or earlier if decisive:** show all observation sources,
their retention/authority mapping, the proposed derived output and application
write set, and the smallest failure/retry fixture. Stop for a decision if a
source cannot be retained or the application design requires a new transaction
framework. Do not spend the remaining allowance widening this slice.

Also stop on a new capability dependency, a second failure of the same unresolved
class, the review-round limit or the four-hour bound. General triage tooling,
policy promotion, queue cleanup across the corpus, unrelated article checks,
search redesign, runtime workers and workspace orchestration remain outside.

After acceptance, the next dependency is the launcher and client admission,
then one separately authorized unscripted pass. Remaining conditional ranges are
2–4 hours here, 8–16 for the launcher and 4–8 for integration: **14–28 active
hours**, excluding new dependencies, external review/owner waits and live runtime.
These are planning ranges, not authorization or a completion promise.
