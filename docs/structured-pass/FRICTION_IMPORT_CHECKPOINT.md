# Friction import: first checkpoint

15 November 2026. The owner authorized the four-hour offline slice. This is
the requested first checkpoint, reached before one active hour. **Recommend
continuing with the contract below; production integration had not begun at this checkpoint.**
The [scope](FRICTION_IMPORT_SLICE.md) and one-review-round limit remain in force.
The owner subsequently authorized continuation; the
[implemented contract](FRICTION_IMPORT.md) reuses the canonical instruction text
as requested in review.

## Decisions

Use the existing candidate-closeout operation for implementer observations,
the existing review/report and rework-response routes for the other sources,
and the existing ordinary importer for parsing, identity and receipt filtering.
No new agent operation or general file writer is needed.

Freeze observation sources at closeout, **not the target queue bytes**. At the
start of application, rebuild the import against the current target queue and
receipts. Then freeze that derived write set in the existing application journal.
This replaces the proposal's stale closeout-time queue preimage: intervening
triage is preserved without copying observations by hand.

## Observation sources and retention

| Source | Submission and authority | Retained evidence for import |
| --- | --- | --- |
| Initial implementer observations | Required `learning` field on the `kind: closeout` operation inside implementer `preview`; use the same preview/confirm/validate/publish lifecycle. | Copy the exact body into the generation's `closeout.json`, which already travels through capture hashes and immutable publication. The field is authored evidence, never a wrapper result or quality claim. |
| Later published implementer observations | The same field on each published candidate. | Walk the current pass's published ancestry, verifying each capture. Do not silently replace earlier observations with the last candidate's body. Rejected/unpublished candidates are not imported as completed handoffs. |
| Reviewer findings | Existing `approve.report` and `request-changes.report`, with an explicit learning section. | Existing verdict history already pins each report's bytes and identity. Include requested-changes and approving reports; neither grants automatic triage authority. |
| Implementer rework response | Existing `reready.response`, with an explicit learning section. | Responses already have immutable hash-named files under `responses/`. Add accepted response references to the existing handoff state under its lock, including round/head identity; `last_response` alone is insufficient for multiple rounds. |
| No observations | Explicit `_None._` in the field or section. | Retain that declaration and distinguish it from absent input. It creates no queue candidate. |

The ordinary importer currently globs `response-*.md`; structured responses are
in a subdirectory. The integration must supply the checked source set explicitly,
not assume those globs cover it. Orphan files from an interrupted state write
must not become accepted observations merely because they exist.

Do not import historical intake archives, earlier run context, arbitrary session
files or rejected candidates. There is no new coordinator-observation route.
If one becomes a concrete FG-1 requirement, return to the owner rather than
inventing another source. Existing sessions lacking required declarations must
report missing evidence; do not synthesize `_None._` for them.

At closeout retain the complete source list, original text, role/run/generation
or verdict identity and content hashes. Include implementer and response evidence
in the durable archive as well as the already archived reviews. Import uses the
indexed originals, not a second parse of the combined archive that could count
the same text twice. Preserve the normal importer semantics for repeated content.

## Exact role instructions and refusal checks

The checkpoint initially proposed the following implementer wording:

> In `preview.operations`, every `kind: closeout` object must include `learning`:
> the body of your Learning Candidates section. Record unresolved process or
> tooling observations, without requiring a proposed fix. Use exactly `_None._`
> when there are none. The service adds the heading and retains this with the
> candidate; do not write PROCESS_FRICTION.md or receipts yourself. A
> `reready.response` must include `## Learning Candidates` with observations or
> `_None._` as its only body.

The checkpoint initially proposed the following reviewer wording:

> Every `approve.report` or `request-changes.report` must include
> `## Learning Candidates`. Record unresolved process or tooling observations;
> use exactly `_None._` as the body when there are none. These are candidates
> for later triage, not approval to implement a fix or promote a rule.

The accepted review refined both declarations to reuse the existing
`LEARNING_CANDIDATE_GUIDANCE` string verbatim, including “record a recurrence only
when it adds new evidence” and the `_None._`-alone rule. Both add “Don't repeat
observations you already submitted in this pass.” The implemented help then
names each role's existing submission routes, as above.

Check both actual `tools/list` declarations offline. Reject missing fields,
missing sections, empty bodies and headings found only inside fenced examples
before changing the accepted candidate, verdict or response state. Use the
existing structural-line and learning-section helpers; do not add a competing
Markdown parser. New refusal tests must distinguish explicit emptiness from
failure to submit an observation source.

Proposed implementer field cap: 4 KiB of JSON-encoded text, with no truncation.
Seven retained source files had nonempty learning sections; the largest was
1,418 UTF-8 bytes, or 1,444 JSON bytes. This is a measured sizing basis, not proof
that every future observation fits. Keep the existing 64 KiB report/response
limits. Check complete preview/review replies against the unchanged 24 KiB wire
ceiling; if preserving required evidence needs a larger interface, stop rather
than silently cutting text or raising the ceiling. Live client declarations
must be re-pinned later; none is installed by this slice.

## Application write set and queue edits

Application continues to write the approved generation delta and canonical
review archive. It additionally writes `PROCESS_FRICTION.md` only when the
ordinary importer derives a changed queue. Receipt files are read and validated,
but neither edited nor committed by import. The application journal records the
source-bundle hash, current queue/receipt preimages and derived queue hash.

Build in private staging from frozen sources plus the target's current queue and
receipts. Recheck all preimages before writing. A valid queue triage or manual
edit between closeout and this planning step is accepted as the new input;
already-triaged observations stay filtered. Uncommitted queue edits must not be
silently included in the pass commit: refuse them with an explicit commit-and-
retry instruction, then rebuild from the committed queue without hand copying.
Malformed receipts still refuse. Ordinary document routes still cannot edit
these artifacts.

Once application has started, retries use its exact frozen write set. Keep
existing partial-write and commit-receipt recovery, and refuse conflicting
mid-transaction edits. Do not rebuild over partially applied outputs. The
existing one-writer-per-project rule still applies; this slice adds neither a
distributed transaction nor concurrent triage support. A changed queue before
application is distinct from a changed queue during an unfinished transaction.

## Component evidence and smallest integrated test

The private packet `fg1-friction-import-20261115` pins the approved code,
producer and probe. Production code and the main checkout were not changed.
Two independent probes passed:

- The unchanged ordinary importer rebuilt from frozen implementation/review/
  response files after triage deleted an old queue and a manual entry was added.
  It retained the three new observations plus the manual entry, filtered the
  triaged candidate, left receipts and source hashes unchanged, and produced
  byte-identical output on repeat. An injected atomic-write failure preserved
  the prior queue; retry produced the same output.
- The unchanged structured application journal recovered after Git committed
  successfully but the final application-receipt write was deliberately failed.
  Retry recognized that same commit; another retry returned the same result
  without an extra commit. The standard fixture uses simulated quality gates
  and real native certification. Its write set does not yet include a queue.

These are component probes, **not integrated D9 acceptance**. The smallest new
integrated fixture must combine them: submit all role sources through bridges,
close out, triage and commit an existing queue entry, apply the rebuilt import,
interrupt before/after the queue write and after commit before receipt, then
retry. Require one final commit, the expected candidate/source identities,
unchanged receipts/manual content and no re-import of triaged work. Missing
sections and `_None._` take separate refusal/no-op paths. Preserve all failures.

The importer and application journal are reusable without a new transaction
framework on this evidence. The next implementation checkpoint is full offline
acceptance within the remaining four-hour allowance. A new dependency or a
failure that invalidates these decisions still stops the slice early.
