# Friction-import offline acceptance

16 November 2026. Implementation of the approved
[slice](FRICTION_IMPORT_SLICE.md), following the accepted
[checkpoint](FRICTION_IMPORT_CHECKPOINT.md). The end remains one complete,
independently reviewed fresh-game corridor. This slice removes manual copying
of process observations; it does not add triage or start a game pass.

## Delivered behavior

The [contract](FRICTION_IMPORT.md) uses the existing candidate-closeout field,
verdict reports and reready responses. Every accepted source survives closeout,
with original text, hashes and run/round/generation provenance. Explicit empty
submissions remain distinct from missing submissions. Both role declarations
reuse the ordinary importer's instruction string, with the no-repeat reminder.

Application rebuilds from the target's committed queue and receipts, preserving
triage performed after closeout. It then freezes the output in the existing
journal. A dirty queue has a tested commit-or-restore-and-retry instruction;
started retries use only their frozen output. The queue is the sole additional
write path. Receipts are validated but never edited or staged.

## Integrated evidence

Seven new tests exercise the public role bridges and trusted application path.
The fixture uses the pinned native producer with explicitly simulated quality
gates. These tests establish lifecycle behavior, not a real semantic verdict.

| Case | Evidence |
| --- | --- |
| Initial publication, rework and approval | Both role bridges retain initial implementer evidence, a replacement candidate, a requested-changes report, a response and approval; restart and application preserve all five sources. |
| Multiple responses | Both accepted responses survive; an orphan file does not enter the source set. Missing or altered history is refused. |
| Original bytes | A CRLF response is retained byte-for-byte, with the same source and submission hashes. |
| Intervening committed triage | A triaged observation stays filtered, an unrelated manual note survives, and receipt bytes remain unchanged. Candidate identities/content agree with the ordinary file-discovery importer. |
| Dirty queue | Refusal occurs before an application journal starts. Committing the intended edit allows a fresh rebuild and successful retry. |
| Interrupted application | Failure after the queue write resumes the frozen write set. Failure after the Git commit but before its receipt recovers the same commit; there is exactly one application commit. |
| Completed application | Repeating closeout/application is idempotent. A later committed queue edit is not overwritten or reimported. |
| Invalid inputs | Malformed receipts, forged receipt content identities, altered source text, incomplete response history, absent/fenced-only sections and wrong-role verdicts are refused. Existing run/generation/approval and document-path controls remain in the structured suite. |
| Explicit empty | No queue or receipt is created. |
| Bounds | A quote-heavy implementer body at 4,096 JSON bytes survives preview, publication, paged review and archive. Oversize bodies are refused; the bridge's 24 KiB ceiling remains unchanged. |

Seven hash-pinned retained observation sections were also transported as payloads
through seven synthetic published candidates, followed by an explicitly empty
review. All eight sources were retained. The resulting queue was byte-identical
to the ordinary importer using the same declared sources: 13 unique candidate
identities including one existing manual note. Repeat application was identical,
and no receipt was created. These are retained-text transport results, **not
historical replay, live agent behavior or a semantic pass**. Source identities,
payloads and raw records remain private.

## Fault controls and validation

Five deliberate in-memory faults are required to fail their matching integrated
test: omit initial implementer evidence, skip source hashes, disable receipt
filtering, duplicate queue content on completed retry, and skip the queue write.
The first four are caught by assertions; the missing write prevents successful
application and fails the test. The controls do not change source files.

Final validation after the last code edit passed:

- Complete structured suite: 348 tests, one opt-in skip, about 160 seconds.
- Retained-text acceptance and all five deliberate fault controls: passed.
- `make test`: 692 shell tests and 1,206 Java tests; strict playbook checking
  reported zero warnings and repository hygiene passed. About 399 seconds total.

The commands ran sequentially under the shared heavy-run lock. Logs, code pins,
source hashes, fault outputs and application evidence remain in the private
packet. Earlier failed test invocations and their corrections are retained
separately rather than overwritten.

The development corrections were test import-path setup, a stale fixture handle
after an MCP publication, and an overly specific expected error code for a
tampered immutable file. Inspection then found and corrected CRLF normalization
while freezing response text; the regression now checks exact bytes. None was a
live-client observation or a change to the accepted scope.

Effort is conservatively estimated at about 1¾ active hours including the
12.1-minute checkpoint, within the four-hour bound. The private record charges
35 minutes for the first continuation block and the full resumed working
interval. It excludes the overnight pause before host test execution; this is
an explicitly provisional charge, not elapsed time presented as active work.

## Limits and next step

No provider calls, client-profile installs, live pass, permission changes,
automatic triage or new transaction framework. The operator's project checkout,
queue and receipts are not application targets in this acceptance. Owner edits
are left in place; protected-state comparisons distinguish concurrent edits.

Actual unsolicited observations, compliance with the no-repeat instruction,
compact-RAM interpretation and operator effort still require the unscripted
pass. Launcher admission must refresh the tool-declaration pins and include the
previously parked reviewer hook-disabled check. The launcher is the next scoped
capability; its implementation and live tests need their own authorization.
