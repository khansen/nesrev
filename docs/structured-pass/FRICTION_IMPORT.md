# Structured learning-candidate import

The service retains observations from both roles and imports them into the
existing project friction queue when the coordinator applies the approved pass.
The ordinary [importer](../../scripts/agent_review.py) remains the authority for
section parsing, content identity, receipt filtering and block replacement.
Import does not triage observations or authorize implementation work.

## Submission and retention

The implementer's existing `kind: closeout` candidate operation requires a
`learning` string: the body of a Learning Candidates section, with a maximum of
4,096 JSON-encoded bytes. The service supplies the heading. This field follows
preview, confirmation, validation and publication; it is copied into the hashed
closeout capture and shown in the retained review's wrapper-closeout evidence.
Every published candidate on the current pass ancestry contributes its own
body. Unpublished candidates do not contribute.

Every `reready.response`, `approve.report` and `request-changes.report` requires
one real `## Learning Candidates` section. An empty submission must contain
exactly `_None._` alone. Missing sections, empty bodies, ambiguous multiple
sections and headings found only in fenced examples are refused before the
accepted state changes. Reports and responses keep their existing 64 KiB cap.
Observations that exceed a bound are refused, never truncated.

Both role declarations reuse `LEARNING_CANDIDATE_GUIDANCE` from the ordinary
review runner, including its recurrence and empty-section rules, followed by
“Don't repeat observations you already submitted in this pass.” Role-specific
help identifies the submission field. This instruction discourages duplicate
prose; import preserves the ordinary parser's semantics rather than introducing
semantic deduplication.

Accepted rework responses have a hash-chained history, with run, round, published
head, file and content identity. The service checks the complete history;
`last_response` alone is insufficient. Orphan response files are ignored.
Existing sessions without the required history or declarations are refused;
they are not retroactively marked empty.

At approved closeout, a hashed source bundle retains every published implementer
body, accepted response and reviewer verdict. The archive includes the original
text and provenance, with source anchors used by the queue. Import consumes the
indexed originals, not the combined archive. Historical intake inputs and
arbitrary transcript files never become import sources.

## Application and recovery

Before an application journal starts, the coordinator rebuilds the queue update
from the frozen sources and the target checkout's current **committed** queue
and receipts. Committed manual notes and intervening triage therefore survive.
Malformed receipts and content identities are refused. Uncommitted queue or
receipt edits return `APPLICATION_FRICTION_DIRTY`: commit intended edits or
restore them, then retry. This refusal starts no application journal.

The existing journal then freezes source identity, queue/receipt preimages,
derived queue hash and the complete approved write set. Application writes the
queue only if it changes, alongside the approved generation and review archive.
Receipt files are read-only inputs and are never staged by import. Ordinary
document edits cannot write either path.

A retry of a started application uses its frozen output. Changed preimages or
receipts refuse rather than replacing concurrent work. A failure after the Git
commit but before the final receipt recovers that exact commit; repeating a
completed application does not import again. Explicitly empty observations
create no queue work. This uses the existing application transaction and retains
its single-coordinator operating assumption.

## Evidence and remaining work

The [scope](FRICTION_IMPORT_SLICE.md) and
[checkpoint](FRICTION_IMPORT_CHECKPOINT.md) define the authorized offline slice.
Its [acceptance record](FRICTION_IMPORT_ACCEPTANCE.md) distinguishes integrated
fixture tests and retained-text transport from live role compliance.

Both corridor tool descriptions changed, as did the standalone reviewer verdict
declaration. Client admission must pin the declarations actually offered before
the next live run. This slice installs no client profile and makes no provider
calls. The launcher and one separately authorized unscripted pass remain the
next steps toward the first complete fresh-game corridor.
