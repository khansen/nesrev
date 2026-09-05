# Friction queue receipts

`projects/<slug>/PROCESS_FRICTION.md` contains candidates awaiting triage,
not accepted implementation work or a historical log. The canonical
[triage criteria](REVIEW_AUDITS.md#process-learning-triage) determine whether
an observation belongs in tooling, a playbook, a project-local artifact, or
nowhere. Routing ends queue residency even when implementation is unfinished.

## Migration and commands

Run from the repository root:

```sh
python3 scripts/process_friction.py list --project demo
python3 scripts/process_friction.py triage --project demo --decisions decisions.json
python3 scripts/process_friction.py prune --project demo
```

`list` reports candidate IDs, content, source references, and existing triage
status. Supply an explicit JSON decision array using the reported IDs:

```json
[
  {
    "id": "<candidate ID from list>",
    "disposition": "accepted",
    "destinations": ["PROCESS_IMPROVEMENT_PLAN.md#pi-4--make-review-bundles-self-contained-and-reproducible"],
    "rationale": "The named plan item owns this reproducible review-bundle defect."
  }
]
```

Dispositions are `accepted`, `promoted`, `project_local`, `duplicate`, `fixed`,
`superseded`, or `discarded`. The first four require at least one destination;
every decision requires a rationale. Local destination files must exist within
the repository; optional anchors and HTTP(S) references remain human-reviewed.
The tool does not prove that a destination actually accepts the work.

For existing marker-only or manually written queues, inspect every candidate
and check source coverage before backfilling. Preserve useful unique evidence
at its destination. An archive's existence is insufficient: implementation-note
learning text is not included by the review archiver. Untracked notes have no
Git-history protection. Do not delete either kind's sole copy during migration.

`triage` validates the complete batch and saves receipts without changing the
queue. Inspect those receipts before `prune`. After migration, `triage --prune`
can perform both steps in that order. Pruning removes only receipted candidates;
it removes the file when no candidates remain. A persistence failure leaves
the queue available for retry. If receipts saved but queue replacement failed,
rerun `prune`. Malformed legacy markers and invalid receipts fail closed.
These commands do not initialize or mutate the project-pass handoff state.
Commit tracked queue/receipt changes before re-archiving, which still requires
a clean tracked worktree. If relocating `agent_review.py` outside the repository,
keep its companion `process_friction.py` in the same directory.

## Receipt and ingestion contract

Receipts are tracked project-local data at
`docs/reverse_engineering/inventory/process_friction_receipts.json`.
Schema version 1 stores the project slug and a `receipts` array. Each entry
contains `id`, normalized `content`, `sources`, `disposition`, `destinations`,
and `rationale`. Keep this machine record, not a second prose backlog or a
completed-items table in the queue.

Identity is the SHA-256 of candidate text after trimming trailing whitespace
and outer blank space, scoped to its project. Source paths, run IDs and reviewed
SHAs are provenance, not identity: re-archiving unchanged text after a rebase
must not recreate triaged work. Distinct new content remains discoverable.
Receipts preserve content and source references, including unique manual or
implementation-note observations. Their schema and content hashes are checked
before ingestion or pruning. Writes replace the receipt file atomically before
any queue removal; run one triage/archive writer per project at a time.

Top-level bullets, numbered items and headings delimit candidates; indented
details and fenced examples remain attached. Headings, source labels, and
receipt markers inside fenced examples are content, not parser boundaries.
Free-form prose is opaque. Pruning preserves unrelated manual context.
Explicit empty observations produce no queue work. Content-changing rewrites
are intentionally new evidence and may need a duplicate decision; this is not
a semantic-similarity classifier. For an untriaged run, force re-archiving keeps
the existing replace-that-run behavior. Previously triaged candidates are
filtered individually, so candidate A cannot hide a new candidate B.
Repeating an identical triage decision merges source references; changing an
existing decision is refused rather than silently overwriting its history.

Tests in `tests/process_friction_test.py` cover migration, partial imports,
deleted queues, new runs/rebased SHAs, persistence failures, manual notes,
malformed input and scoped paths. The shell harness also exercises the existing
review/archive workflow.
