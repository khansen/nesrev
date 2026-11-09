# Structured pass service

This opt-in service lets an implementer and reviewer work with assembler records
instead of opening assembly files. It is a migration of the exercised prototype
to the published XORcyst source-model contract. The ordinary project commands
remain available and retain their existing behavior.

The [rollout plan](ROLLOUT_PLAN.md) defines the three delivery steps and their
completion gates: promote this service, complete normal-pass operation coverage,
then make structured passes the enforced default. Opt-in is transitional.
The [step-2 coverage baseline](STEP_2_COVERAGE.md) records the proposed missing
operations and their acceptance criteria; it does not add supported operations.

The producer is pinned to the official XORcyst 2.1.0 release in
[producer.json](producer.json), including its immutable release commit, download
URL, archive checksum and source-model schema hash. Ordinary CI and structured
passes build from that same checked archive. The schema is vendored unchanged in
`scripts/structured_pass/source-model.schema.json`.

## Supported work

The `source-v2` profile supports bound global/local/EQU renames, EQU and label
insertion, typed expression replacement, unused-declaration removal, grouped
localization, data reflow, and comment/trivia edits. It also supports admitted
authored Markdown, rename-ledger appends, and typed scorecard/closeout inputs.
The fixed artifact writers update `data_extent_assertions.csv`,
`data_blob_dispositions.csv` and `WARNING_BASELINE.txt`. See the
[Step 2A operation contract](SOURCE_OPERATIONS.md) for request fields,
preconditions, layout restrictions and read views.

A rename changes every producer-bound use, including data and nested expressions.
It preserves the other declarations and bindings and refuses undisposed current
prose. Historical review archives, historical scorecard rows and the old-name
ledger column remain history. Preview currently refuses a combined batch of
more than 64 retired names across renames, localizations and declaration removals;
the [Q09 follow-ups](STEP_2_COVERAGE.md#deferred-q09-follow-ups) track that limit
and the incomplete retired-name list in review page-zero metadata.

Comment-only repair batches are supported. In a corridor they still include the
scorecard and closeout operations, but need neither a rename nor an unrelated
document edit. Scorecard-only repairs also need no dummy edit. Preview and review
results are paginated, with a 24 KiB ceiling on each serialized bridge response.
Review page zero contains the Q09 count and paginated read request, changed files
and the change/page totals, without any change payload. For `rename` and
`source-v2` review, `limit` defaults to 1 and accepts 1–40 review items per call.
An item is one declaration or other change, or up to eight consecutive uses of
one declaration (fewer when the encoded bytes require it). Page zero stays
metadata-only at every limit; its continuation is 1 when changes exist.
`offset` addresses these stable items, with changes starting at 1. Follow
`next_offset` until null: a page can stop before the requested limit to fit the
24 KiB wire ceiling. Batching preserves the exact single-item change payloads,
including any existing context/document truncation markers, in the same order.
`total_changes` counts individual changes, including grouped uses; the legacy
`total_pages` remains the number of single-item pages including metadata, not
the number of calls needed with a larger limit. The older instruction profile
still accepts only `limit: 1`.
Use rows retain the full before/after statement and the exact reference leaf,
including its binding, plus the lexical owner's record ID. They omit neighbouring
statements and the repeated declaration body. To read context, call `navigate`
with `view: records`, the side's statement or lexical-owner `record_id`, and the
page's generation. Corridor and retained sessions both accept those `E-` IDs.
Ledger additions use pages of at most 16 rows (fewer if needed to fit), with
`row_offset` and `total_added_rows`; every row retains its reason and confidence.
The unchanged ledger prefix is checked. Review-code hashes appear on page zero,
with their digest on every page.
Oversized declaration/use pages omit only neighbours (`neighbors_omitted: true`);
the changed records and IDs remain. Document comparisons keep path, reason, hashes
and line counts. `hunks` show each changed area with one-based `before_line` and
`after_line` positions and their `before_lines`/`after_lines`; unchanged lines are
not repeated. A zero-line side names its insertion position, possibly past EOF.
`total_hunks` counts all changed areas, and each side counts those with its lines.
When the wire budget requires trimming, lines are removed from the last hunk first.
`omitted_hunks` counts areas with any omitted lines, including partially shown ones;
each side reports its own count, `truncated` and one-based `first_omitted_line`.
Partial hunks also mark the affected side with `before_truncated`/`after_truncated`.
Use `first_omitted_line - 1` as the document read offset. A terminator-only change
has no hunks and sets `line_terminators_changed: true` instead of inventing a line.
Read the page's before/after `E-` generations with `document` for omitted
lines, in either corridor or retained sessions. Corridor reads also accept `G-` IDs.
Closeout views carry a digest of the wrapper hash list and the original receipt
hash; the complete list remains in the retained receipt. An individually oversized
changed record still refuses with `RESPONSE_TOO_LARGE`, but includes `offset`,
`total_changes` and `next_offset` so other changes remain reachable.
Inspect returns a declaration and use count; use `navigate` to page references.
For paginated document/query/navigation results, reduce `limit` and retry the same
offset if a response is too large; those refusals never give a skipping `next_offset`.
`document` accepts `generation`, a repository-relative `path`, optional `offset`
(default 0), and optional `limit` (default and maximum 80 lines).
Q09 accepts `offset` (default 0) and `limit` (default 12, maximum 40). It returns
`mentions`, `total_mentions` and `next_offset`, stopping earlier when the encoded
byte budget requires it. Follow `next_offset` until null; no match is discarded.
An individually oversized match refuses with its location and an action naming
the offset after that undelivered match; continuing there does not mean the match
was reviewed. Preview still checks
the complete prose inventory, independently of the public page limit.
Read subsequent pages with `preview_page` before confirming the preview digest.
It accepts `generation`, `preview_digest`, optional `offset` (default 0), and
optional `limit` (default 12, maximum 40 records). Follow the returned
`next_offset`; the byte ceiling may end a page before the requested limit.
Preview pages measure the complete MCP encoding, including escaped text, with
metadata headroom. An individual oversized item refuses before its confirmation
digest is registered, rather than leaving an unreadable saved preview.

Navigation includes declarations, complete direct uses, lexical blocks and
comments, including anonymous forward/backward declarations. Repeated anonymous
names require a `record_id` to select a particular declaration and its bound uses.
The constant-context query also follows EQU dependencies. Its `owners` counts
cover the full inventory for owners represented on the current use page;
`owners_scope: current_page` and `total_owner_count` make that scope explicit.
Following all use pages exposes every owner without repeating the full inventory.
Comments with invalid UTF-8 bytes use replacement characters in `text`, marked
by `text_encoding: utf-8-replacement`, and carry exact `bytes_hex`. Their preimage
hash still covers the original bytes; `comment_replace` can repair them with
UTF-8 text while leaving untouched comments byte-identical. These views
present evidence; they do not decide whether a name or constant is semantically
correct. Addresses retain their producer segment identity.

Code/data recovery, project-tool edits, KPI/allowlist changes and runtime capture
remain unavailable. Authored updates to `policy_baseline.csv`,
`data_format_targets.csv`, `proof_debt_acknowledged.csv` and the judgment fields
of `raw_ram_review.csv` have no edit route yet. Trusted refresh may update the
existing raw-RAM queue's factual fields while preserving its authored judgments.
A rename that requires an unsupported artifact update can fail closed during
validation or closeout; the service cannot complete it until that writer exists.
Existing deferral rows also remain protected; closeout supports new-row appends,
not closing or rewriting existing rows.
A pass requiring one of these operations must stop and
report the missing operation. No agent worker or arbitrary-code endpoint is
provided.

## Invariants and ownership

* The saved source model contains the bytes and complete lexical partition. A
  no-op reconstruction opens no input source and reproduces every byte.
* Bindings, expression structure, scopes, segments, layout and values come from
  the pinned producer. The adapter validates the schema and joins; it has no
  assembly parser or expression evaluator. The independent semantic validator
  remains in the producer's tests.
* Certification requires exit zero, comparison `equal`, and independently equal
  **whole PRG bytes and length**. A partial comparison cannot certify a pass.
* Every read names a generation. Candidate responses also name their revision;
  amendment clears all earlier validation evidence. An interrupted validation is
  recovered under the same lock used by every state mutation.
* Authored document writes use preimages and a narrow text-file allowlist.
  Sources, project configuration, reference files, mods, generated inventories,
  review archives and service-owned evidence have no document-write route.
  Paths are checked for case variants and symlinks.
* Clients author only the scorecard's `focus` and `notes`. Gate and metric cells
  and closeout deferral rows belong to the trusted wrapper. Gates use one pinned,
  allowlisted environment and record it. A forbidden generated write names its
  project-relative path in the rejection.
  Failed gates include sanitized `failure_lines` for `FAIL:`, `ERROR:` and `FATAL:`
  messages, even when a later subcheck prints a successful JSON summary. The
  bounded `failure_context` includes up to 120 following lines per message,
  stopping at a blank line, a JSON/progress block or the next failure. Entries are
  keyed by `failure_index`; `context_truncated` and the overall `truncated` flag
  mark any detail lost to the line, string or byte limits. Byte trimming removes
  lines from the end of the last context first. An empty, flagged entry remains
  while its failure message is visible. The trailing structured report (including
  residue entries) remains available when it fits. Diagnostics prioritize failures
  within a shared encoded-byte allowance;
  truncation flags and the failure-line count describe omitted detail. Log scanning
  covers the last 256 KiB and explicitly reports when earlier output was omitted.
  Full logs and their hashes remain service-owned; raw source excerpts and host
  paths are sanitized in the response.
* Publication exports immutable content before moving the current generation.
  A ticket can reopen the complete review window after the editor is deleted.
  Rename receipts retain the original pass ID, so Q09 keeps checking the current
  scorecard row even when earlier generations are outside the restored window.
  The retained producer can reassemble the restored tree; dependency checks
  refuse inputs outside it.
* Content identity is independent of installation path and service code. Fact
  tooling identity covers the producer, adapter, schema and record-ID mapping.
  Changed fact readers refuse old artifacts with `TOOLING_IDENTITY_MISMATCH`.
  Review outputs separately identify the code that rendered them.

This uses artifact schema `structured-pass-artifact-v3`. Prototype v1/v2 receipts
and live runtime state are deliberately not upgraded in place. Keep their
original readers and stores until their evidence has been archived independently.
New service sessions use a separate store; they never rewrite the prototype's
store. Changing code while an editor is open also invalidates its runtime pin.

## Operator setup

Use Python 3.9 or later, Git, make, Bash, ripgrep and a C compiler. The macOS
subscription profile additionally requires a Claude Code version that passes the
native restriction probe below. Do not infer compatibility from the version name.

Configure **one absolute lock path shared by all worktrees and both agents**.
All builds, project checks and model tests run sequentially through the runner:

```sh
export PYTHONPATH="$PWD/scripts"
export STRUCTURED_PASS_LOCK=/absolute/shared/nesrev/heavy.lock
export STRUCTURED_PASS_STORE=/absolute/retained/nesrev/structured-pass

mkdir -p "$STRUCTURED_PASS_STORE"
curl --fail --location --retry 3 --output "$STRUCTURED_PASS_STORE/xorcyst-source.tar.gz" \
  "$(python3 -c 'import json; print(json.load(open("docs/structured-pass/producer.json"))["archive_url"])')"

python3 -B scripts/structured_pass_heavy_run.py \
  --lock "$STRUCTURED_PASS_LOCK" --agent operator --session producer-build \
  --estimate-mib 128 --reserve-mib 2048 --volume "$STRUCTURED_PASS_STORE" -- \
  python3 -B -m structured_pass.toolchain \
    --archive "$STRUCTURED_PASS_STORE/xorcyst-source.tar.gz" --store "$STRUCTURED_PASS_STORE"
```

The builder verifies the archive checksum before extraction, then checks the
schema and both tool versions. It does not fetch code or use a Git checkout.
It retains the executables, exact release archive, compiler identification and
rebuild recipe under the assembler's binary hash. Set `STRUCTURED_PASS_XASM` to
the returned producer path. `--archive` replaces the earlier commit-only `--repo`
setup. Existing stores are not migrated: retain their pinned tools and start new
sessions with the release build in a separate store.

Write an operator selection JSON containing exactly these string fields:
`project`, `target`, `objective`, `why_now`, `boundaries`, `evidence`,
`reference_scope`, `out_of_scope`. No edit map or expected semantic answers belong
in this profile. The operator supplies the project and selected corridor.

```sh
python3 -B scripts/structured_pass_heavy_run.py \
  --lock "$STRUCTURED_PASS_LOCK" --agent operator --session prepare \
  --estimate-mib 1024 --reserve-mib 2048 --volume "$STRUCTURED_PASS_STORE" -- \
  python3 -B -m structured_pass.prepare --repo /absolute/project-checkout \
    --output /absolute/private/session-preparation --selection selection.json \
    --producer "$STRUCTURED_PASS_XASM" --store "$STRUCTURED_PASS_STORE"
```

Preparation clones an isolated base, uses the existing config loader and
next-pass/pass-start wrappers, certifies the source and runs the four baseline
gates. It creates an empty editor. It neither edits the operator checkout nor
authorizes inference. A nonzero baseline refuses preparation rather than masking
later gate failures.

## Clients and review

The trusted operator starts each bridge with a fixed role. Role, profile and
session are not request arguments. Review verdicts use the existing
`agent_review.py` history. Coverage includes every publication edge, even when a
pass exceeds one eight-state review window. A new publication invalidates
complete coverage until reviewed. Closeout recomputes live coverage, then writes
the archive; reading a stored `APPROVED` field alone is insufficient.
Closeout checks approval and creates the archive under the handoff and shared
editor locks. Application keeps those same locks through gates and the local
commit. An intervening revocation refuses application; concurrent verdicts and
publication must retry after application releases those locks.
Each closeout preserves an immutable archive snapshot under the coordinator's
run directory (`closeouts/<sha256>.md`). Reapproval may replace the canonical
archive while no application journal exists; the prior snapshot remains intact.
Once application begins, a different archive refuses with `CLOSEOUT_ALREADY_APPLIED`
so retries retain the exact approved write set. Unknown or tampered prior archives
are never overwritten. Keep these snapshots with the other coordinator evidence.

Status and verdict responses include at most 1,024 characters of `latest_review.report`.
For a partial report, both roles can call `review_report` with its `sequence`
and follow `next_offset` until null. Offsets count Unicode characters; `limit`
defaults to 1,024 and cannot exceed it. Each page includes the full report's hash
and total character count. The checked canonical report and archive remain complete.

The permission boundary is the restricted client's configuration, not Unix user
separation. Both services run as the operator and own source, Git and evidence.
The agent's workspace contains no checkout, snapshots, Git objects or source-model
files. Its only tools are `Read` for explicitly selected reference media and the
role bridge. Native shell, search, edit, agents and connectors are absent. The
hook allowlists paths; the client's `--restricted` boundary independently denies
outside reads. A client upgrade must pass the native probe before use.

Prepare subscription settings with explicit model, effort, client and interpreter
paths. This command makes no model request:

```sh
python3 -B -m structured_pass.subscription_client --root /absolute/private/launch \
  prepare --session /absolute/private/session-preparation/session \
  --prompts /absolute/private/role-prompts --model MODEL --effort EFFORT \
  --client /absolute/path/to/claude --interpreter /absolute/stable/python3 \
  --heavy-lock "$STRUCTURED_PASS_LOCK"
```

The prompt directory contains `implementer.md` and `reviewer.md`. State the
corridor constraints, supported operations, allowance and batching instructions
in both prompts. Authentication uses the launch's isolated `auth-config`; an
existing subscription login outside it is not reused. `check` verifies that login
without running a model. Settings and prompts are pinned at preparation.
Optional repeated `--media /absolute/reference.png` or `--media /absolute/manual.pdf`
arguments copy operator-selected reference media into the source-free workspaces.
Their bytes and allowed read paths are pinned; unexpected workspace files refuse
launch.

Only an explicit operator `authorize --responses N --minutes N` enables a run.
Run a role under the same heavy runner with `run implementer --message TEXT` or
`run reviewer --message TEXT`. Each invocation reserves up to 30 responses from
the shared allowance. Response IDs are persisted as they arrive and charged once
across all invocations, including resumes; the client's `num_turns` is telemetry,
not billing. Incomplete streams keep their observed charges, mark usage uncertain
and block continuation until explicit owner recovery. The CLI exits nonzero for
a failed client exit, a missing or duplicate final result, or an error result,
after saving the observed charges and run receipt. A successful invocation needs
exit 0 and exactly one successful final result. `extend` is
operator-only, records each grant and never runs automatically. These are usage
ceilings, not estimates of subscription quota or monetary cost.

After approved closeout, `python3 -B -m structured_pass.application --session
SESSION --repo CHECKOUT` checks application without writing. Adding `--commit`
applies the approved files, reruns gates and makes an unsigned local commit on
`projects`. Nonoverlapping intervening commits are accepted; overlapping or dirty
paths refuse. It never pushes. A gate failure leaves the explicit write set for
repair/retry; it does not claim that a commit occurred.

## Validation and retention

Run `make test-structured-pass` with `STRUCTURED_PASS_LOCK` and
`STRUCTURED_PASS_XASM` set. The producer tests, neutral lifecycle, malformed
requests, document ownership, coverage, shared-runner and budget tests require no
models. The synthetic lifecycle uses clearly labelled simulated quality gates;
it is not evidence that those quality gates are correct. Real-project replay
evidence stays outside the project-neutral repository.

Set `STRUCTURED_PASS_CLIENT` to additionally run the opt-in native probe. Its
fake API listens only on loopback with a dummy credential; it tests the real
client and bridge, denied raw reads/shell, image/PDF access and the offered tool
set. It performs no provider inference and uses no subscription login.

Retain immutable receipts, blobs, toolchains and review tickets outside system
temporary directories. Tests remove only their own temporary trees. Never remove
the shared coordinator directory or its receipts while a process might be live:
deleting the entire directory defeats coordination. On
`HEAVY_ORPHAN_REQUIRES_RECOVERY`, inspect the recorded process group and wait for
or explicitly stop the known run; rerun after the group has exited. Do not delete
the receipt to bypass recovery. Free-space measurements describe available
space, may be rounded by a sandbox, and cannot exclude unrelated system activity.

The prototype demonstrated feasibility with operator assistance. This migration
does not claim lower token cost, better names or superior pass quality. Those
claims require a separately authorized comparison exercise.
