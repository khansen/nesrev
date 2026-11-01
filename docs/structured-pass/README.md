# Structured pass service

This opt-in service lets an implementer and reviewer work with assembler records
instead of opening assembly files. It is a migration of the exercised prototype
to the published XORcyst source-model contract. The ordinary project commands
remain available and retain their existing behavior.

The [rollout plan](ROLLOUT_PLAN.md) defines the three delivery steps and their
completion gates: promote this service, complete normal-pass operation coverage,
then make structured passes the enforced default. Opt-in is transitional.

The producer is pinned in [producer.json](producer.json). This is a commit pin,
not a requirement to install or release a new stable assembler. The schema is
vendored unchanged in `scripts/structured_pass/source-model.schema.json`.

## Supported work

The current editing surface supports bound global/local/EQU renames, replacement
of existing comment records, appended rename-ledger rows, authored text documents,
and typed scorecard/closeout inputs. A rename changes every producer-bound use,
including data and nested expressions. It preserves the other declarations and
bindings and refuses undisposed current prose. Historical review archives,
historical scorecard rows and the old-name ledger column remain history.

Comment-only repair batches are supported. In a corridor they still include the
scorecard and closeout operations, but need neither a rename nor an unrelated
document edit. Scorecard-only repairs also need no dummy edit. Preview and review
results are paginated, with a 24 KiB ceiling on each serialized bridge response.
Review pages separate the declaration from each changed use; only the first page
carries Q09 and the changed-file list. Inspect returns a declaration and use count;
use `navigate` to page through references. Reduce the requested page size if a
query returns `RESPONSE_TOO_LARGE`.
Read subsequent pages with `preview_page` before confirming the preview digest.
An individual oversized item is refused explicitly, never silently truncated.

Navigation includes declarations, complete direct uses, lexical blocks and
comments. The constant-context query also follows EQU dependencies. These views
present evidence; they do not decide whether a name or constant is semantically
correct. Addresses retain their producer segment identity.

Operand replacement, adding declarations, localization, data reflow, general
project-tool edits, mixed raw-RAM row editing and runtime capture are not exposed
by this corridor profile. Authored inventory updates to
`data_blob_dispositions.csv` and `policy_baseline.csv`, and mixed
`raw_ram_review.csv` rows, have no edit route yet. A rename whose spelling occurs
in these files can fail closed during closeout after validation work; the service
cannot complete that rename until the required ledger operation exists.
A pass requiring one of these operations must stop and
report the missing operation. The earlier instruction-correction experiment is
not an editing API in this extraction. No agent worker or arbitrary-code endpoint
is provided.

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
* Publication exports immutable content before moving the current generation.
  A ticket can reopen the complete review window after the editor is deleted.
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

python3 -B scripts/structured_pass_heavy_run.py \
  --lock "$STRUCTURED_PASS_LOCK" --agent operator --session producer-build \
  --estimate-mib 128 --reserve-mib 2048 --volume "$STRUCTURED_PASS_STORE" -- \
  python3 -B -m structured_pass.toolchain \
    --repo /absolute/path/to/xorcyst --store "$STRUCTURED_PASS_STORE"
```

Create the store parent before running the volume check. The builder uses only
the pinned local Git commit; it does not fetch code. It retains the executable,
source archive, compiler identification and rebuild recipe under its binary hash.
Set `STRUCTURED_PASS_XASM` to the returned executable path.

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
and block continuation until explicit owner recovery. `extend` is
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
