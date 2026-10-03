# Project-Pass Review Packet - Specification

Status: implemented by `scripts/project_pass_review_packet.sh` and
`make project-pass-review-packet`.

This document defines the review packet used when a committed semantic
project-pass is handed to external or adversarial review. The packet is useful
on its own in the current manual workflow and is also the evidence contract
future review automation must generate or consume.

## 1. Purpose

A project-pass review packet standardizes the evidence handed to an external
reviewer after a committed semantic pass. It turns "review the last pass" into
"review this exact Git range with this minimum evidence bundle."

The packet is not a verdict, a gate, or a new project artifact. It is a
generated briefing file. Git history, committed project files, and the existing
project gates remain authoritative. It does not replace the mandatory
self-review, readability audit, closeout, or project gates, and it is not
required for ordinary self-review-only passes.

## 2. Scope

Use a packet when a committed semantic disassembly pass on a `projects/*`
branch is selected for external/adversarial review, review automation handoff,
or an optional solo post-commit audit. The normal reviewed unit is one pass
commit, but the input is an explicit local `BASE..HEAD` range so fixup commits
and small batches can be reviewed without ambiguity.

Do not use this packet format for process, tooling, playbook, test, wrapper,
or shared-script review. Those changes use ordinary branch or PR-style code
review.

## 3. Lifecycle

For external/adversarial review, packets are intended to be ephemeral:

1. The implementation agent commits the project pass.
2. The implementation agent generates a packet from a clean worktree checked
   out at the review head.
3. The reviewer reads the packet and repository state.
4. The packet may be discarded after review.

Keeping a copy under an ignored path such as `/private/tmp` or
`.agents/runs/` is useful for debugging or audit, but packets are not tracked
source files and are not required to reproduce the codebase.

A sole implementer may generate a packet as an optional review aid, but normal
self-review-only pass closure does not require one.

In a future automated handoff, a coordinator may generate the packet when the
review state enters `READY_FOR_REVIEW`. That does not change ownership: the
packet generator materializes protocol-required evidence, and the reviewer
still judges the pass.

## 4. Inputs

The generator takes:

- `PROJECT=<slug>` - project under `projects/<slug>`.
- `BASE=<ref>` - base commit before the reviewed pass or batch.
- `HEAD=<ref>` - review head commit.
- optional `ALLOW_UNRESOLVED_LXXXX=1` when the reviewed pass used relaxed
  semantic-pass verification.
- optional `OUT=<path>` for writing the packet to an ignored file.
- optional `REVIEW_EXPECTED_XASM_SHA256` and `REVIEW_EXPECTED_REF_SHA256`
  environment values to compare the assembler/reference against independently
  recorded expectations. Without these, hashes are reported, not matched to a
  claimed approved baseline.

The implementation must resolve `BASE` and `HEAD` to exact SHAs and print those
SHAs in the packet.

## 5. Required Invariants

A compliant packet generator must:

- run from a clean tracked worktree;
- refuse staged or unstaged tracked changes;
- allow untracked files such as the packet output path;
- refuse to generate if the current checkout is not the requested review head;
- label every gate or generated-evidence block with the SHA or range it
  describes;
- capture command exit statuses and diagnostics, not only summaries;
- include the complete reviewed range, not only a selected commit summary;
- avoid presenting gate output from an earlier SHA as proof about the review
  head.
- recheck HEAD and tracked cleanliness around commands; state changes invalidate
  the bundle and prevent further commands from running against changed inputs.

If historical output from another SHA is included for context, the packet must
label it as such.

## 6. Required Contents

A packet must include these sections or their exact equivalents.

### Reviewed State

List the project slug, project path, base ref and SHA, review-head ref and SHA,
current checkout SHA, short range, and whether the range has project-file
changes.

### Range Summary

Include range-level counters that make common ledger contradictions visible
without comparing against another packet:

- total commits in range and the separate project-filtered commit count;
- rename-ledger row delta and before/after totals;
- unresolved `LXXXX` definition/reference before/after counts and deltas;
- added rename rows whose old name is an `LXXXX` label;
- removed `LXXXX` definitions reconciled against those `LXXXX`-sourced
  rename rows, including any removed labels that have no rename row and any
  `LXXXX`-sourced rename rows that have no matching definition removal.

The unresolved-label count must match the scorecard-sync definition:
`^L[0-9A-F]{4,5}:` for definitions and
`\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:` for occurrences.

The reconciliation uses distinct removed definitions and row-level rename
entries, not the total rename-row count. Each removed definition can match at
most one added `LXXXX`-sourced rename row, so duplicate rows, phantom rows, or
name-to-name refinements cannot hide a deleted or localized generic label. A
removed `LXXXX` definition without a rename row, or a rename row without a
definition removal, is not automatically wrong; it is review-relevant
arithmetic that the packet must make visible.

### Complete Commit List And Diffstat

Include unfiltered `git log --oneline --stat BASE..HEAD`. Root/shared changes
and commits affecting other paths must be visible, not removed by a project
path filter. Also include an unfiltered per-commit changed-path inventory, such
as `git log --format='commit %H' --name-status BASE..HEAD`. This retains paths
changed and later reverted within the range; a net diff alone would omit them.

### Project Diff

Include the full project-filtered diff for `BASE..HEAD`, clearly distinct from
the complete unfiltered history and changed-path inventory above.

### Build and Fixture Prerequisites

Record the resolved paths and SHA-256 hashes of the selected assembler, Make,
Python, Bash, Git and ripgrep, plus the source and reference input paths, sizes
and hashes. Pass the selected `XASM_BIN` explicitly to build/gate commands.
An identical version string is not a binary-identity check; compare file hashes.

Collect missing, empty, unreadable and expected-hash-mismatch diagnostics before
expensive preparation. A reference file's presence/hash is a prerequisite, not
proof of valid iNES structure or parity; canonical verification owns those
checks. Missing fixtures are not labelled parity or semantic failures. Provision
private fixtures only from authorized local inputs; never download or commit
them, and do not run captures during packet generation.

<a id="runtime-analyzer-portability"></a>
### Runtime Analyzer Portability

Run `python3 scripts/runtime_evidence_portability.py --project <slug>
--doc-root <docs> --base <base-sha> --head <head-sha>` independently of the
private-reference prerequisites. A missing ROM must not suppress this check.
It reuses `inventory/runtime_evidence.json` and the runtime checker's declared
commands, acceptance cases, isolated missing-signal refusals and diagnostics.
There is no additional test registry. The current runtime membership and
artifact contract must validate even when executable tests are outside scope.

The affected scope is the reviewed project's active questions. Execute all of
their cases when any commit in the range changes the manifest, its deferral,
blob or family inventories, `project.conf`, or a declared analyzer, runner,
trace plan or fixture from either endpoint. Also include changes under the
project's `scripts/`, `tools/`, and `tests/`, shared directories with those
names, `agent_playbook/templates/trace/`, and root `Makefile`, `pyproject.toml`,
`requirements.txt`, or `requirements-dev.txt`. This covers conventional shared
helper changes without maintaining a second dependency registry. Reverted
changes still count. Other changes explicitly report `no_affected_inputs`;
projects with no active questions report that fact without exporting or running
tests. An analyzer without an active runtime question is outside this contract.

Execute from a fresh export of the exact reviewed commit. Only committed files
enter the export; ignored captures, local reference ROMs and Git metadata do
not. Exported symlinks must remain inside that tree. Each declared case gets
its own temporary working directory and output path and retains the existing
30-second timeout. Use the documented Python/Bash/sh or directly executable
analyzer dependency; do not run capture runners or install dependencies here.
Clear checkout-specific environment variables and Python search-path/user-site
overrides. This runs trusted project code, not an OS sandbox: independent review
must still reject hard-coded external input paths, undeclared helper locations,
network access or emulator invocations. Such dependencies are not portable.

Record the trigger paths, subject and case identities, declared and expanded
commands, expected and actual exits, and diagnostic matches in the section's
JSON output. A required case that fails, cannot run, times out, or produces the
wrong refusal diagnostic fails this evidence. No reference ROM, live capture,
or local Python import path may substitute for committed synthetic inputs.
An unaffected scope exits 0 with an explicit `not-required` reason and no
claimed case results. Fixture success leaves live-capture questions unresolved.

### Cache Preparation

Run `project-pass-prep` explicitly before dependent evidence and gates, using
fresh ignored storage in a cold review worktree. Show its exact command and
exit status. If prerequisites or preparation fail, dependent commands are
explicitly `not-run`, never implicitly green. This is evidence preparation,
not `project-pass-start`, mutating closeout or scorecard/history synchronization.
Set `PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=0` so preparation does not rewrite
the authored raw-RAM review queue, and
`PROJECT_PASS_PREP_CHECK_RAW_RAM_REVIEW=1` to check closeout reconciliation.
Preparation compares the committed queue with the rows computed by the same
raw-RAM refresh path used by closeout, using its fresh, validated assembly
bundle. HEAD, timestamps, or an earlier closeout invocation cannot substitute
for this comparison. The subsequent next-pass command uses
`PROJECT_NEXT_PASS_AUTO_PREP=0` to consume the explicitly prepared cache.

The comparison renders the merged rows in memory with closeout's shared CSV
writer and requires identical bytes. Field diagnostics cover missing candidate
rows and the seven derived columns:
`active`, `operand_count`, `distinct_owner_count`, `read_count`, `write_count`,
`top_readers`, and `top_writers`. Existing refresh policy still applies: supporting
pointer reads do not create candidates, and historical rows without current
access evidence retain their facts. Nonblank authored status, proposed symbols,
notes, and last-reviewed pass are preserved. Closeout's blank-status default
(`unreviewed`), canonical header order, line endings and quoting must already be
reconciled; formatting-only drift is stale even when every parsed field matches.
An absent ledger with no candidates passes without creating a file; closeout's
refresh also preserves that absence. Existing empty ledgers remain present,
and refresh creates a ledger when candidates appear. This checks raw-RAM
reconciliation only; it does not
certify authored decisions, deferral capture, or scorecard/history synchronization.

Preparation prints a `raw_ram_reconciliation` JSON result with changed addresses
and actual/expected fields, including status normalization. `bytes_changed` and
`serialization_changed` distinguish byte drift and noncanonical CSV formatting;
formatting-only changes can have zero changed rows. Stale output returns 68 from the preparation script;
malformed ledgers or invalid analysis evidence return 65. Make may report these
as exit 2. Both block dependent packet commands and handoff; an unrun preparation
is also a refusal. The operator reruns closeout for the reviewed pass, reviews
and commits its changes, then regenerates the packet. Packet creation itself
never performs that repair or changes tracked project files.

### Review Ledger Deltas

Include diffs for authored review ledgers present at either endpoint of the
range. At minimum this covers warning baseline, scorecard, rename ledger,
deferral ledger, semantic claims, crosswalk, and proof-debt acknowledgement
ledger, plus the raw-RAM review queue, when those files exist.

### Aggregate Signals

Include proof-debt output and crosswalk currency output at the review head.

### Next-Pass Evidence

Include `project-next-pass` output at the review head. The reviewer uses it to
judge whether the just-finished pass changed the aggregate project story and
whether the next recommendation is consistent with recorded debt.

### Gates

Include `project-verify`, `project-process-check`, and `project-docs-check`
output at the review head, with exit status and diagnostics. If the pass is in
the semantic phase and unresolved `LXXXX` labels remain, the verify command may
set `ALLOW_UNRESOLVED_LXXXX=1`; the packet must show that mode explicitly.

Do not stop after the first failed gate: when prerequisites permit execution,
run all three sequentially and retain every actual exit and diagnostic.
Protect fenced outputs so headings, commands or status-shaped text printed by
a tool cannot be parsed as packet metadata.

### Required Gate Summary

End with one `## Required Gate Summary` section containing a fenced JSON object
using schema version 3. It records the project and exact review-head SHA,
prerequisite/environment evidence, final state-integrity result, three required
gate records and five supporting-evidence records (cache preparation, next-pass,
proof-debt, crosswalk currency and runtime portability). Each record includes name, SHA, exact command
and actual numeric `exit_status`, or JSON `null` for an explicitly unrun command.
The human-readable command block uses `Exit status: not-run` for that case.

The summary lists every failed/unrun category and an overall evidence status.
It does not infer hidden sub-check results inside a canonical wrapper: full
diagnostics are preserved, including any wrapper's own early termination.
Packet generation can exit 0 when the briefing was produced successfully even
though required evidence failed. That is not gate success or handoff readiness.

`scripts/review_packet_evidence.py` is the shared producer/consumer contract.
The handoff parser requires captured output blocks and checks summary/section
agreement on commands, SHA, statuses, subject and complete required membership.
Build commands must use the recorded Make/assembler; supporting commands must
run their canonical targets against the recorded documentation context.
Every prerequisite, required gate and
supporting evidence command must succeed before handoff. The parser also requires
the read-only reconciliation flags and disabled next-pass auto-preparation in
the recorded commands. Runtime portability must match the packet's base/head
and project; its captured output must include every declared case result,
successful expected exits and diagnostic matches, or an explicit unaffected
scope. Missing, failed and unrun portability commands prevent handoff even when
the other gates pass. Versions 1/2 and missing legacy summaries require packet
regeneration; archived review judgements are not rewritten.

### Reviewer Instructions

Tell the reviewer to read `AGENTS.md` and follow the
`Review a committed project pass` row in its Mandatory Routing Table before
judging the pass. Then tell the reviewer to review the explicit range, inspect
the aggregate signals, read ledger deltas, and return either `APPROVED` or
`CHANGES_REQUESTED` with findings ordered by severity. The review artifact
should include `## Learning Candidates` for process, harness, or tooling
lessons, or `_None._` when there are no candidates.

## 7. Reviewer Use

The packet is a starting point, not a sandbox. The reviewer may inspect the
repository directly, rerun commands, and cross-check packet claims against Git
and project files. Findings should cite the committed project state or packet
sections that expose the issue.

The reviewer should treat a packet as insufficient if it omits a changed commit
from the range, labels gates with the wrong SHA, hides command failures, or
fails to expose authored-ledger deltas, or contradicts/omits required terminal
evidence. A zero verify exit cannot hide failed process/docs gates or unrun
preparation. SHA and command agreement is structural validation of captured
evidence, not authentication of an arbitrarily hand-forged packet.

Reference review context includes the applicable pass plan's `REFERENCE_SCOPE`
(explicitly unversioned, never gate evidence) and committed source inventory /
crosswalk paths at the reviewed head. The source inventory is
`docs/crosswalk/MANUAL_TERMS.md`; the same path feeds pass-start freshness
checks and ledger diffs (including a file removed since the base).
Missing inventory is reported with intake/migration guidance. Existing
projects must adopt this canonical location after rebasing onto the tooling.
Missing or mismatched plans are reported
as unrecorded; reviewers reconstruct scope from the range. Review source
coverage and newly provable identities per
[QUALITY_REVIEW.md](agent_playbook/QUALITY_REVIEW.md#reference-coverage).

## 8. Relationship To Automation And Prior Art

This packet contract is orthogonal to agent-review coordination. A generic
coordinator decides whose turn it is and how findings move between agents; it
does not know this repository's project-pass evidence unless it runs or
consumes a compliant packet.

Prior-art tools can satisfy the review workflow in two ways:

- invoke this repository's packet generator and pass the packet to a reviewer
  engine; or
- generate an equivalent packet from the same Git range, ledgers, aggregate
  signals, and gates.

Tools that only review PR-shaped diffs or branch summaries are insufficient
for project-pass review unless wrapped with this packet contract.

## 9. Non-Goals

The packet generator does not:

- approve or reject a pass;
- implement turn-taking, round limits, or agent wakeups;
- create commits, branches, merges, or pushes;
- replace project gates;
- replace reviewer judgement;
- validate every ledger row retroactively.

Mechanical gates discovered from packet-review failures should be added as
separate process changes. The packet should expose review evidence; it should
not grow into a hidden second process-check implementation.
