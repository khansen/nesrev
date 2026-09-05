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

### Cache Preparation

Run `project-pass-prep` explicitly before dependent evidence and gates, using
fresh ignored storage in a cold review worktree. Show its exact command and
exit status. If prerequisites or preparation fail, dependent commands are
explicitly `not-run`, never implicitly green. This is evidence preparation,
not `project-pass-start`, mutating closeout or scorecard/history synchronization.
Set `PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=0` so preparation does not rewrite
the authored raw-RAM review queue.

### Review Ledger Deltas

Include diffs for authored review ledgers present at either endpoint of the
range. At minimum this covers warning baseline, scorecard, rename ledger,
deferral ledger, semantic claims, crosswalk, and proof-debt acknowledgement
ledger when those files exist.

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
using schema version 1. It records the project and exact review-head SHA,
prerequisite/environment evidence, final state-integrity result, three required
gate records and four supporting-evidence records (cache preparation, next-pass,
proof-debt and crosswalk currency). Each record includes name, SHA, exact command
and actual numeric `exit_status`, or JSON `null` for an explicitly unrun command.
The human-readable command block uses `Exit status: not-run` for that case.

The summary lists every failed/unrun category and an overall evidence status.
It does not infer hidden sub-check results inside a canonical wrapper: full
diagnostics are preserved, including any wrapper's own early termination.
Packet generation can exit 0 when the briefing was produced successfully even
though required evidence failed. That is not gate success or handoff readiness.

`scripts/review_packet_evidence.py` is the shared producer/consumer contract.
The handoff parser checks summary/section agreement on commands, SHA, statuses,
subject and complete required membership. Every prerequisite, required gate and
supporting evidence command must succeed before handoff. Missing legacy summaries
require packet regeneration; archived review judgements are not rewritten.

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
