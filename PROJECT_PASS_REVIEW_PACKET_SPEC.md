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

- project commits in range;
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

Include `git log --oneline --stat BASE..HEAD -- projects/<slug>` or an
equivalent complete commit list for the project path.

### Project Diff

Include the full project diff for `BASE..HEAD`.

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
fails to expose authored-ledger deltas.

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
