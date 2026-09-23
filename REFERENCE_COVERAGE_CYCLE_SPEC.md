# Reference Coverage Throughout the Pass Cycle

Status: implemented by the project-pass and agent-review tooling.

## Purpose

Make reference terminology part of ordinary reverse-engineering work, and
require an explicit assessment of its coverage before declaring gold.

A project can have clear mechanical names, binary parity, and green quality
gates while still failing to identify the game's important creatures, items,
actions, or rules. A crosswalk can also look complete simply because nobody
inventoried the missing concepts. Counting mapped rows cannot detect that.

The desired result is a disassembly whose names describe the game wherever
code evidence supports the connection to its manual and supplied FAQs. Work
should resolve those connections as the relevant subsystem becomes understood,
instead of accumulating a separate terminology backlog until final review.

## What Changes

| Stage | Operator or reviewer responsibility | Tool behavior |
|---|---|---|
| Reference intake | Inventory important concepts from supplied sources; distinguish official vocabulary from community names. | Existing manual intake and explicit-waiver process remains in force. |
| Pass selection | State which reference concepts the selected corridor can resolve, or explain why none apply. Revisit gaps when their missing evidence becomes available. | `REFERENCE_SCOPE` is saved with the corridor objective. Missing scope produces guidance; it does not prohibit ordinary WIP passes. |
| Implementation | Trace concepts to routines, selectors, records, RAM, and behavior. Apply proven names and update the crosswalk in the same pass. | No automatic semantic renaming or numerical coverage target. |
| Pass review | Assess the pass's reference scope, mapping evidence, and newly answerable gaps. | Review prompts and packets carry reference context. Ordinary review remains human/agent judgment. |
| Gold review | Compare the inventory with supplied references, check important mappings, and justify remaining dispositions. | Approval requires a structured reference assessment and resolving evidence links at the reviewed commit, before strict CI. |

For example, a movement pass may prove that a shared handler serves several
creatures. The handler should retain its shared name. A later rendering pass
may identify which selector denotes a particular manual creature; that pass
should name the selector and close the crosswalk gap. It should neither invent
the identity early nor postpone the now-proven mapping until gold review.

## Reference Artifacts and Planning Context

The source inventory records important entities, items, actions, rules, and
world/UI concepts from every supplied source, with page or section citations.
The crosswalk records code mappings and evidence, unresolved links with revisit
conditions, or justified context-only, absent-version, and shared-code
dispositions. Ordinary story prose does not require artificial code symbols.

The sole inventory location is `docs/crosswalk/MANUAL_TERMS.md`. The
reference-material tree remains git-ignored; authored extraction belongs in the
canonical inventory. Existing projects need migration after rebasing, described
below. This branch adds no fallback paths or alternate formats.

One helper supplies the canonical inventory path for:

- pass-start freshness checks alongside the crosswalk;
- packet context, using files committed at the reviewed head;
- ledger diffs, including an inventory removed since the review base.

If the canonical inventory is absent at the reviewed commit, the packet asks
for intake or migration. It does not infer that the manual is missing or waived
from a missing filename.

`REFERENCE_SCOPE` is operator-authored planning context stored in the ignored
`current_pass_plan.json` and Markdown plan. Packets label it as unversioned.
Missing, malformed, wrong-project, or wrong-pass plans are explicitly unrecorded;
the reviewer reconstructs scope from the committed range. Planning text is
never presented as committed proof of a mapping.

## Gold Assessment and Enforcement Boundary

A gold review contains `## Reference Coverage` with these fields:

- `Sources:` which supplied sources were processed, including optional FAQs.
- `Inventory:` how completeness was checked, including omissions.
- `Mappings:` mapping evidence and shared-handler/record distinctions.
- `Gaps:` remaining uncertainties, or none, and why the conclusion is justified.
- `Reference coverage: COMPLETE`, or `Reference coverage: EXPLICIT MANUAL WAIVER`.
- `Waiver:` the explicit user decision and quality limitation, when applicable.

Every evidence field, including `Gaps`, needs a repository-relative Markdown
link to authored documentation under this project's `docs/`. Referenced files
and anchors must exist at the reviewed commit. Bare placeholders such as
`Gaps: N/A` do not satisfy the contract; a no-gaps conclusion still cites its
evidence. Fenced examples do not count as assessment fields.

The tool validates structure and link resolution. The reviewer judges source
completeness, whether the evidence proves the claimed identities, whether a
waiver is valid, and whether remaining gaps block gold. A resolving link alone
cannot prove those judgments. Existing clean-tree, reviewed-head, strict-CI,
and approval/archive checks remain required.

Important unresolved gameplay identities, including pending runtime evidence,
block gold. An explicit manual waiver permits work with reduced reference
material; it does not waive evidence standards for available sources. Ordinary
passes may retain specific unresolved identities and continue useful work.

## Identity-Debt Acknowledgements

Existing advisory signals flag a largely unmapped crosswalk and repeatedly
deferred subjects. This branch narrows how those signals can be acknowledged:

- Identity rows need a reason, review pass number, evidence scope token, and
  a concrete revisit condition.
- `crosswalk_unmapped` scopes its acknowledgement to the full crosswalk text.
- `deferral_repeat` scopes each acknowledgement to that subject's deferral rows;
  acknowledging one subject does not suppress another.
- Changed recorded evidence invalidates the matching scope. A later unrelated
  pass alone does not expire it. Missing, invalid, or future pass numbers cannot
  suppress a signal.
- Operators must check revisit conditions during pass selection and record new
  relevant evidence. The detector cannot infer from a code change alone whether
  a condition has been met. Even unrelated edits to hashed evidence invalidate
  its token; this is evidence fingerprinting, not automatic dependency analysis.

The sole CSV header is `signal,reason,pass_id,scope,revisit_condition`.
Scaffolding, artifact validation, process checks, and the acknowledgement reader
use that format. The old three-column header is rejected. Non-identity signals
retain their existing reasoned dispositions after migration; their added fields
may remain blank.

Acknowledgements suppress advisory scheduling signals, never the gold reference
assessment or a reviewer's obligation to investigate important gaps.

## Rollout and Project Migration

Land the tooling, rebase the local `projects` branch onto the updated master,
then migrate project artifacts before resuming passes. Do not carry legacy
support into master to avoid that one-time migration. Shared tooling does not
migrate or push project content automatically.

1. Extend every acknowledgement ledger to the five-column header. Preserve each
   historical signal, reason, and pass number; append blank fields to existing
   rows. Never fabricate a historical scope token or revisit decision. Review
   identity signals that resurface and acknowledge only current evidence.
2. Move authored inventories from the old reference-metadata location into
   `docs/crosswalk/MANUAL_TERMS.md`. Where both exist, reconcile unique evidence
   without overwriting the canonical file. For crosswalk-only projects, create
   the inventory from available sources and existing evidence. Do not invent
   missing citations or treat an absent manual as a waiver.
3. Keep manuals, FAQs, and other external material outside tracked source. The
   migration commits only authored summaries and dispositions.
4. Run affected process/reference checks and commit the project migration
   separately from shared tooling. Continue normal pass preparation only after
   the migrated artifacts satisfy the current contract.

## Implementation and Validation

`scripts/reference_review.py` owns planning-context reading, inventory paths,
and gold evidence validation. Pass-start, review-packet, and agent-review
wrappers use it. `scripts/proof_debt.py` owns scoped acknowledgements. The
Makefile, scaffolder, artifact validators, and launcher prompts carry the
corresponding fields and guidance.

Regression coverage exercises placeholder/broken-link gold refusal before CI,
canonical inventories, missing-inventory migration guidance, evidence selected
from the reviewed commit, stale reference inputs, added/removed inventory diffs,
changed-evidence acknowledgement expiry, unrelated-pass persistence, and
per-subject isolation. Old ledger headers must fail validation. Mutation tests
should restore the old failure modes in
disposable copies and demonstrate that the relevant tests fail. Existing
project layouts must also be inspected read-only to identify migration work;
synthetic fixtures alone missed the original location split. Before migration,
old-format projects are expected to fail the new schema checks, not remain green.

Canonical operating rules live in
[PASS_WORKFLOW](agent_playbook/PASS_WORKFLOW.md#corridor-objective),
[DOCUMENTATION](agent_playbook/DOCUMENTATION.md#terminology-crosswalk), and
[QUALITY_REVIEW](agent_playbook/QUALITY_REVIEW.md#reference-coverage).
The [review-packet spec](PROJECT_PASS_REVIEW_PACKET_SPEC.md) and
[proof-debt spec](PROOF_DEBT_SIGNALS_SPEC.md) retain their mechanism details.
This document explains the combined change; it does not replace those contracts.
