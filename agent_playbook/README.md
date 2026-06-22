# Agent Playbook Governance

This directory holds the specialized playbooks that the root `AGENTS.md` routes to. This README is the permanent guide for extending the structure: how to add a rule, where it belongs, what to link instead of duplicate, and which validation commands must stay green.

<a id="execution-model"></a>
## 0. Execution model (permanent)

Organize semantic work by coherent subsystem corridor, not by horizontal work type. Do not stage repository-wide "label pass", "data-format pass", "constant pass", or "documentation pass" sequences. Pass-shape semantics live at [AGENTS.md#high-value-pass-contract](../AGENTS.md#high-value-pass-contract); execution mechanics live at [AGENTS.md#work-order](../AGENTS.md#work-order) (Corridor Execution Contract).

Strict ordering is appropriate only for: new-project intake, session warm-up, wrapper invocation, concrete evidence dependencies inside a corridor (procedure boundaries before localizing labels, producer/consumer proof before stable RAM names), verification, and closeout. Anything outside that list is a corridor-internal scheduling choice, not a sequence to enforce.

The [first-three-pass architecture](NEW_PROJECT.md#first-three-pass-architecture) is recommended front-loading, not strict ordering: it offers candidate architectural corridors, and each selected pass remains corridor-shaped under the Corridor Execution Contract.

Project-maturity dimensions live at [PASS_WORKFLOW.md#project-maturity-dimensions](PASS_WORKFLOW.md#project-maturity-dimensions). Do not reintroduce horizontal pass shapes when adding or moving rules.

<a id="placement"></a>
## 1. Root vs. playbook placement

A rule belongs at **`AGENTS.md` root** if any of the following is true:

- it is a cross-task contract every agent must apply (Mission, Safety Rules, Confidence Protocol, Guiding Pass Philosophy, High-Value Pass Contract, Reviewer Simulation Checklist, Prior-Project Reuse Gate, Session Orientation, Naming Conventions summary, Corridor Execution Contract, Output Philosophy);
- it is the Mandatory Routing Table itself;
- it is the Specialized Rule Index that maps topic-specific rules to their canonical home.

Everything else belongs in a playbook. If a new rule is topic-specific (style, recovery, docs, workflow, review, tooling, project bootstrap), it goes in the playbook that owns that topic. If no existing playbook owns it cleanly, see [Adding a new playbook](#adding-a-playbook).

<a id="ownership"></a>
## 2. Canonical ownership

| Playbook | Owns |
|---|---|
| `ASM_STYLE.md` | naming conventions, local/global label rules, placeholder-name policy, relocatability, literal-base readability, hardware/OAM/joypad/PPU/APU constants, structured-field offsets and overlays, fixed-point naming, state/action constants, label-math syntax, tail-call and parity-preserved redundant-instruction annotations, RAM/ZP naming evidence |
| `DATA_RECOVERY.md` | code-pointer and inline-call recovery, recovery artifacts (`codepointers.csv`, etc.), BIT-skip and overlapping-code cleanup, listing-assisted pointer-blob audits, computed-pointer consumer recovery, orphan opcode-blob detection, pointer-table conversion, PPU packet streams, audio/motion/metasprite/script command-stream formatting, data blob readability and boundary rules, hardcoded length and counter elimination in data consumers |
| `DOCUMENTATION.md` | target-audience/onboarding scope, comment quality and minimality, declaration and procedure comments, raw-address prose prohibition, documentation artifact boundaries, `*_DX_Systems.md` abstraction level, `MEMORY_MAP.md`, terminology crosswalk, data-label format and usage comments, data format documentation (canonical packed-format specification), `WORKING_NOTES.md` inclusion/pruning, optional support-document rules, reference-document use |
| `NEW_PROJECT.md` | project scaffolding, ROM/header intake and mapper/size derivation, initial assembly generation, reference-document processing and crosswalk seeding, warning-baseline bootstrap, first-three-pass architecture, new-project autonomy defaults |
| `PASS_WORKFLOW.md` | resume/warm-up, `project-pass-prep`/`-next-pass`/`-pass-start`, candidate-evidence framing and operator-selected corridor objective (`project-next-pass` is advisory, not an authoritative recommender), pass-versus-commit, low-yield strategy checkpoint, current-pass plan, scorecard synchronization, raw-RAM review queue operation, closeout and verification, generated cache vs. authored artifact distinctions, batching and commit boundaries, RAM symbolization prioritization |
| `QUALITY_REVIEW.md` | readability self-audit, gold-standard assessment, KPI interpretation, expanded reviewer simulation, stale-placeholder / symbol-family / residual-magic-number / global-label audits, project-wide pointer-byte consolidation audit, optional deep-confidence passes, static-vs-runtime gap classification, semantic-claims ledger (maturity/gold-closeout evidence model) |
| `TOOLING.md` | xasm listings/xref options, structured-feature workflow, NESrev regeneration controls, inventory commands, parity-drift diagnostics, command reference, exit-code interpretation, auxiliary-script hygiene |

<a id="one-canonical-home"></a>
## 3. One canonical home

Every rule has exactly one canonical home. Other places **link** to it instead of restating it. A duplicated rule is a future drift bug — when one copy is edited, the other goes stale silently.

- If the rule is most strongly about *how to spell or shape symbols*, it lives in `ASM_STYLE.md`.
- If the rule is most strongly about *how to find or reshape data*, it lives in `DATA_RECOVERY.md`.
- If the rule is most strongly about *what to write in comments or system docs*, it lives in `DOCUMENTATION.md`.
- If the rule is most strongly about *what an agent does during a pass*, it lives in `PASS_WORKFLOW.md`.
- If the rule is most strongly about *how to review a finished or near-finished project*, it lives in `QUALITY_REVIEW.md`.
- If the rule is most strongly about *how to invoke a tool or wrapper*, it lives in `TOOLING.md`.
- If the rule is most strongly about *the new-project intake sequence*, it lives in `NEW_PROJECT.md`.

When a rule touches two playbooks, place it in the one whose ownership the rule's *primary* effect supports, and cross-link from the other.

<a id="anchors"></a>
## 4. Stable semantic anchors

Every section heading that other documents (or external memory) might link to must have a stable anchor:

```
<a id="kebab-case-anchor"></a>
## Section heading
```

Rules:

- **Anchor names are stable contracts.** Once published, do not rename. Add a new one if the rule's scope shifts; keep the old one as a redirect entry in the Specialized Rule Index.
- **Anchor names are kebab-case ASCII**, lower-case, no punctuation.
- **Required root anchors are enforced by `scripts/check_agent_playbooks.py`** (`REQUIRED_ROOT_ANCHORS`). Anything you publish externally that links to `AGENTS.md#...` belongs in that list.
- **The Specialized Rule Index** preserves a stable anchor for each topic-specific rule whose body lives in a playbook. Each index entry's `<a id="...">` keeps inbound links resolving while the link beside it points at the canonical home.

<a id="routing-updates"></a>
## 5. When the routing table or rule index needs an update

Update the **Mandatory Routing Table** in `AGENTS.md` whenever:

- a new task family appears that does not fit any existing route;
- a route's bundle changes (a playbook becomes required for that task, or stops being relevant);
- a playbook is added or removed — see [Adding a new playbook](#adding-a-playbook).

Update the **Specialized Rule Index** in `AGENTS.md` whenever:

- a topic-specific rule's canonical home moves to a different playbook anchor;
- a new topic-specific rule deserves a stable inbound anchor at root;
- an existing anchor under the index is renamed (keep the old anchor as a redirect entry).

If a rule simply moves *within* a playbook (different anchor in the same file), update internal links and the index entry; no routing-table change is needed.

<a id="add-or-move-rule"></a>
## 6. Checklist for adding or moving a rule

1. **Pick the canonical home** using [Root vs. playbook placement](#placement) and [Canonical ownership](#ownership).
2. **Write the rule text** under the appropriate `<a id="anchor"></a>\n## Heading` block. Use kebab-case for the anchor. Add an `## Ownership` entry if the rule introduces a new top-level concept.
3. **Cross-link from other playbooks** that reference the rule. Do not duplicate the rule text.
4. **DRY review** before merging the change:
   - identify the rule's canonical owner per [#one-canonical-home](#one-canonical-home);
   - `rg` for equivalent normative wording in `AGENTS.md` and every operational playbook, including paraphrases and split statements;
   - replace duplicate copies with noun-phrase links to the canonical home (not restated rules with the same effect);
   - verify that any summary or cross-link describes the destination without creating a second independently editable rule (a summary that imposes its own constraint is a duplicate).
5. **If the rule introduces a new stable anchor that external docs may link to**, add it to the Specialized Rule Index in `AGENTS.md` (`<a id="anchor"></a>**Title** — [destination](path)`).
6. **Run** `make check-agent-playbooks` and `make test`. Both must exit `OK (0 warning(s))` — `make` invokes the validator with `--strict`, so any warning fails the gate.
7. **If a budget warning fires**, see [Context-budget limits](#budgets).
8. **If the rule's home turned out to be wrong**, move the body to the right playbook, update inbound links, and leave a redirect entry in the index.

<a id="budgets"></a>
## 7. Context-budget limits

The validator enforces line/word ceilings on `AGENTS.md` and per-route bundles.
The source of truth is `ROOT_LINE_CEILING`, `ROOT_WORD_CEILING`, and
`ROUTE_BUDGETS` in `scripts/check_agent_playbooks.py`; do not copy the numeric
ceilings into this README.

If a new rule pushes a bundle over budget:

- prefer **tightening the rule text** (most root prose has been compacted; new rules should be similarly terse);
- if the rule is genuinely large and only one route is affected, consider whether the rule belongs in a different (smaller) playbook;
- if multiple routes are affected and the budgets feel too tight, calibrate the ceilings in `ROUTE_BUDGETS` — but only with a measured justification, not to absorb sprawl.

<a id="validation"></a>
## 8. Required validation

The following must stay green:

```sh
make check-agent-playbooks      # structural validator only
make test                        # check-agent-playbooks + NESrev JUnit suite
make project-docs-check PROJECT=<slug>
make project-process-check PROJECT=<slug>
```

`check-agent-playbooks` exits non-zero on any failure (broken links/anchors, missing playbook, malformed link, missing required root anchor, missing routing-table entry, unknown playbook in the routing table, obsolete architecture labels in corridor-model files — `"Work Order (Strict Sequence)"` in `AGENTS.md` and `Phase A`..`Phase D` in `AGENTS.md`, `PASS_WORKFLOW.md`, and `DATA_RECOVERY.md`). Warnings (stale numbered references, ceiling/budget overages) are informational only when invoking `scripts/check_agent_playbooks.py` directly without `--strict`; both `make check-agent-playbooks` and `make test` pass `--strict` and fail on any warning.

<a id="adding-a-playbook"></a>
## 9. Adding a new playbook

A new playbook is justified when **both** are true:

- an ownership cluster exists that does not fit any current playbook (the topic is genuinely orthogonal, not a sub-aspect of an existing one), and
- the cluster is large enough that putting it in an existing playbook would push that playbook past its share of the relevant route budget.

To add one:

1. Create `agent_playbook/<NAME>.md` with the standard skeleton:
   ```markdown
   # <NAME> Playbook

   <one-paragraph description of what this playbook owns and how it
    relates to neighbors>

   ## Ownership

   This playbook owns:

   - …
   ```
2. Add the new file to `REQUIRED_PLAYBOOKS` in `scripts/check_agent_playbooks.py`.
3. Add the new playbook to the relevant routing-table rows in `AGENTS.md`.
4. Add an entry to the [Canonical ownership](#ownership) table above.
5. If any new route would include the new playbook, sanity-check the bundle's line/word totals against `ROUTE_BUDGETS` and either fit within the existing budget or add a calibrated new bucket.
6. Run `make check-agent-playbooks` and `make test`.

To remove a playbook, reverse the steps: move its rules to their new homes (preserving anchors via the Specialized Rule Index where external links exist), drop the file, drop the `REQUIRED_PLAYBOOKS` entry, drop it from routing-table rows, and re-validate.
