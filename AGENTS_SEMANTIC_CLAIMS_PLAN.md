# Semantic Claims Ledger Plan

## Purpose

Clean-room reverse-engineering runs need a way to compare final semantics, not
just final symbol spelling or KPI counts. A polished assembly can still be
wrong if it assigns the wrong owner to a RAM byte, misidentifies a state value,
or documents a data format with the wrong producer/consumer relationship.

The goal is to add a maturity-time evidence ledger that answers "why does this
project believe this semantic claim?" The ledger should make independent
clean-room runs comparable by meaning:

- same meaning, different symbol spelling: acceptable naming variation
- same subject, different meaning: semantic disagreement
- same meaning, different evidence: evidence-quality review target
- claim present in one run and missing in another: coverage gap
- different subsystem boundaries: architecture divergence worth review

This must not become another per-pass chore. The ledger is for subsystem
maturity and gold closeout, not for every small edit batch.

## Current Gap

Existing artifacts each capture part of the story:

- `MEMORY_MAP.md` lists stable RAM/ZP ownership, but usually not the evidence
  chain that proves the ownership.
- `raw_ram_review.csv` records raw-RAM review status and pass provenance, but
  it is too low-level for cross-run semantic comparison.
- `renames.csv` records symbol introductions, but not necessarily the final
  subsystem claim or competing interpretation.
- `*_DX_Systems.md` summarizes stable behavior late in the project, but it is
  intentionally prose-oriented and should not become an evidence ledger.
- dedicated format docs can describe records and streams, but their evidence
  structure is not normalized across projects.
- scorecard rows explain pass outcomes, not final mature semantic claims.

As a result, two clean-room projects can both pass maturity gates while making
different semantic claims in ways that are hard to audit without rereading the
entire assembly and pass history.

## Target Artifact

Add one project artifact:

`projects/<slug>/docs/reverse_engineering/SEMANTIC_CLAIMS.md`

The file is a maturity-time ledger of major evidence-backed conclusions. It is
not a work log and not a replacement for `MEMORY_MAP.md`, data-format docs, or
systems docs.

Each claim is a stable review unit with a unique heading:

```md
## Claim: frame-oam-cursor

Subject: ZP_FrameOamCursor
Kind: RAM/ZP field
Subsystem: rendering / OAM staging
Claim: Byte $3F is the per-frame OAM shadow write cursor shared by title OAM
copy, selected-team staging, metasprite emission, and unused-row hiding.
Confidence: high
Evidence:
- Writers: ContinueNmiFrameAfterDispatch, StageModeSpecificOam,
  StageSelectedTeamOamTemplate, EmitMetaspriteByPointerListId
- Readers: StageSelectedTeamOamTemplate, FinishFrameRenderStagingAndDispatch,
  HideOamRowsFromRawCursor
- Cross-check: all uses advance by OAM_SPRITE_STRIDE or write OAM shadow bytes.
Caveats:
- None. Related selected-team marker byte $3E is a separate overlay.
Canonical docs:
- MEMORY_MAP.md
- raw_ram_review.csv
```

For a data format:

```md
## Claim: ppu-packet-buffer-format

Subject: RAM_PpuPacketBufferBase
Kind: data format
Subsystem: PPU update queue
Claim: Queue records are [length, target_hi, target_lo, PPUCTRL, payload...]
and the stream is terminated by a zero length byte.
Confidence: high
Evidence:
- Producer: QueuePpuPacketHeader
- Consumer: NMI queued-transfer path
- Terminator: FinishFrameRenderStagingAndDispatch writes zero length.
Caveats:
- Direct PPU streams use a separate format.
Canonical docs:
- PPU packet format document
```

## Claim Scope

Required at gold closeout:

- major RAM/ZP ownership families in `MEMORY_MAP.md`
- nontrivial scoped overlays that remain important to edit safely
- major state bytes and their named values
- nontrivial data formats, packet streams, pointer tables, and record families
- major subsystem entry points whose behavior anchors a `*_DX_Systems.md`
  overview
- semantic claims that were contested, inferred, or likely to vary across
  clean-room runs

Optional:

- small helper-local scratch with obvious producer/consumer evidence
- mechanical aliases that exist only to remove raw operands
- one-off constants when the symbol name and call site are self-evident

Excluded by default:

- purely mechanical write-only aliases with no proven reader
- raw-RAM queue rows still marked `unreviewed`, `deferred`, or `revisit`
- scorecard/pass-history provenance
- reference-only terminology that has no assembly mapping yet
- comments that merely restate an instruction, symbol name, or numeric value

If an excluded item could be mistaken for a real semantic claim, record the
exclusion in the existing ledger that owns it, usually `raw_ram_review.csv` or
`WORKING_NOTES.md`; do not create a full semantic claim solely to explain
non-ownership.

## Relationship To Existing Artifacts

`MEMORY_MAP.md`

- Lists stable ownership for day-to-day navigation.
- Nontrivial entries or families should have a corresponding semantic claim by
  gold closeout.
- Mechanical/write-only aliases should not be promoted to `MEMORY_MAP.md`
  unless they have stable reader-facing meaning.

`raw_ram_review.csv`

- Remains the detailed raw-RAM queue and status ledger.
- It may link or name the semantic claim for mature rows, but it should not
  duplicate the evidence text.

`renames.csv`

- Remains the symbol-introduction ledger.
- It should not be used as the final semantic evidence record.

Data-format docs

- Remain the canonical place for field layout, record shape, examples, and
  constraints.
- Each mature nontrivial format should either contain a claim section in the
  required shape or link to a claim in `SEMANTIC_CLAIMS.md`.

`*_DX_Systems.md`

- Remains a late-maturity subsystem overview.
- It may link to relevant claims but must not duplicate evidence chains or pass
  provenance.

`PROGRESS_SCORECARD.md`

- Remains pass history.
- It should not be mined as the final semantic claim ledger.

## Checker Behavior

Add a wrapper:

`make project-semantic-claims-check PROJECT=<slug>`

Suggested implementation: `scripts/project_semantic_claims_check.py`.

Mechanical validation:

- file exists for new/current projects once maturity mode requires it
- claim headings are unique and use `## Claim: <slug>`
- each claim contains required fields:
  `Subject`, `Kind`, `Subsystem`, `Claim`, `Confidence`, `Evidence`,
  `Caveats`, `Canonical docs`
- `Kind` is one of:
  `RAM/ZP field`, `scoped overlay`, `state machine`, `state value`,
  `data format`, `pointer table`, `routine contract`, `subsystem`, `other`
- `Confidence` is one of:
  `high`, `medium`, `inferred`, `mechanical`
- `Subject` symbols that look like ASM identifiers exist in the project ASM,
  unless the claim explicitly marks `Subject: External/reference-only`
- raw `LXXXX` subjects fail
- placeholder subjects such as `StateNN`, `ModeNN`, `FieldNN`, `AddrNNNN`, or
  bare raw `$NN` subjects fail unless the claim is `Confidence: mechanical`
  and the caveat states why it is excluded from semantic ownership
- `Canonical docs` links resolve when they are local markdown paths
- optional: warn, but do not fail, when a `MEMORY_MAP.md` symbol has no claim
  and appears to be a nontrivial RAM/ZP family

The checker should not try to prove the claims. It only verifies that claims
are reviewable and connected to real symbols/docs. Evidence quality remains a
reviewer judgment.

## Maturity Integration

Initial rollout:

- scaffold `SEMANTIC_CLAIMS.md` for new projects with short instructions and
  one commented/template claim
- add `make project-semantic-claims-check`
- run the checker from `project-maturity-check`
- for legacy projects, missing/empty `SEMANTIC_CLAIMS.md` should warn at first
  unless the project declares it has opted into semantic-claims maturity
- for new projects created after the rollout, gold standard requires the file
  and the checker must pass

Do not add the checker to ordinary pass closeout. A pass may add or update
claims when it matures a subsystem, but it is not required for every pass.

## Implementation Batches

### Batch 1: Documentation model

Update playbooks to define the ledger and its ownership.

Expected files:

- `AGENTS.md`
- `agent_playbook/DOCUMENTATION.md`
- `agent_playbook/QUALITY_REVIEW.md`
- `agent_playbook/PASS_WORKFLOW.md`
- `agent_playbook/README.md`

Required wording:

- semantic claims are maturity/gold-closeout artifacts, not per-pass ceremony
- `MEMORY_MAP.md` and data-format docs remain canonical navigation/spec docs
- `SEMANTIC_CLAIMS.md` records evidence-backed final semantic conclusions
- systems docs may link claims but must not duplicate evidence chains
- mechanical/write-only aliases are excluded unless needed to explain a
  non-ownership decision

### Batch 2: New-project scaffold

Add `SEMANTIC_CLAIMS.md` to generated projects.

Expected files:

- `scripts/new_project.sh`
- `agent_playbook/NEW_PROJECT.md`
- `projects/README.md` if command docs mention generated artifacts
- shell tests for scaffold presence and generated-doc links

The scaffold should be explicit that the file may stay sparse until subsystem
maturity and gold closeout.

### Batch 3: Checker and wrapper

Implement the mechanical checker and Make target.

Expected files:

- `scripts/project_semantic_claims_check.py`
- `Makefile`
- `README.md`
- `projects/README.md`
- `tests/shell/cases/pass_workflow_test.sh` or a dedicated shell test file

Test cases:

- valid claim passes
- duplicate claim heading fails
- missing required field fails
- invalid confidence fails
- ASM subject that does not exist fails
- `LXXXX` subject fails
- local markdown canonical-doc link resolves
- `External/reference-only` subject is allowed
- legacy missing file is warning/non-fatal when invoked in legacy mode
- new-project/gold mode treats missing file as failure

### Batch 4: Maturity-check integration

Wire the checker into `project-maturity-check`.

Expected behavior:

- advisory for legacy projects by default
- strict for projects that opt in or are created after the scaffold change
- strict at gold closeout for new projects

Avoid mass-updating every existing project in this batch. The goal is to make
the process available and required for new clean-room validation, not to churn
old histories.

### Batch 5: Optional comparison helper

Only after the ledger shape has stabilized, consider a helper that compares two
projects' claim ledgers:

`scripts/compare_semantic_claims.py <project_a> <project_b>`

Initial comparison can be simple:

- claims present in A but missing in B
- same subject with different claim text
- same claim heading with different subject
- differing confidence
- differing caveats

This is optional and should not block the initial rollout.

## Acceptance Criteria

- New projects contain a scaffolded `SEMANTIC_CLAIMS.md`.
- The playbooks clearly say the ledger is for maturity/gold closeout, not every
  pass.
- `make project-semantic-claims-check PROJECT=<slug>` exists.
- `project-maturity-check` invokes the semantic-claims check with backward
  compatibility for legacy projects.
- The checker validates structure without pretending to prove semantics.
- Existing projects continue to pass normal process gates.
- New clean-room projects have a normalized place to explain final semantic
  claims and evidence.
- Independent reviewers can compare two final projects and identify whether a
  difference is naming-only, evidence-quality, coverage, or semantic.

## Non-Goals

- Do not replace `MEMORY_MAP.md`, data-format docs, `raw_ram_review.csv`, or
  `renames.csv`.
- Do not require a claim for every renamed symbol.
- Do not make every pass update `SEMANTIC_CLAIMS.md`.
- Do not mass-migrate old projects as part of the initial implementation.
- Do not make the checker infer or judge semantic truth.
- Do not use `*_DX_Systems.md` as the evidence ledger.
- Do not make mechanical/write-only aliases look more semantic than they are.

## Open Decisions

1. Should new projects use a project.conf flag such as
   `SEMANTIC_CLAIMS_REQUIRED=1`, or should the presence of the scaffolded file
   imply strict mode?

   Recommendation: use a project.conf flag so legacy projects can opt in
   deliberately and new scaffolds can enable it.

2. Should data-format docs embed claims directly or link to
   `SEMANTIC_CLAIMS.md`?

   Recommendation: allow either, but require the same fields. Avoid forcing a
   separate claim when a dedicated format doc is already the canonical home.

3. Should `Confidence: mechanical` be allowed in `SEMANTIC_CLAIMS.md`?

   Recommendation: allow it only for explicit non-semantic exclusions or
   comparison-relevant mechanical aliases. It should be rare.

4. Should claim headings be stable IDs independent of symbol names?

   Recommendation: yes. Use semantic slugs, not exact symbol names, so a rename
   does not break cross-run comparison.

5. Should claim coverage be computed mechanically from `MEMORY_MAP.md`?

   Recommendation: warn only. Coverage quality is judgment-heavy and should not
   become a noisy hard gate in version 1.

## Review Questions For Implementation

- Does the implementation add maturity-time evidence without increasing
  ordinary pass burden?
- Are mechanical/write-only aliases kept out of stable semantic claims unless
  explicitly justified?
- Can a non-technical user still start a project without understanding this
  file until gold closeout?
- Can an independent reviewer compare two clean-room outputs by claim subject,
  confidence, caveat, and evidence?
- Does the checker avoid false authority by validating structure only?
- Are legacy projects protected from immediate churn?
