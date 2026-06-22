# Corridor Throughput Plan

## Purpose

This plan addresses a recurring process failure: NES reverse-engineering
projects are still taking on the order of 100-300 passes to approach gold
standard, even after major improvements to `AGENTS.md`, the playbooks, and the
project wrappers.

The current process has raised the quality floor. It prevents many bad
outcomes: unreproducible regeneration, inconsistent naming, stale warnings,
unsafe parity claims, and undocumented process drift. It has not adequately
improved throughput. The process still rewards small, locally safe passes more
than broad subsystem ownership.

The target change is not a return to free-form work. It is bounded free-form
execution: keep hard quality gates, but stop treating generated hot spots as
the pass strategy.

## Current Diagnosis

### What works

- Hard gates provide real value: parity, docs/process checks, naming checks,
  warning-baseline sync, and repository hygiene.
- Tracked NESrev controls and project wrappers make fresh checkouts
  reproducible.
- `renames.csv`, `raw_ram_review.csv`, `WARNING_BASELINE.txt`, and
  `WORKING_NOTES.md` are useful when they capture durable decisions.
- Scorecard rows are useful when they summarize a coherent corridor and explain
  why the pass mattered.
- The playbooks now encode important quality rules that are hard to rediscover
  in each project: comment minimality, ZP/RAM naming, hardware aliases,
  `*_DX_Systems.md` promotion, and raw-RAM overlay restraint.

### What does not work

- `project-next-pass` is described and used as a recommendation engine, but it
  is fundamentally an evidence generator. It ranks what is visible, not what is
  strategically best.
- Generated targets are often local anchors: one owner routine, one table, one
  raw byte family, or one branch cluster. Operators then close exactly that
  target instead of broadening to a subsystem corridor.
- The scorecard/pass mechanism encourages one row per small edit batch. This
  inflates pass count and makes small cleanup commits look like project
  progress.
- Raw-RAM work tends to arrive late because the recommender switches into
  raw-RAM mode after `LXXXX=0`, even though some RAM ownership is best closed
  earlier as part of the subsystem corridor that proves it.
- Guardrails sometimes create false certainty. A green generated plan can make
  the operator less willing to override the tool with a better human-readable
  corridor.
- Generated artifacts are sometimes treated as authoritative state rather than
  disposable evidence.

### Late-Stage Raw-RAM Calibration

Late-stage raw-RAM passes validate the new corridor-objective flow, but they
also show the remaining friction:

- The generated evidence can repeatedly surface a broad setup/reset owner as
  the top raw-RAM candidate even after the operator has correctly marked much
  of that reset cluster as mixed or deferred. The useful work is not the broad
  anchor; it is specific sub-corridors inside or adjacent to it: assignment
  slots, selected path-bucket side effects, draw-order state, path-task timers,
  resolution state, or scoped stream-pointer overlays.
- The operator had to manually convert a broad mixed anchor into actionable
  owner corridors. That is the right operator decision, but the tool should
  make those sub-corridors first-class candidates instead of requiring the
  operator to carve them out every pass.
- Scoped overlays are legitimate progress. If `$08/$09` are proven as a
  direct-stream pointer in one helper while unrelated projection and late-frame
  uses remain raw, the candidate model should describe that as a scoped overlay
  opportunity, not as a reason to avoid the work.
- The project-level maturity picture is still too hard to see. A late-stage
  project can still have hundreds of raw low-address operands, noncompliant
  data labels, raw indirect operands, and substantial callable/global-label
  review inventory. Estimating remaining work required reading the scorecard,
  `unknowns.md`, KPI scripts, and maturity gate output manually.
- Data-label and format debt competes with raw-RAM debt. A recommender that is
  mostly raw-RAM-driven can keep feeding small raw-byte passes even when a
  nearby data-label or format corridor would produce higher readability gain.
- Canonical hardware constant drift remains easy to introduce. A project-local
  constant with a canonical-looking prefix such as `PPUCTRL_` can slip into a
  pass even when the canonical hardware table does not define it.
- The fix should not be more required prose. The operator already records
  corridor objectives. The next improvements should improve tool feedback and
  candidate quality, not add ceremony.

## Target Operating Model

### Bounded free-form corridor execution

The normal work unit is still one coherent subsystem corridor. The difference
is that the operator must choose and state the corridor objective, rather than
accepting the first generated target as the pass.

The generated tools should answer:

- What evidence is currently visible?
- Which labels, tables, raw bytes, and docs are hot?
- Which candidates might be worth opening?
- Which gates are currently red?

The operator should decide:

- Which subsystem corridor is worth owning now?
- What boundary keeps the pass coherent?
- Which generated targets are evidence for that corridor?
- Which generated targets should be ignored or deferred?
- Whether multiple edit batches belong to the same corridor pass.

### Artifact classes

Classify project artifacts into three groups.

| Class | Examples | Rule |
|---|---|---|
| Hard gates | `project-verify`, `project-docs-check`, `project-process-check`, naming checks, warning-baseline sync | Must be current before reporting green. |
| Decision ledgers | `PROGRESS_SCORECARD.md`, `renames.csv`, `raw_ram_review.csv`, `WORKING_NOTES.md`, `WARNING_BASELINE.txt` | Update only when they preserve durable project knowledge or pass outcome. |
| Generated evidence | `next_pass.json`, `current_pass_plan.json`, `xref_*`, temporary pass inventories | Advisory. Do not treat as strategy or authored history. |

### Pass versus commit

A pass is a corridor outcome, not necessarily one commit.

One semantic pass may span multiple small commits or edit batches when they
serve the same corridor and keep verification risk manageable. The scorecard
row should describe the corridor result. It should not force every tiny
mechanical cleanup into a separate conceptual pass.

## Proposed Changes

### Batch 1: Documentation-only operating model

Update `AGENTS.md` and `agent_playbook/PASS_WORKFLOW.md`.

- Rename the mental model from "recommended next pass" to "candidate evidence"
  where appropriate.
- State that `project-next-pass` output is advisory, not authoritative.
- Require an explicit corridor objective before substantial edits.
- Define the minimum corridor objective fields:
  `selected corridor`, `why now`, `expected boundaries`, `generated evidence`,
  `explicitly out of scope`.
- State that a generated local anchor must be broadened into a corridor or
  explicitly rejected.
- Clarify that one pass can contain multiple commits/edit batches.
- Clarify that the scorecard records corridor outcomes, not necessarily every
  small commit.
- Add a strategy checkpoint after repeated low-yield micro-passes.

Expected files:

- `AGENTS.md`
- `agent_playbook/PASS_WORKFLOW.md`
- `agent_playbook/README.md`
- Possibly `agent_playbook/QUALITY_REVIEW.md`

### Batch 2: Tool wording and pass-start behavior

Update wrappers so the CLI reinforces the new model.

- Change `project_next_pass.sh` text output from "Recommended next..." to
  "Candidate evidence..." or "Default candidate...".
- Keep JSON compatibility where possible by retaining existing keys, but add
  new clearer fields such as `candidate_pass` or `candidate_evidence` if useful.
- Update `project_pass_start.sh` to prefer an explicit `TARGET` or objective.
- Consider warning when `project-pass-start` is run without `TARGET` and the
  chosen target is merely the first generated candidate.
- Persist the operator's selected corridor objective in
  `current_pass_plan.md/json`.
- Ensure generated current-pass plans include "why selected" and "out of
  scope" fields when supplied.

Expected files:

- `scripts/project_next_pass.sh`
- `scripts/project_pass_start.sh`
- `tests/shell/cases/pass_workflow_test.sh`

### Batch 3: Scorecard and closeout guidance

Update closeout semantics without breaking existing projects.

- Document that scorecard rows summarize completed corridor outcomes.
- Allow small commit batches to share one scorecard pass when they are one
  coherent corridor.
- Keep `project-pass-closeout` strict about gates and synchronization.
- Do not require a schema change unless the current `notes` column proves
  insufficient.
- If adding structure, prefer appending structured text in `notes` over adding
  new columns that churn every project.

Expected files:

- `agent_playbook/PASS_WORKFLOW.md`
- `scripts/project_pass_closeout.sh` only if enforcement is needed
- `tests/shell/cases/pass_workflow_test.sh` if behavior changes

### Batch 4: Recommender calibration

Reduce micro-pass incentives in `project_next_pass.sh`.

- Rank candidates by actionable corridor value, not raw local density alone.
- Keep recently deferred or already reviewed rows as context, not primary rank
  drivers.
- Group raw-RAM candidates into subsystem families and owner corridors when
  possible.
- Treat broad mixed anchors as evidence containers, not pass targets. If a
  broad setup routine contains deferred bytes plus
  smaller actionable owners, rank the actionable sub-corridors above the broad
  mixed anchor.
- Surface "broaden this anchor" or "narrow this anchor" hints when a hot target
  is local but adjacent evidence points to a better corridor boundary.
- Surface scoped-overlay opportunities explicitly: one proven owner may receive
  a scoped alias while unrelated overlay uses remain raw and active.
- Include data-label and format-debt candidates when they cluster with recent
  work or represent higher readability value than another small raw-RAM pass.
- Add a confidence caveat to output: the tool cannot know strategic project
  value; the operator must choose.

Some of this began with the actionable raw-RAM cluster fix, but the broader
candidate model should be made explicit and tested.

Expected files:

- `scripts/project_next_pass.sh`
- `tests/shell/cases/pass_workflow_test.sh`

### Batch 5: Maturity summary and advisory warnings

Add a lightweight project-level dashboard so strategy decisions do not require
manual synthesis from several artifacts.

Add `project-maturity-summary` or an equivalent target that prints:

- hard maturity blockers: raw low-address operands, raw absolute-ROM operands,
  and noncompliant data labels
- soft review inventory: raw indirect operands, magic immediates,
  undocumented callable procedures, undocumented global code labels, inferred
  annotations, placeholder comments
- recent pass yield: last N scorecard rows with raw-RAM, raw-indirect,
  magic-immediate, warning, and rework movement
- top actionable clusters from current generated evidence
- deferred or mixed clusters that should not be ranked as direct pass targets
- explicit reminder that callable/global-label counts are review inventories,
  not zero-target KPIs

Add advisory-only warnings:

- `project-pass-start` or closeout warns when the selected objective is a tiny
  1-2-site cleanup while larger actionable clusters remain, unless the
  objective explains final-tail cleanup or a strategic unblock.
- `project-next-pass` warns when its top-ranked candidate is a broad mixed
  anchor with smaller actionable sub-corridors beneath it.

Do not fail these warnings initially. The goal is to prompt strategy review,
not block a legitimate expert override.

Expected files:

- `Makefile`
- new or existing script under `scripts/`
- `scripts/project_next_pass.sh`
- `scripts/project_pass_start.sh` or `scripts/project_pass_closeout.sh`
- `tests/shell/cases/pass_workflow_test.sh`

### Batch 6: Canonical hardware constant drift check

Prevent stale-example drift in projects without requiring reviewers to remember
the canonical hardware table manually.

- Parse the canonical hardware constants from
  `agent_playbook/ASM_STYLE.md#hardware-constants`.
- Warn on project-local `.EQU` names with canonical-looking prefixes that are
  absent from the canonical table, such as `PPUCTRL_`, `PPUMASK_`, `PAD_`,
  `OAM_`, `APU_`, and hardware-register aliases.
- Provide an explicit project-local allowlist for truly local composites or
  encoding constants that should not be added to the canonical table.
- Keep this advisory at first. Promote to a strict gate only after existing
  projects are clean or allowlisted.

Expected files:

- `scripts/check_agent_playbooks.py` or a project-process script
- `agent_playbook/ASM_STYLE.md`
- `agent_playbook/PASS_WORKFLOW.md`
- `tests/shell/cases/` coverage for one bad project-local hardware name and one
  allowlisted local composite

## Acceptance Criteria

The implementation is successful if:

- `project-next-pass` no longer reads like the tool is choosing the pass for
  the operator.
- `project-pass-start` records the operator-selected corridor objective.
- The playbooks clearly permit one corridor pass to span multiple commits or
  edit batches.
- The scorecard guidance discourages one row per tiny cleanup when the work is
  part of one corridor.
- Repeated low-yield micro-passes trigger a documented strategy checkpoint.
- Broad mixed anchors are not repeatedly ranked above their actionable
  sub-corridors.
- Scoped-overlay opportunities are visible and do not disappear merely because
  unrelated overlay uses remain raw.
- Data-label/format debt can appear as candidate corridor evidence when it is
  higher value than another raw-RAM micro-pass.
- A maturity summary command gives a one-screen view of hard blockers, soft
  review inventory, recent yield, and top current candidates.
- Canonical-looking hardware constants that are not canonical are warned or
  explicitly allowlisted.
- Existing projects still pass `make test`.
- Existing scorecards and generated pass artifacts remain backward compatible.
- Operators still have hard gates, but are less likely to blindly follow a hot
  generated target.

## Non-Goals

- Do not remove parity, docs/process, naming, or repository hygiene gates.
- Do not remove `PROGRESS_SCORECARD.md`.
- Do not remove `raw_ram_review.csv`.
- Do not make the process fully free-form.
- Do not rewrite existing project histories.
- Do not require a mass scorecard schema migration unless absolutely necessary.
- Do not add more mandatory per-pass prose unless a script consumes it.
- Do not make low-yield or hardware-drift advisories hard failures until the
  current project set has been audited.

## Open Decisions

1. Should `project-pass-start` fail without an explicit `TARGET`, or only warn?
   Recommendation: warn first, fail later only if operators keep accepting bad
   defaults.

2. Should the corridor objective be passed on the command line, stored in a
   small draft file, or edited into `current_pass_plan.md`?
   Recommendation: start with `TARGET` plus generated objective fields; avoid
   interactive editing.

3. Should scorecard pass IDs represent conceptual passes or commits?
   Recommendation: conceptual corridor passes. Commit count can differ.

4. Should `project-next-pass` keep the JSON key `recommended_pass`?
   Recommendation: keep it for compatibility, but add clearer wording and a
   replacement key before any future removal.

5. Should the process include an explicit "major pass" versus "cleanup batch"
   distinction?
   Recommendation: yes in documentation, but avoid new schema until a real
   consumer needs it.

6. Should canonical hardware drift warnings live in the global playbook
   validator or per-project process checks?
   Recommendation: start with per-project process checks because the issue is
   project `.EQU` drift, then consider a global validator helper only if
   duplicated logic appears.

7. Should `project-maturity-summary` be pure text or JSON plus text?
   Recommendation: emit text first for operators; add JSON only when another
   script consumes it.

## Review Questions

- Does this preserve enough guardrail strength to keep agent output consistent?
- Does it give strong operators enough room to choose the right subsystem
  corridor?
- Are generated artifacts now correctly framed as evidence rather than command?
- Is the proposed change small enough to implement without destabilizing
  existing projects?
- Would this have reduced the number of late-stage micro-passes?
- Does the updated candidate model make setup/reset-style mixed
  anchors useful without repeatedly suggesting them as the pass?
- Does the maturity dashboard change operator strategy, or merely summarize
  existing churn?
