# Universal Project Gates Migration Plan

## Purpose

Bring every NESrev project under one current quality contract. A project must
not be able to select which repository gates apply by setting or omitting a
flag in `project.conf`, by omitting the artifact that triggers a check, or by
using an effectively infinite KPI ceiling.

The target state is simple:

- `project.conf` describes project facts, never quality policy.
- Every applicable gate runs for every project.
- Applicability is derived from repository facts, not a project-controlled
  opt-in.
- Deterministic defects fail immediately.
- Heuristic findings are either resolved or explicitly dispositioned; they are
  not hidden by disabling the check.
- Pass-time gates permit honestly recorded unfinished work, while maturity
  gates reject it.
- A corpus-wide command proves that a newly added or old project cannot escape
  the common contract.

This is both a tooling migration on `master` and a corpus retrofit on the
local-only `projects` branch. The two sides must be prepared and landed as one
coordinated change. The `projects` branch is never pushed.

## Problem Statement

NESrev currently has four different ways for an older project to bypass a
modern check:

1. `*_REQUIRED` flags in `project.conf` conditionally invoke a check or select
   its strict mode.
2. `NESREV_RECOVERY_STATUS` defaults by omission to `legacy`, an enum value
   that suppresses or weakens checks even though it looks like project data.
3. Some wrappers run a checker only if its ledger already exists, so omitting
   the ledger suppresses the checker.
4. KPI files use `999999` as a practical no-limit value. The KPI command runs,
   but it cannot catch a realistic regression.

This makes a green result mean different things for different projects. It
also allows a legacy project to retain a historical quality level indefinitely
without an explicit debt record.

## Definitions

### Mandatory execution

A mandatory check is invoked for every project by the canonical wrapper. A
project cannot suppress it in `project.conf` or by deleting an input file.

### Hard gate

A deterministic violation exits nonzero. Examples include binary drift,
malformed or missing canonical ledgers, stale generated inventories, unresolved
required labels, confirmed embedded pointers, invalid scorecard lifecycle, and
readability forms covered by an exact lexical rule.

### Mandatory advisory

Some analyses intentionally produce review candidates rather than proof of a
defect. These analyses must still run for every project. Their operational
errors are hard failures. Their findings must eventually be resolved or
recorded in a validated disposition ledger; a project-wide off switch is not
an acceptable disposition.

### Pass-time completeness

Pass-time process gates require canonical artifacts, valid schemas, and honest
statuses. Values such as `queued_static_pass`, `runtime_gated`, or an open
deferral may be valid while work remains.

### Maturity completeness

Maturity gates reject missing evidence, queued work, open maturity debt, sparse
semantic claims, and other provisional states. A project may continue semantic
passes while failing maturity; it may not claim gold.

## Configuration Boundary

`project.conf` may continue to contain facts that differ by project:

- asm, ROM, output, documentation, warning-baseline, and inventory paths
- mapper-derived ROM ranges and CPU bases
- NESrev recovery-control paths and an explicit recovery-discovery fact:
  `pending`, `none`, or `configured`
- genuinely project-shaped thresholds whose meaning cannot be universal,
  provided they are bounded and cannot disable a gate

It must not contain a boolean, enum value, sentinel, omitted default, or other
selector that enables, disables, or weakens quality policy.

Remove these policy switches:

- `SEMANTIC_CLAIMS_REQUIRED`
- `PROCEDURE_CONTRACTS_REQUIRED`
- `LEGACY_RETROFIT_REQUIRED`
- `WORKING_NOTES_MATURITY_REQUIRED`
- `PROOF_DEBT_REQUIRED`
- `DATA_FORMAT_TARGETS_REQUIRED`
- `DATA_BLOB_DISPOSITIONS_REQUIRED`
- `EMBEDDED_POINTER_AUDIT_REQUIRED`
- `BASE_READABILITY_REQUIRED`
- `BASE_READABILITY_EQU_REQUIRED`
- `SCORECARD_LIFECYCLE_REQUIRED`

Add a project-configuration schema check that rejects these names if they
reappear. Do not merely ignore them: a stale flag that appears meaningful is a
future false assurance.

`NESREV_RECOVERY_STATUS` currently mixes a genuine discovery fact with a
twelfth policy selector. Its omitted/default `legacy` value suppresses hard
terminology-crosswalk validation, makes the pass-1 analogue optional, and
relaxes stale scorecard-placeholder validation. Split those responsibilities:

- keep the status only as the explicit `pending` / `none` / `configured`
  recovery-discovery fact used by intake and regeneration;
- delete the permissive `legacy` value and default;
- require every tracked project to declare `none` or `configured` after its
  recovery discovery has been audited;
- run crosswalk-header, pass-1 analogue, and stale scorecard-placeholder checks
  universally, independent of recovery status.

The configuration-policy test must inspect every project-config-sourced
variable used in a wrapper conditional, not merely names matching
`*_REQUIRED`. A fact variable may select data or parameters; it may not select
whether a quality check runs or whether that check is strict.

Explicit one-run workflow modes such as `ALLOW_UNRESOLVED_LXXXX=1` during an
unfinished semantic pass and the audited `ALLOW_TRAILING_BYTES=1` intake
override are not persistent project opt-ins. They may remain only where the
strict closeout/maturity path cannot accept them and their use is reported in
the resulting evidence.

## Current Corpus Baseline

Measured on local `projects` at `c01a10ae5`, with process tooling from
`master` at `13e40f504`.

### Opt-in coverage

| Policy | Enabled today | Observed universal result |
|---|---:|---|
| Semantic claims | 8/22 | 8 pass maturity; 14 need a ledger and real claims |
| Procedure contracts | 7/22 | All 22 meet the current minimum |
| Legacy retrofit marker | 4/22 | Only the four enabled projects carry the current marker |
| Working-notes maturity | 4/22 | 20 pass at 120 lines; Urban Champion and Zelda fail |
| Proof-debt analyses | 2/22 | The advisory group is silent for 20 projects |
| Data-format targets | 4/22 | Four files exist; only Balloon Fight and Kid Icarus pass maturity |
| Data-blob dispositions | 3/22 | Five files exist; only Balloon Fight and Kid Icarus pass maturity |
| Embedded-pointer audit | 1/22 | 21 pass; Zelda exposes one confirmed raw pointer table |
| Immediate base readability | 22/22 | Already universal in practice; the flag is redundant |
| `.EQU` base readability | 0/22 | 19 projects fail, with 516 exact lexical fixes |
| Scorecard lifecycle | 2/22 | 7 pass; 15 require normalization |
| Explicit non-legacy recovery status | 8/22 | 14 omit it and inherit the weaker `legacy` policy path |

### Canonical-artifact coverage

| Artifact | Present |
|---|---:|
| `SEMANTIC_CLAIMS.md` | 8/22 |
| `inventory/data_format_targets.csv` | 4/22 |
| `inventory/data_blob_dispositions.csv` | 5/22 |
| `inventory/data_extent_assertions.csv` | 19/22 |
| `inventory/embedded_pointer_targets.csv` | 22/22 |
| `inventory/split_pointer_targets.csv` | 22/22 |
| `inventory/deferrals.csv` | 2/22 |
| `inventory/proof_debt_acknowledged.csv` | 0/22 |

Header-only ledgers are acceptable only where their contract permits an empty
state. Do not invent semantic claims, dispositions, or not-applicable results
to make an artifact nonempty.

### KPI escape hatches

Eighteen of 22 projects contain at least one `MAX_*=999999` value. There are 92
such ceilings:

| KPI ceiling | `999999` projects |
|---|---:|
| Active raw low addresses | 15 |
| Active absolute-ROM operands | 0 |
| Active magic immediates | 16 |
| Active branch literals | 17 |
| Inferred annotations | 17 |
| Placeholder comments | 0 |
| Undocumented procedures | 6 |
| Undocumented global code labels | 6 |
| Undocumented data labels | 15 |

### Confirmed immediate blockers

- Quantity-suffixed `.EQU` readability has 516 hex literals across 19
  projects. Devil World, Donkey Kong, and Golf are already clean.
- The embedded-pointer audit identifies one confirmed unrelocated structure in
  Zelda. Implementation disproved the three original Kung Fu reports: their
  source and destination indexes differ because they are one-byte hitbox-table
  lookups, not block copies. The generic proof now requires the same traversal
  index, while Zelda still needs semantic pointer representation rather than an
  allowlist or disabled audit.
- Fifteen scorecards fail the current lifecycle checker.
- Urban Champion and Zelda exceed the current 120-line working-notes maturity
  budget.
- Fourteen projects lack maturity-grade semantic claims.
- Most projects lack complete data-format and data-blob disposition evidence.

## Target Wrapper Contract

### `project-verify`

Run unconditionally:

- binary/warning parity and unresolved-label policy
- every KPI with a finite reviewed ceiling
- `.DW`, embedded `.DB`, and split `.DB` inventory synchronization
- embedded-pointer audit
- immediate and quantity-`.EQU` base-readability strict checks
- pointer-table body checks
- comment, inferred, data-label, branch-site, and extent checks

The three pointer inventories are canonical generated artifacts. Their checks
must not be guarded by `-f`; a missing file is an actionable failure.

### `project-process-check`

Run unconditionally:

- required process-artifact and ledger schema checks
- scorecard cell and lifecycle checks
- generated-inventory completeness and freshness
- raw-RAM owner synchronization when a raw-RAM ledger is present or structured
  evidence says one is required
- terminology-crosswalk header validation for every project
- proof-debt analyses
- data-format target validation in required process mode
- data-blob disposition validation in required process mode
- data-extent omission scan and the existing naming/hardware checks

Advisory analyses remain conservative. Replace the global opt-out with a
validated disposition path where persistent findings need acknowledgement.

### `project-docs-check`

Always validate `SEMANTIC_CLAIMS.md` in strict pass-time mode. Missing files are
failures. A structurally valid sparse ledger is allowed during ordinary passes
when the project has not reached subsystem maturity.

The stale scorecard-placeholder check inside `check_docs.sh` must also be
universal. Recovery status may inform displayed recovery facts, but it must not
exclude a project from documentation policy.

### `project-prior-reuse-check`

Always require the pass-1 scorecard to record either a valid analogue project
or the explicit `Analogue: none` disposition. Remove the recovery-status-based
`--optional` path. The semantic comparison remains advisory unless its own
strict mode is explicitly requested; the authored analogue decision is
mandatory.

### `project-maturity-check`

Always enforce:

- full embedded-pointer strictness
- procedure/global-contract audit minimums
- semantic claims in maturity mode
- working-notes budget
- data-format targets in required maturity mode
- data-blob dispositions in required maturity mode
- a universal, live-validated policy-baseline audit marker
- existing raw-address, data-label, pointer-table, and extent hard gates

Replace `legacy-retrofit-audit:` with the neutral
`policy-baseline-audit:` scorecard marker and require it for every project at
maturity. Rename the checker accordingly while preserving its live denominator
cross-checks for procedure and global-code-label detail rows and its semantic
claims validation. New projects write the same marker during gold audit; old
projects add it through the retrofit. There is no project-level enable flag.

### `project-ci`

Continue to call verify, process, maturity, and docs checks in a fixed order.
No child wrapper may select a weaker path from project configuration.

### `project-maturity-summary`

The maturity summary is a reporting surface rather than a hard gate, but it is
inside the migration because operators use it to choose work. Remove its
data-format/data-blob `-f` branches and proof-debt opt-in branch. It must always
summarize the canonical ledgers and universal proof-debt signals, reporting a
missing required ledger as a defect rather than as an optional absence.

## Applicability Without Opt-ins

Some checks apply only when source facts make them relevant. Derive that state
instead of asking the project to opt in.

- An optional `WORKING_NOTES.md` is treated as zero lines when absent, but the
  maturity checker still runs.
- A raw-RAM ledger becomes required when structured pass evidence reports raw
  low-address review work; its absence is not controlled by a boolean.
- Empty pointer inventories are represented by header-only canonical CSVs;
  deletion does not mean not applicable.
- Data-format families use explicit `absent_not_applicable` rows supported by
  review, not a missing ledger.
- Runtime-gated work is represented by a disposition and capture plan, not by
  disabling the checker.

## Migration Workstreams

### Phase 1: Universal gate framework

Implement on a process/tooling feature branch rooted at current `master`:

1. Remove the eleven quality booleans and their defaults; remove the
   `NESREV_RECOVERY_STATUS=legacy` default and decouple the remaining recovery
   fact from quality-policy conditionals.
2. Make wrapper invocations unconditional with the pass-time/maturity modes
   defined above.
3. Add a canonical artifact manifest used by process checks and tests.
4. Add a `project.conf` policy-field rejection check.
5. Make generated and authored input absence produce a precise remediation
   message.
6. Update `project-maturity-summary`, `new_project.sh`, playbooks, templates,
   and the embedded-pointer audit specification so none describe legacy opt-in
   behavior.
7. Add a test that enumerates config-derived wrapper conditionals and rejects
   any fact variable that selects whether a quality check runs or whether it is
   strict.
8. Add a test that enumerates the canonical wrappers and proves every project
   receives the same quality-check set.

Do not land this phase alone while the local projects corpus cannot pass its
pass-time gates.

### Phase 2: Mechanical corpus prerequisites

Prepare local-only project commits without weakening any checker:

1. Normalize the 15 failing scorecards.
2. Convert the 516 quantity-suffixed `.EQU` values from hex to decimal.
3. Resolve Zelda's confirmed embedded-pointer finding symbolically. Keep a
   regression fixture for the disproved Kung Fu shape so reused scratch bytes
   cannot turn an indexed coordinate lookup into a false block-copy proof.
4. Add missing header-only canonical ledgers where an empty state is valid.
5. Add missing `data_extent_assertions.csv` files with only the schema until
   actual extent evidence supports rows.
6. Audit recovery discovery for the 14 projects that currently inherit
   `legacy`, then record explicit `none` or `configured` facts. Do not translate
   omission mechanically to `none`.
7. Normalize those projects' crosswalk headers, pass-1 analogue decisions, and
   stale scorecard placeholders before the recovery-policy branches are
   removed.
8. Run `project-verify` after every project's symbolic or representation
   batch; never batch verification across multiple symbolic shifts.

The `.EQU` conversion is lexical but still touches assembly. Preserve byte
identity project by project and do not combine it with semantic renaming.

### Phase 3: Honest evidence retrofit

This phase cannot be solved by scaffolding alone:

1. Create semantic-claims ledgers for the 14 missing projects from existing
   mature source/docs and direct producer/consumer evidence.
2. Populate canonical data-format family dispositions for every project.
3. Populate data-blob dispositions from structured coverage and consumer
   evidence.
4. Normalize deferral and proof-debt acknowledgement ledgers.
5. Prune or promote Urban Champion and Zelda working notes.
6. Add one `policy-baseline-audit:` scorecard marker per project after the live
   procedure/global detail rows and semantic-claims state have actually been
   reviewed; migrate the four historical `legacy-retrofit-audit:` markers.
7. Record explicit queued/runtime-gated states where evidence is genuinely
   incomplete; do not write filler claims or false `absent_not_applicable`
   rows.

Pass-time gates should become green after honest queues are recorded. Maturity
may remain red until each project completes the underlying review.

### Phase 4: Finite KPI ratchets

1. Reject `999999` and other configured sentinel ranges in the KPI config
   checker.
2. After all Phase 2 representation changes and Phase 3 evidence/source edits
   that can affect a KPI are final, remeasure every KPI. Do not calibrate from
   the pre-retrofit counts recorded in this plan.
3. Replace each sentinel with that post-retrofit measured count as the initial
   anti-regression ceiling when immediate zero is not justified.
4. Record that initial calibration as legacy debt, not gold evidence.
5. Burn ceilings down through coherent semantic/readability passes.
6. For maturity-hard categories such as raw addresses and undocumented data
   labels, keep the existing zero requirement regardless of the pass-time
   ceiling.
7. Reject unexplained ceiling increases. Intentional regressions must use the
   scorecard convention and identify the semantic gain.

An exact current baseline is a temporary ratchet, not completion. It prevents
new debt immediately while preserving an honest work queue.

### Phase 5: Corpus-wide enforcement

Add two aggregate commands:

```sh
make projects-policy-check
make projects-ci
```

`projects-policy-check` must be ROM-independent and run configuration, artifact,
schema, process, docs-structure, and finite-ceiling checks for every tracked
project. It is suitable for normal repository CI.

`projects-ci` runs the full per-project CI sequence locally when the untracked
commercial reference ROMs are available. It must report every project and a
summary; it must not silently skip a project with a missing gate input. Missing
private ROMs are explicit environment failures, not project exemptions.

Project discovery must come from the tracked project set, not a hand-maintained
allowlist that can omit an old project.

## Tests and Bad-Direction Proofs

The implementation is incomplete until these mutations turn red:

1. Add a removed `*_REQUIRED=0` field to one project config.
2. Omit `NESREV_RECOVERY_STATUS` or restore its permissive `legacy` default.
3. Make recovery status suppress crosswalk, analogue, or docs-placeholder
   validation again.
4. Delete a canonical ledger from one fixture project.
5. Restore an `if [[ "${..._REQUIRED}" == "1" ]]` wrapper guard.
6. Restore an `if [[ -f ledger ]]` presence-triggered skip in a gate or the
   maturity summary.
7. Change one KPI ceiling to `999999`.
8. Remove one project from aggregate project discovery.
9. Make an advisory checker crash while producing no findings.
10. Change a maturity checker to accept a queued or sparse artifact.
11. Change pass-time validation to require invented mature content rather than
   accepting an honest queued state.

For each mutation, run the real repository test runner. Before trusting the
result, inject a guaranteed failure at the same position in the same test
function and confirm the harness reports it.

## Corpus Validation

For every project, record:

- `project-verify` exit status
- `project-process-check` exit status
- `project-docs-check` exit status
- `project-maturity-check` exit status
- remaining honest maturity failures by category
- KPI measurements and finite ceilings
- canonical artifact presence/schema status
- embedded-pointer audit result
- scorecard lifecycle result
- `.EQU` readability count

The migration report must distinguish:

- pass-time green from maturity green
- an absent finding from an acknowledged finding
- a current measured ratchet from a gold-standard zero
- an artifact that exists from an artifact whose evidence has been reviewed

Aggregate totals are not enough. Investigate per-project outliers, especially a
single project that differs from an otherwise uniform corpus pattern.

## Pre-Landing Implementation Results

The implementation was prepared on `feat/mandatory-project-gates`, with the
co-dependent corpus retrofit on the local-only
`retrofit/universal-project-gates` branch. These results describe the complete
pre-landing state; the final commit identities may change when the corpus
branch is rebased over the reviewed tooling head.

Universal pass-time enforcement is green:

- `make projects-policy-check` passes all 22 tracked projects. It discovers the
  projects from tracked `project.conf` files and runs the process, docs,
  schema, finite-ceiling, recovery-policy, proof-debt, and canonical-artifact
  checks without a project opt-in.
- `make project-verify PROJECT=<slug>` passes all 22 projects after the final
  retrofit edits. Twenty pass strictly. Hogan's Alley and Zelda pass with the
  documented one-run `ALLOW_UNRESOLVED_LXXXX=1` semantic-pass allowance; both
  fail the unresolved-label check without it.
- All eight canonical authored/generated artifact classes in the baseline
  table are present for 22/22 projects, and every project records an explicit
  recovery fact: 10 `configured`, 12 `none`, zero omitted or `legacy`.
- The 516 quantity-suffixed `.EQU` operands were converted without binary
  drift. No `999999` KPI sentinel remains; every former sentinel is replaced
  by its post-retrofit measured finite ceiling.
- The embedded-pointer audit is universal. Its block-copy proof now requires a
  shared traversal index, rejecting the three disproved Kung Fu findings while
  the Zelda pointer table is represented symbolically.
- All 22 semantic-claims ledgers contain validated, evidence-backed claims.
  Sparse ledgers remain maturity debt rather than being filled with invented
  claims.
- Structured coverage reports 3,799 candidate data spans. Existing reviewed
  rows covered 863; the remaining 2,936 are explicit
  `queued_static_pass` rows with their measured size and structured reason.
  No candidate is undispositioned. The 22 data-format ledgers contain 28
  documented, one evidence-backed `absent_not_applicable`, 202 queued, and 12
  not-yet-reviewed family rows.
- Every scorecard has a live-denominator `policy-baseline-audit:` marker. Six
  projects have complete procedure/global-code review fractions; the other 16
  record exact incomplete fractions and fail maturity. The historical
  `legacy-retrofit-audit:` marker is gone.
- Urban Champion's working notes were pruned from 150 to 79 lines. Zelda's
  notes were pruned from 225 to 64 lines, with stable screen-feature and audio
  facts promoted to canonical format documentation.

Maturity was then run separately for every project with fresh pass-prep
caches. All 22 fail for explicit project debt; none fails because a checker was
skipped, a canonical artifact was missing, or a structured blob candidate was
undispositioned:

| Project | Remaining maturity failures |
|---|---|
| Balloon Fight | policy-baseline audit |
| Baseball | policy-baseline audit; data formats; data blobs |
| Clu Clu Land | policy-baseline audit; data formats; data blobs |
| Devil World | policy-baseline audit; data formats; data blobs |
| Donkey Kong | data formats; data blobs |
| Donkey Kong 3 | data formats; data blobs |
| Donkey Kong Jr. | data formats; data blobs |
| Donkey Kong Jr. Math | data formats; data blobs |
| Duck Hunt | policy-baseline audit; data formats; data blobs |
| Excitebike | policy-baseline audit; data formats; data blobs |
| Golf | policy-baseline audit; data formats; data blobs |
| Hogan's Alley | raw-address debt (264); noncompliant data labels (97); policy-baseline audit; data formats; data blobs |
| Ice Climber | policy-baseline audit; data formats; data blobs |
| Kid Icarus | policy-baseline audit |
| Kung Fu | policy-baseline audit; data formats; data blobs |
| Mario Bros. | data formats; data blobs |
| Metroid | data formats; data blobs |
| Pinball | policy-baseline audit; data formats; data blobs |
| Popeye | policy-baseline audit; data formats; data blobs |
| Tennis | policy-baseline audit; data formats; data blobs |
| Urban Champion | policy-baseline audit; data formats; data blobs |
| Zelda | symbolic pointer-table bodies; raw-address debt (5,467); noncompliant data labels (85); policy-baseline audit; data formats; data blobs |

This is the intended migration boundary: pass-time policy is universal and
green, while maturity remains an honest work queue. The corpus branch has not
been and must never be pushed.

## Atomic Landing Sequence

The tooling and corpus are co-dependent.

1. Prepare and review the process/tooling branch from current `master` without
   touching `projects/`.
2. Prepare the required local-only project retrofit commits on `projects`.
3. Land and push `master` explicitly.
4. Rebase local `projects` onto the new `master` and replay/retain all retrofit
   commits as one operator action.
5. Run no project gate in the unsupported interval between the tooling rebase
   and the project retrofit state.
6. Run the corpus policy check, then the full available local corpus checks.
7. Never push `projects`.

If one universal gate cannot be activated safely in the same batch, split the
tooling work by gate family, but each activation must still land atomically with
its complete corpus prerequisite. Do not restore a per-project switch as a
staging mechanism.

## Acceptance Criteria

The migration is complete when all of the following are true:

- No quality-policy `*_REQUIRED` field remains in `project.conf`, defaults,
  scaffold output, wrapper logic, playbooks, specs, or tests.
- `NESREV_RECOVERY_STATUS` has no `legacy` value or permissive omission
  default; all projects record an explicit recovery fact.
- Crosswalk-header, pass-1 analogue, and stale scorecard-placeholder checks do
  not branch on recovery status.
- The config checker rejects reintroduction of a removed policy flag and any
  config-derived conditional that weakens or skips a quality check.
- No gate is skipped because its ledger is absent.
- Every canonical project artifact is present or its optional absence is
  handled by a universal, fact-derived rule.
- Both base-readability classes run strictly for every project.
- The embedded-pointer audit runs for every project.
- Semantic claims, procedure contracts, scorecard lifecycle, working notes,
  data formats, and data blobs have universal pass-time and maturity behavior.
- Proof-debt analyses run for all projects and persistent findings have a
  validated disposition path.
- `project-maturity-summary` reports the universal artifact and proof-debt
  contract without presence or policy opt-ins.
- Every project carries a live-validated `policy-baseline-audit:` marker at
  maturity; the legacy marker and enable flag no longer exist.
- No KPI ceiling uses `999999` or another disabling sentinel.
- Every tracked project is discovered by `projects-policy-check`.
- The corpus has no unreported pass-time failure.
- Remaining maturity failures are explicit project debt, not skipped checks.
- `master` contains only tooling/process changes from this migration.
- Local `projects` contains the corpus retrofit and has never been pushed.

## Recommended Execution Order

1. Build the policy/config linter and aggregate project discovery first.
2. Remove recovery-status policy coupling and audit the 14 implicit-legacy
   projects' recovery facts, crosswalk headers, analogue decisions, and stale
   scorecard placeholders.
3. Make scorecard lifecycle and `.EQU` readability universal; their debt is
   exact and inexpensive to verify.
4. Make the embedded-pointer audit universal after fixing Zelda and pinning the
   Kung Fu false-positive correction.
5. Require canonical ledger presence and strict pass-time schemas.
6. Make semantic/data-format/data-blob maturity universal while retaining
   honest queued pass-time states.
7. Replace the legacy retrofit marker with the universal policy-baseline audit.
8. Remove KPI sentinels and establish finite post-retrofit ratchets.
9. Make proof-debt execution and dispositions universal, including the
   maturity summary.
10. Run the full corpus audit and record which projects remain genuinely below
   maturity.

This order removes silent bypasses early without manufacturing evidence or
forcing all historical semantic debt into one unreviewable commit.
