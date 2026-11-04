# Structured pass rollout plan

Status: step 1 is complete: [PR #175](https://github.com/khansen/nesrev/pull/175)
merged as `ea2fd0de2`, including service head `40203e10d`. Steps 2 and 3 are not
complete. The [step-2 coverage baseline](STEP_2_COVERAGE.md) maps required
operations, ownership, replays and proposed operating limits before implementation.
It proposes splitting step 2 into three reviewable PRs; that split is pending plan
agreement. The numbers below identify delivery stages, not GitHub PR numbers.

The destination is ordinary full-scale project passes in which implementers and
reviewers work through structured services throughout. Opt-in operation is a
transition state. The trusted service retains source, Git and wrapper execution;
agents receive generation-pinned records and use controlled mutations for every
artifact they are permitted to change. A missing capability stops the operation
and identifies the gap; it does not enable raw-source fallback.

This plan governs service rollout. The separate
[structured-analysis migration plan](../../NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md)
governs assembler-fact consumption inside scripts. Operational instructions and
current limitations remain in the [service README](README.md).

## Step 1 — Promote the exercised service

**Scope:** extract the working rename/comment/document workflow into
project-neutral tooling using the public, pinned XORcyst source model. Preserve
preparation, protected closeout, publication, durable review, window coverage and
local application. Ordinary pass launchers keep their existing behavior during
this step.

**Completion criteria:**

- All configured corpus sources reconstruct byte-for-byte without reopening the
  input source and produce the complete reference PRG. Reference inventory,
  native bindings, scopes, segments and edit-provenance joins remain checked.
- Neutral positive and failing-direction tests cover the editing lifecycle,
  ownership, generation/revision consistency, interrupted recovery, durable review
  and local application. The historical replay passes real project gates; simulated
  gates are labelled as such.
- The four real-pass follow-ups work: comment-only repairs, bounded complete
  previews and review pages, observed-response accounting across resumes, and actionable forbidden
  path diagnostics. Lost or uncertain usage blocks automatic continuation.
- Restricted-client probes preserve reference-media viewing while denying ordinary
  source, shell, edit and Git paths. Reviewer verdicts remain protected. These
  probes make no claim about an untested subscription configuration.
- Existing repository tests pass; independent review has no unresolved blockers;
  CI passes on the submitted revision. Tests with intermittent results are reported
  with their failed attempts, not described as having passed consistently.
- The branch contains no game sources, private replay fixtures, reference media,
  authentication or machine-specific paths. Documentation states unsupported
  operations and artifact-version compatibility explicitly.
- After publication is authorized, the PR is merged. Local implementation or a
  green test run alone does not complete this step.

**Current evidence:** the implementation has a 23-source corpus check, neutral
service tests, native loopback probes, real wrapper replay and repository
regressions. Independent implementation review approved `1d3e5acbf`, including
107 focused tests; the optimized suite, ordinary review suite and full repository
tests subsequently passed on that final head. The preceding readiness slice
passed a disposable 64-rename corridor. The document-history replay covered 983 edits; it is distinct
from the historical workflow replay required above. Partial document views give
the first omitted line on each side, not a list of every omitted location.

Compact use views, gate diagnostics that include the failing `FAIL:` lines,
and standalone Q09 paging are implemented and independently approved. Release
acceptance uses the published XORcyst 2.1.0 archive for both ordinary gates
and structured passes, pinned by release commit, archive checksum and schema hash.
Optional document-diff performance and mixed
line-terminator reporting improvements remain separate follow-ups. The test counts
above describe the original approval, not the growing PR regression suite.
Remote CI passed at `0b99a9180`. At `80140bf66`, Linux passed; macOS failed an
ordinary FCEUX supervisor test before its structured-pass tests ran. Subsequent
fixes landed at `40203e10d`; both Linux and macOS passed on that head in
[CI run 41718944736](https://github.com/khansen/nesrev/actions/runs/41718944736)
before merge. Those are step-1 results, not tests of the proposed step-2 work.
Real inference and default rollout still require explicit owner authorization.

## Step 2 — Complete the normal-pass operation coverage

**Entry criterion:** step 1's service contract is accepted. Before implementation,
freeze a coverage checklist derived from the High-Value Pass Contract, Reviewer
Simulation Checklist, recorded pass sessions and intended next-pass work. Each
obligation must name its read operation, mutation where applicable, owning writer,
generation behavior, positive test and failing-direction test. Prioritize quality
queries using classified historical findings; do not invent a new query suite
merely to fill the checklist.

[STEP_2_COVERAGE.md](STEP_2_COVERAGE.md) is the concrete baseline for this gate.
It also records what to reuse from the earlier analysis-query branches and what
remains unmeasured. Its proposed PR split keeps every obligation below; it does
not authorize a narrower definition of normal passes.

The following are the minimum areas to resolve, not claims of current support:

| Area | Required capability and proof |
|---|---|
| Operands and declarations | Typed expression/operand replacement and declaration insertion; complete native bindings and exact PRG. Cross-routine selections show grouped context before confirmation. Same-valued wrong-meaning or wrong-binding edits must not pass solely on parity. |
| Localization | A typed operation checks every use against the target scope, including repeated local names; an out-of-scope use refuses. |
| Data and layout | Reflow uses producer operand ranges, widths and segment identities. Byte order, operand identity and bindings survive. No consumer assembly parser or evaluator is introduced. |
| Comments and formatting | Create, replace and remove the comment/layout units required by real work; unrelated bytes remain identical. |
| Docs and ledgers | Cover all required authored project artifacts, named shared documents and typed authored columns in mixed ledgers, including `data_blob_dispositions.csv`, `policy_baseline.csv` and `raw_ram_review.csv`. Generated values, wrapper-owned fields and review history remain protected; newly created rows cannot fabricate results. |
| Project tools and runtime evidence | Provide required trace-tool edits and fixed capture/decoding operations. Agent-authored code/data runs only in a sandbox without bulk source, source-bearing host access or service credentials. Symbols and evidence come from the model and identify their generation. |
| Navigation and quality checks | Support the required scope, use, control/data-flow, value-in-context, prose and unused-symbol checks. Keep bank/segment identity in address queries. Queries surface evidence for judgment; they do not turn a plausible name into a proven fact. |
| Wrapper obligations | Map next-pass, pass-start, verify/process/docs, inventory, prior reuse, comment audit, data recovery/decoding, tracing, review packet and closeout to service results. Diagnostics permit repair without an operator reading a private log. No unattached assembly excerpts or mixed-generation evidence reach the agent. |

**Completion criteria:**

- Every applicable checklist row has an implemented operation and passing positive
  and negative evidence. An absent operation is an open requirement, not a completed
  row labelled "unavailable". Genuine non-applicability needs evidence.
- Deterministic replays cover the raw accesses and edits required by representative
  recorded passes, including a large rename/review range, mixed artifacts and
  banked code. Replays name the replacement structured operations. Known historical
  defects have defective/corrected checks; synthetic cases are identified.
- Enabled Tier 1 quality queries have their relevant historical replays, or an
  explicit absence of a recoverable case, and applicable holdouts. Tier 2 doc and
  judgment checks remain the existing playbook checklist unless evidence justifies
  a dedicated query. The unfinished findings census is reported as unfinished.
- A multi-batch rehearsal exercises repair, publication across review windows,
  restart in a fresh process and approved local application without direct edits
  or operator-relayed gate evidence.
- Full-amend latency, peak temporary space and retained growth are measured on
  the largest configured sources. Numeric operating limits are fixed in the
  checklist before implementation; the results meet them and existing wrapper
  non-regression requirements. Shared locking and cleanup prevent concurrent
  cooperating runs from exceeding the planned disk allowance.
- Corpus, affected wrapper and service regressions pass. Independent review and
  CI pass, and the authorized PR is merged.

Keep this PR bounded by the frozen checklist. If it cannot fit in one reviewable
PR, propose a split before expanding the work; the completion gates do not change.
A requested deferral that narrows "normal passes" needs an explicit owner decision
and an updated rollout claim. Missing producer facts are fixed in XORcyst under
its own contract/review rather than reconstructed in NESrev.

## Step 3 — Make structured passes the default

**Entry criteria:** steps 1 and 2 are accepted, with no missing capability for the
intended normal-pass scope. The owner selects the supported client configuration
and explicitly authorizes the real-run budget; earlier prototype authorization
does not carry forward to another run.

**Scope:** normal pass launchers, role instructions and handoffs use the service
by default. Trusted wrappers remain underneath it. Operator maintenance commands
may remain, but agent profiles expose no direct source/artifact mutation bypass.

**Completion criteria:**

- Normal launch and resume paths select the structured service without a special
  opt-in flag. Startup checks the actual client's offered tools, source-free
  workspace, reference-media access, role authority and pinned code. Subscription
  connectors and interactive restriction are tested for the chosen real setup;
  fake-API results alone do not establish that boundary.
- Access-denial tests cover alternate source copies/worktrees, Git object reads,
  path discovery and script-built paths. Shell/interpreter tools are disabled, or
  OS-sandboxed with default-deny reads/traversal inherited by children and no route
  to source-bearing services. A broken hook does not make source available.
- After explicit authorization, a current-project corridor selected by the normal
  next-pass process completes with real implementer and reviewer sessions. It
  represents the intended broader use and exercises capability added in step 2;
  it is not restricted to another rename-only case to avoid missing operations.
- All edits, diagnostics, requested repairs and verdicts go through the services,
  with no batch-shape workaround or operator-transcribed evidence. Review covers
  every publication edge, including earlier windows. A fresh session can reopen
  the evidence, and budget/time stops preserve a supported continuation path.
- Canonical closeout and PRG checks pass after the final edits. Approved files and
  review history land as an ordinary unsigned local commit on `projects`.
- The launcher/instruction changes have independent review and green CI and are
  merged after authorization. Enabling the default happens at a completed pass
  boundary, without invalidating an active editor or rewriting old evidence.
- An unhealthy service refuses launch/resume with a useful diagnostic. Rollback
  selects a reviewed compatible service or stops the run; it never silently
  restores raw-source access to agents.

Reaching these criteria completes the rollout: ordinary full-scale passes use the
services, including all mutable pass artifacts, rather than remaining an opt-in
experiment.

## Decisions and quality claims

This document records the delivery proposal and its gates; it does not authorize
future implementation scope, inference, extensions, pushes, merges or releases.
Only project-neutral promotion branches may be published when requested.
`projects` is never pushed. XORcyst release/version decisions remain separate;
step 1 now targets the official XORcyst 2.1.0 release. Consumer acceptance uses
that released archive before the NESrev PR is opened.

Technical readiness is distinct from evidence that passes improve. The existing
quality-evaluation contract remains: comparable frozen handoff states, fresh
reviews with the same setup/tools, implementer dispositions withheld, archived
findings cross-checked, and size-matching/normalization rules fixed in advance.
Rework history carries its detection confound. A comparison exercise needs its
own authorization, and census/replay requirements are not silently waived by
this rollout plan. No token saving or quality gain is claimed from passing these
functional gates.
