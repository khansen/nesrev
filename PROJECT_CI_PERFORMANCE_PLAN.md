# Project CI Performance Plan

Status: CI-P1 merged in [PR #107](https://github.com/khansen/nesrev/pull/107).
CI-P2's instruction-producer prerequisite is complete; its validated bundle is
next. CI-P3 is conditional; CI-P4's text indexes are deferred.
Updated 2026-09-08.

## Purpose and ownership

Reduce the work performed by `make project-ci` without weakening gates, changing
inventory semantics, or gaining time by skipping checks or changing failure order.
The measured bottlenecks were per-constant subprocess loops, repeated assembly,
and repeated source analysis—not an inherent limitation of shell or Python.

The [structured-analysis migration plan](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#performance-work-and-migration-priority)
owns architectural sequencing and assembler schemas. This document owns
performance scope, acceptance criteria, and measurements. CI-P identifiers name
scopes, not four consecutive optimization projects: design shared production
alongside the instruction artifact, migrate consumers, then re-profile before
selecting further optimization. Do not optimize parsers awaiting replacement as
a competing workstream.

Game-specific reproduction commands, input fingerprints, diagnostic profiles,
and detailed results belong in the local-only companion
`projects/PROJECT_CI_PERFORMANCE_EVIDENCE.md`, not in shared changes. Public
fixtures, commits, and PR descriptions must remain project-agnostic.

## CI-P1 — Completed: batched lexical constant counting

[PR #107](https://github.com/khansen/nesrev/pull/107) replaced the per-constant
search/count loop in [inventory refresh](scripts/refresh_inventory.sh) with
one ripgrep JSON search and Python aggregation for normal text under the default
search policy. The [helper contract](scripts/constant_usage_counts.py) preserves
legacy per-name behavior for binary input, custom ripgrep configuration, and
search failures; those paths are outside the one-search guarantee.

The catalog still counts matching source lines, including comments, not semantic
references or token occurrences. Discovery, case sensitivity, word/physical-line
boundaries, value spelling, domain precedence, distinct name/value rows, CSV
bytes, and subtraction of exactly one definition line remain unchanged.

Three sequential warm-workspace runs on a representative banked local input:

| Check | Median wall seconds, before → after | Observed range, before → after |
|---|---|---|
| CI wrapper | 49.42 → 32.56 | 49.06–50.67 → 32.52–33.02 |
| Standalone inventory, including fresh xref assembly | 23.56 → 5.84 | 23.38–23.60 → 5.69–6.08 |
| Isolated lexical counter | 17.18 → 0.21 | 17.17–17.18 → 0.20–0.21 |

These are separate experiments, not additive stage timings. The CI reduction is
about 34%. Inputs and tool build were unchanged; no competing verification ran
during timing and no cold-cache claim is made. Complete diagnostics matched,
including the input's pre-existing maturity-policy failure. Verification
preserved binary identity and process/inventory passed; documentation checks
were not reached. This is not a green full-CI result for that input.

All 22 local constant catalogs remained byte-identical. A smaller complete input
passed full CI before and after. The merged master passed 601 shell tests and
1,206 Java tests, including 12 focused compatibility tests. Differential fixtures
cover duplicate definitions, Unicode and unusual line boundaries, custom search
settings, malformed/unreadable inputs, and complete CSV generation. Independent
bad-direction checks reject catalog/source drift, per-occurrence counting, and
per-name subprocess dispatch. Both usual reviewers approved implementation and
publication before PR creation and merge; GitHub reported no hosted checks.

Before further investment in `usage_sites`, apply the migration plan's
[metric-disposition requirement](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#checks-that-should-remain-text-based):
identify its useful consumer and explicitly choose retention, semantic
replacement, or retirement. Lexical compatibility does not exempt constant
definition/kind/value discovery from structured migration.

## CI-P2 — Planned: one fresh analysis bundle per invocation

Design production and freshness with the general instruction-operand artifact.
The [xasm version 1 producer](https://github.com/khansen/xorcyst/blob/c753b565572a9ea5ea9ebc346381c5b6c7f80710/XASM_INSTRUCTION_RECORDS_SPEC.md)
now provides that artifact and specifies the follow-on bundle boundary. It does
not yet hash the full consumed dependency set or certify freshness, and no
NESrev consumer has switched to it. This producer-only unit makes no CI
speedup claim. Next implement producer-side dependency hashing and validated
bundle production, then migrate the first branch-literal consumer under the
[migration contract](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#migration-contract-for-each-work-item).

Minimal sharing of existing outputs may land independently if the contract stays
useful to migrated consumers; a general caching framework must not block the
instruction artifact. [Pass-prep bundling](scripts/project_pass_prep.sh) is prior
art, not permission to reuse its persistent cache during CI.

Extend the primary verification assembly to emit the structured outputs needed
by later consumers, including listing, indexed patterns, and data-consumer facts.
Keep parity and warning-baseline verification on that assembly. Compare bytes
and warning/error sets with and without analysis options: outputs must remain
observational.

Measure artifact size and consumer loading cost as well as assembly counts.
The optional instruction section must not make every legacy consumer repeatedly
decode facts it does not need; keep sharing scoped to the required outputs.

Required contract:

- `project_ci.sh` owns invocation-local scratch. Publish a completed, versioned
  bundle descriptor only after successful production and input validation.
- Identify producer/tool build and options, project/configuration, address/bank
  domain, dependency closure, and output hashes. Content-hash root source,
  transitive includes, binary inputs, and configuration; existence, size, path
  lists, or timestamps alone cannot establish freshness.
- Embedded-pointer and extent consumers validate supplied bundles. Missing,
  malformed, partial, mismatched, changed-input, or incompatible supplied
  artifacts must refuse, not silently reassemble or use stale pass-prep files.
- Preserve a separate standalone mode: with no supplied bundle, generate the
  required fresh facts once. Absence of an optional bundle is not the same case
  as an invalid supplied bundle.
- Detect inputs changing during production or reuse before certifying success.
  Fail or restart explicitly; never certify evidence from mixed snapshots.
  Keep this invocation-local, not a persistent caching service.

Acceptance: deterministic invocation-count tests prove one assembly in the
normal complete CI flow, versus five on the diagnosed baseline path. Preserve
the additional `xasm --compare` assembly used for source-mapped parity-mismatch
diagnostics unless equivalent output and status are proven; that failure path
is outside the normal one-assembly budget. Standalone behavior, parity, warnings,
diagnostics, and exit statuses must remain equivalent. Independently mutate
same-size root source, transitive includes, binary inputs, and configuration
while preserving timestamps; each must invalidate reuse. Resolve missing
producer facts before removing the old production path.

## CI-P3 — Conditional: reuse measurements, not verdicts

Remove straightforward duplicate collection during producer/consumer wiring
when it needs no substantial infrastructure. Re-profile after migration before
building further result reuse around supported consumers.

Where justified, collect identical expensive findings once and let verification
and maturity apply their separate policies. Extent reuse requires identical
inputs and assertion ledgers; smaller repeated metrics join only when measured
cost and simple contracts warrant it.

- Preserve phase-specific thresholds, whole-body versus strict-prefix coverage,
  and zero-debt maturity requirements. A verification pass is not a maturity pass.
- Share counts, detail sets, evidence, diagnostics, and explicit completion/
  coverage state—not a bare `passed` flag.
- Bind results to checker version, validated bundle, effective arguments, and
  relevant authored ledgers/policy inputs. Changed inputs or thresholds cannot
  reuse incompatible results or verdicts.
- Reject failed or partial collection. Preserve phase reporting, failure
  propagation, unreached gates, and aggregate maturity checks; do not reorder
  checks into a faster failure path.

Acceptance: operation-count fixtures prove one identical expensive collection;
independent fixtures prove the same facts can pass verification and fail maturity.
Compare counts, detail membership, coverage, diagnostics, and exit statuses.

## CI-P4 — Deferred: pointer-text indexing

Do not build owner/alias/source-position indexes for current pointer-proof regex
matchers. Their structured replacements and semantic evidence limits belong to
the [migration plan](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#follow-up-embedded-pointer-audit-proof-heuristics).
Faster heuristics do not provide stronger proof.

At most, consider a trivial immutable-preprocessing hoist with immediate measured
benefit, no new parser/index/cache design, and no delay to migration. This is not
a standalone optimization project. Preserve candidate identities, bank/address
distinctions, ordering, confidence, diagnostics, and refusal behavior. Keep
physical source-line identity and full sequential windows, including unrelated
instructions, comments, and blank lines; filtered match positions are not valid
substitutes. Do not conflate successful-proof deduplication with a general
visited-candidate rule or discard candidates by owner-only memoization.

Any such exception requires exact old/new corpus and adversarial-fixture output
equivalence. Test the last included and first excluded line of every window in
both `struct_copy_deref_proof()` and `pointer_store_proof()`; for a four-line
window starting at `i`, test destinations at `i+3` and `i+4` independently with
other conditions satisfied. Show preprocessing happens once per audit using
operation counts. New grammar/dataflow or unexplained confidence/candidate
changes require a separately reviewed semantic migration, not this exception.

## Measurement, verification, and landing

For each authorized implementation unit:

- Freeze source/configuration/ledgers and assembler build. Run verification
  sequentially, without competing reviewer/corpus tests during timings.
- Collect at least three unprofiled wall/user/system runs before and after;
  report median, spread, machine/tool versions, reached phases, and cold/warm
  artifact conditions. Compare identical stopping paths. Do not add overlapping
  parent/child timings or treat profiled wall time as an unprofiled benchmark.
- Cover a known-failing path and a complete passing path, small and larger/banked
  local inputs, standalone wrappers, missing artifacts, and ledger drift.
  Supported synthetic fixtures supply reproducible full-stage coverage without
  publishing commercial inputs.
- Record assembly/process counts and stage durations. Use operation-count and
  synthetic scaling guards, not brittle wall-time thresholds, in normal tests.
- Preserve exact diagnostics and inventory output for performance-only changes.
  Existing failures remain failures, not exemptions. Semantic migrations may
  change outcomes only under the migration plan's explicit review contract.
- Test stale includes/data/configuration, wrong project, incompatible tool/
  schema/options, missing/truncated output, partial production, changed ledgers/
  thresholds, and collector failure independently. Do not let an unrelated
  missing prerequisite mask the refusal being tested.
- Apply [process-change review requirements](agent_playbook/REVIEW_AUDITS.md#process-change-review-sanity-checks),
  including bad-direction proof and representative blast-radius checks. Mutate
  disposable fixtures, not the active corpus. Rerun affected wrappers and
  repository tests after the final relevant edit.

Re-profile after each unit. A twofold reduction is an exploratory target, not a
forecast, gate waiver, or reason to implement deferred parser optimizations.
Defer remaining work when measurements no longer justify its cost.

This plan does not authorize implementation or publication by itself. Requested
units use separate branches from current `origin/master`, with both usual
reviewers' approvals before PR creation and merge. Rebase the local corpus after
each merge and rerun affected checks, preserving and reporting existing failures.

Out of scope: language rewrites, concurrent verification, persistent caches,
weaker or removed checks, changed maturity policy, suppressed warnings, semantic
game changes, or replacing fresh-build executable-audit evidence with cache reads.
