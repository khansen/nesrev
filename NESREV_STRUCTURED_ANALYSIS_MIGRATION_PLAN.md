# NESrev Structured-Analysis Migration Plan

Status: Phase 1 and Phase 2's xasm instruction-record and consumed-input
manifest producers are complete. The validated invocation-local analysis
bundle is next; Phase 2 consumer migrations and Phase 3 remain planned.

## Purpose

Move process checks away from reparsing assembly text when they are trying to
recover facts that xasm already knows, or should expose. Keep source-text checks
when spelling, comments, naming, or physical layout are the facts being tested.

The migration is intended to reduce duplicated parsers, false positives from
formatting changes, and disagreements between NESrev's interpretation of an
operand and xasm's interpretation of the same operand. It must not increase the
number of xasm invocations in normal wrapper flows.

## Classification Rule

A check should consume structured assembler output when it needs one or more of
these facts:

- instruction or directive identity
- operand boundaries or expression structure
- symbol definitions, kinds, values, scopes, or owners
- resolved addresses, offsets, projections, or displacements
- reference, read, write, control-flow, or simple dataflow edges

A check should continue reading source text when it evaluates:

- literal spelling, such as hexadecimal versus decimal notation
- comments or documentation prose
- symbol naming style
- deliberate source representation or line layout
- authored ledgers, allowlists, or other policy inputs

Hybrid checks should use structured output for assembler facts and source text
only for the lexical or authored portion of the rule.

## Performance Work and Migration Priority

CI-P1's bounded lexical-counting fix is merged in
[PR #107](https://github.com/khansen/nesrev/pull/107). Next, prioritize shared
structured artifacts and consumer migrations, then re-profile. Do not treat a
performance backlog as a requirement to optimize every existing text parser
before replacing it.

This plan owns architectural sequencing. The
[CI performance plan](PROJECT_CI_PERFORMANCE_PLAN.md) records performance scope,
acceptance criteria, and measurements; it is not a competing migration roadmap.

- Design shared fresh-artifact production alongside the general instruction
  stream. Minimal sharing of existing outputs may land independently when its
  contract remains useful to migrated consumers; a general caching framework
  must not become a prerequisite for the instruction artifact.
- Remove straightforward duplicate work during wrapper/consumer wiring where
  safe. Defer elaborate result caching around consumers awaiting replacement.
  Further reuse must be justified by post-migration measurements and preserve
  phase-specific policy, coverage, diagnostics, and failure propagation.
- Do not build owner/alias/source-position indexes around the embedded-pointer
  audit's current regex matchers as a standalone performance project. At most,
  allow a trivial immutable-preprocessing hoist with immediate measured benefit
  and exact current-behavior equivalence, no new parser/index/cache design, and
  no delay to migration.
- Re-profile after migrations and optimize the remaining supported paths.
  Exact reproduction of an old parser's output is a compatibility check, not
  sufficient justification for substantial investment in that parser.

This sequencing does not weaken the migration/refusal contracts below or
authorize implementation, publication, or merges without their normal approval.

## Current Boundary

The xasm data-directive xref-v2 work provides per-operand `.DB` and `.DW`
records with directive width, operand and owner-relative indices, lexical
owner, expression, referenced symbols, target symbol/kind/projection/
displacement, addresses, offsets, segment identity, and emitted value.

The `.DW` pointer inventory and all four Phase 1 consumers now use structured
xref data. Their completed implementation anchors are `fa805bd84` (`.DW`),
`3c80da22a` (embedded/split `.DB`), `3cc5b72f6` (`Used by`), and `4d0393e89`
(pass-selection RAM/ZP map).

The opt-in xasm instruction producer is implemented in
[`c753b56`](https://github.com/khansen/xorcyst/commit/c753b565572a9ea5ea9ebc346381c5b6c7f80710).
Its [version 1 contract](https://github.com/khansen/xorcyst/blob/c753b565572a9ea5ea9ebc346381c5b6c7f80710/XASM_INSTRUCTION_RECORDS_SPEC.md)
provides an ordered stream of active emitted instructions, parser-owned source
and operand spans, pre-fold expression trees, lexical owners, and final
opcode/mode/value/byte/address facts. It requires pure-binary JSON xref and
`--xref-instructions=true`; existing xref sections are unchanged.

The separate opt-in [dependency-manifest producer](https://github.com/khansen/xorcyst/blob/3adde81e01a62d03b44d4268521a22513c5744cb/XASM_DEPENDENCY_MANIFEST_SPEC.md)
snapshots and hashes actual consumed files and the running executable, records
original arguments and missing lookup probes, and revalidates before publication.
It currently supports macOS and Linux and requires pure-binary mode with JSON
xref when requested. It is not a validated NESrev bundle: output hashes,
configuration/policy identity, schema/completeness checks, and reuse validation
remain wrapper responsibilities. The instruction stream alone carries no such
dependency certificate.

These are producer prerequisites, not a completed consumer migration or a CI
speedup. No gate has switched to this stream. Origin IDs survive folding within one
assembly, not across edits; structural bases describe written syntax, not
resolved symbol bindings, alias lifetimes, bank visibility, or dataflow proof.

Corpus-specific corrections, pinned inputs, and historical results belong in
the local-only `projects/STRUCTURED_ANALYSIS_MIGRATION_EVIDENCE.md` companion,
which is not published on `master`. Keep game names, project symbols, and
private commit references out of shared plan changes and PR descriptions.

## Phase 1: Consume Data-Directive Xref v2

Completed migrations; the contracts below record their intended behavior.
They required no additional xasm schema beyond data-directive xref v2.

### 1. Embedded `.DB` pointer pairs

- Replace the operand, projection, owner, and target-kind parsing in
  `scripts/embedded_pointer_targets.py` with `data_directive_references`.
- Recognize adjacent low/high projections belonging to the same lexical owner
  and target expression.
- Preserve NESrev's inventory schema, classification mapping, confidence text,
  statement-local adjacency, and project policy.
- Consume the wrapper-provided shared xref; do not add another assembly.
- Prove exact corpus parity before deleting the source parser. Investigate every
  per-project outlier rather than accepting aggregate totals alone.

### 2. Split low/high `.DB` tables

- Migrate `scripts/split_pointer_targets.py` in the same workstream as embedded
  pointer pairs because both previously shared the same source parser.
- Use xref operand records for table ownership, projection, target expression,
  target kind, and entry order.
- Keep NESrev's suffix-based low/high table pairing policy and mismatch
  diagnostics; these are repository conventions, not assembler facts.
- Prove exact corpus parity and retain refusal tests for incomplete symbolic
  bodies, unequal lengths, wrong projections, and mismatched targets. Preserve
  existing behavior that ignores a lone suffix match: a legitimate low-only
  table can receive its shared high byte from a separate consumer.

### 3. `Used by` pointer-table edges

- Keep parsing `; Used by:` annotations from source text.
- Replace `build_source_references()` in `scripts/used_by_xref_check.py` with
  ordinary xref edges plus data-directive owner-to-target edges.
- Use the lexical data owner supplied by xref v2 rather than assigning table
  entries to a preceding routine.
- Preserve the narrow NESrev rule that only a named pointer-table intermediary
  justifies the two-hop consumer-to-target proof.
- In wrapper flows, require the shared fresh xref. Any standalone fallback must
  be explicit and must not affect the normal invocation budget.

### 4. Pass-selection RAM/ZP symbol map

- Replace `parse_lowaddr_ram_equ_symbols()` in
  `scripts/project_next_pass.sh` with the xref symbol table's kind and resolved
  value fields.
- Keep source excerpts only as presentation context after structured evidence
  has selected the relevant lines.
- Audit `project_next_pass.sh` and `project_pass_residue_check.sh` function by
  function for similar mixed paths; do not attempt a wholesale rewrite because
  both scripts also perform legitimate textual residue and readability checks.

## Phase 2: Instruction Producer, Fresh Bundle, and Consumers

The general producer is implemented; do not create a separate xasm feature for
every remaining NESrev regex. Complete its production and freshness contract
with the shared invocation-local analysis bundle before switching consumers,
so migrations do not add assemblies or incompatible artifact-sharing paths.

At minimum, each record should provide:

- source file, line, column, and assembly-local origin identity retained through
  folding and tied to source/use spans
- lexical owner
- CPU address and output offset
- opcode and addressing mode
- original operand spelling and normalized expression
- referenced symbols
- resolved operand value or target where meaningful
- structured base symbol, displacement, and index register where provable
- immediate/non-immediate and literal/symbolic classification

The original spelling is required for consumers whose policy distinguishes a
raw literal from a symbol. Resolved values alone are insufficient. Macro and
debug/non-debug behavior must be deterministic, and conservative omission is
preferred to a guessed base or displacement.

### Next dependency: trustworthy shared production

Use xasm's consumed-input manifest; do not reconstruct dependencies with an
include regex. Its original arguments, working directory, executable digest,
content hashes, and missing lookup probes identify the producer invocation and
its observed inputs, not future filesystem state. Implement the
[CI-P2 bundle contract](PROJECT_CI_PERFORMANCE_PLAN.md#ci-p2--planned-one-fresh-analysis-bundle-per-invocation):
the wrapper adds configuration/policy identity, validates consistent inputs and
successful output hashes, and rejects invalid supplied bundles without fallback.
Validate negative lookup probes as well as file hashes, since a newly present
candidate can change include resolution without changing the old inputs.
Require producer exit success even if an older manifest remains at the supplied
path. Keep the separately tested no-bundle standalone path explicit.

The producer's optional section is larger than legacy xref. Choose output
sharing and loading deliberately so each legacy consumer does not repeatedly
decode an instruction tree it does not use. Measure wrapper invocation counts,
artifact sizes, and parse costs when wiring consumers; no new persistent cache
or text-parser index is needed to complete this dependency.

Migrate the branch-literal consumer first after this boundary is implemented
and tested, then the remaining consumers below. Review active-code, macro,
same-line, and lexical-policy coverage differences explicitly; a changed count
is not automatically equivalent behavior.

### 5. Branch-literal inventory and KPI

- Replace `scripts/branch_literal_sites.sh` and the corresponding KPI parser.
- Cover literal-only operands such as `$+23`, which ordinary symbol-reference
  xref cannot currently represent.
- Preserve source spelling and lexical owner in the generated inventory.

### 6. Raw-address KPI

- Replace `scripts/raw_address_kpi.sh`'s opcode/addressing parser.
- Preserve its exact policy: exclude immediates, count all qualifying raw low
  addresses, and exclude mapper-style absolute-ROM stores where configured.
- Do not substitute the existing raw-address audit blindly: its A100/A120
  findings are narrower than the KPI's counting contract. Either consume the
  general instruction records or extend the audit with the exact categories
  required by the KPI.

### 7. Negative indexed data offsets

- Replace `scripts/negative_data_offset_check.py`'s label and operand parser.
- Consume structured data-label kind, base symbol, negative displacement, index
  register, opcode, owner, and source location.
- Keep the NESrev policy bound (`1..MAX_OFFSET`) in the consumer.

### 8. Suspicious RAM/ZP immediates

- Replace the inline regex in `scripts/project_process_check.sh`.
- Flag immediate-mode operands whose structural symbol is `ZP_*` or `RAM_*`,
  including same-line labels and macro-expanded forms.
- Refuse to infer this from the resolved numeric value alone because an
  intentional immediate constant may share that value.

### 9. Raw immediate followed by a state/request store

- Replace the instruction parsing and `next_executable()` reconstruction in
  `scripts/raw_immediate_constant_check.py` with the ordered instruction stream.
- Use structured literal value, register flow, following executable
  instruction, destination symbol, and equate values.
- Keep NESrev's semantic-name matching and exclusion policy in the consumer.

### Follow-up: Embedded-pointer audit proof heuristics

`scripts/embedded_pointer_audit.py` is a hybrid, not a completed structured
migration. Besides listing/index-pattern inputs, `struct_copy_deref_proof()`
and `pointer_store_proof()` scan instruction text; `routine_block()` and
`build_equ_aliases()` reconstruct scope and aliases from source.

- Prioritize replacing these parsers, not indexing their current text matches.
  The limited preprocessing exception in
  [Performance Work and Migration Priority](#performance-work-and-migration-priority)
  must not become a competing implementation workstream.
- Replace those assembler-fact parsers with instruction records and structured
  symbol/scope information once the required fields exist. Alias dependency
  gaps also depend on Phase 3; do not replace regex with expression-string
  parsing under another name.
- Ordered instructions and paired reads alone do not prove that a later
  indirect read consumes the same pointer. Preserve explicit evidence limits
  for register flow, scratch reuse, clobbers, and cross-routine reachability;
  unsupported relationships remain advisory rather than confirmed proof.
- Retain byte-run discovery as candidate evidence. Add positive and independent
  refusal fixtures for different copy indices, overwritten pointer bytes,
  unrelated scratch dereferences, and alias/scope ambiguity before changing
  confirmation behavior. Explain any resulting confidence or KPI deltas.

## Phase 3: Structured Equate Provenance and Shared Corpus Facts

### 10. Semantic-evidence assembler checks

- Keep crosswalk and Markdown ordering checks textual.
- Move `.EQU` definitions, external uses, and root-plus/minus-derived dependency
  analysis in `scripts/semantic_evidence_check.py` to structured symbol data.
- Extend xasm output with definition expression and referenced-symbol/dependency
  fields if needed; do not parse expression strings downstream as a substitute
  for the missing structure.

### 11. Hardware constant drift and prior-project reuse

- Prefer xref symbol kind/value data over reparsing `.EQU` literals in
  `scripts/check_hardware_constant_drift.py` and
  `scripts/prior_project_reuse_check.py`.
- Avoid assembling every peer project during one process check. Reuse a
  validated shared cache or derive a committed/generated constant catalog from
  normal project artifacts.
- Keep canonical-name tables, project allowlists, analogue selection, and
  semantic-family policy in NESrev.
- Migrate immediate-site evidence only after the Phase 2 instruction artifact
  exists.

## Checks That Should Remain Text-Based

Do not migrate these merely because they open an asm file:

- `base_readability_kpi.sh`: hexadecimal versus decimal spelling is the fact.
- `constant_kpi.sh`: raw literal spelling and reviewed source allowlists are
  central to the rule, unless a future structured record explicitly preserves
  the original operand spelling.
- The current constant catalog's `usage_sites` counts matching source lines,
  including comments, rather than semantic references. Do not silently replace
  it with xref use counts. This lexical definition does not exempt constant
  definition/kind/value discovery from the structured classification rule.
- comment-quality, stale-comment, inferred-prose, documentation, and naming
  checks
- source-format checks for packet boundaries, table-body representation, and
  declaration comments
- authored inventories, allowlists, crosswalks, scorecards, and review ledgers

Structured output may narrow these checks to relevant source locations, but it
must not erase the lexical evidence they are intended to inspect.

Before further investment in the catalog's usage metric, identify its consumer
and useful decision. Decide explicitly whether to retain lexical counts, replace
them with a defined semantic-reference metric, or retire the field. A change
requires a reviewed inventory-schema/policy migration; legacy compatibility
alone does not justify indefinite retention or more optimization work.

## Migration Contract for Each Work Item

Each migration must satisfy all of the following before the source parser is
removed:

- Pin producer and consumer versions and fail clearly on incompatible input.
- Establish whether each entry point runs only after successful assembly or
  must support intake before the source assembles. Preserve a required
  pre-assembly path only as an explicit, separately tested, limited text mode;
  never silently substitute it when structured input is missing, stale, or
  incompatible in a post-assembly flow.
- Use one shared xasm result per wrapper invocation; do not hide extra
  assemblies inside leaf scripts.
- Compare warning and diagnostic sets with and without each structured-output
  option. Analysis artifacts must be observational: preserving extra AST nodes
  for reporting must not suppress or introduce ordinary assembly diagnostics.
- Compare old and new outputs across a pinned NESrev corpus commit.
- Investigate project-level outliers, even when aggregate parity is exact or
  nearly exact.
- Correct baseline defects in the same atomic landing unit as the new
  generator, so no pinned commit fails its own verification gate.
- Add positive, conservative-refusal, malformed-input, and stale-artifact
  fixtures.
- Mutate every refusal condition independently, using one disqualifier per
  fixture case where guards can overlap.
- Prove the test harness reports a guaranteed non-final assertion failure
  before trusting bad-direction results.
- Delete the superseded semantic parser. Do not keep two authoritative paths
  indefinitely under a silent fallback.
- Preserve source parsing only for explicitly documented lexical policy or
  the separately tested pre-assembly mode above; the latter cannot certify
  assembler-derived semantic facts.
- Run repository gates and the affected project/corpus verification after the
  final edit.

## Planned Order

- [x] Land xasm data-directive xref v2.
- [x] Merge the NESrev `.DW` consumer and reconcile its local inventory
      baselines atomically. Keep the corpus branch local-only.
- [x] Migrate embedded and split `.DB` pointer inventories together.
- [x] Migrate the `Used by` pointer-table source graph.
- [x] Replace pass-selection low-address equate parsing with xref symbols.
- [x] Specify and implement the general xasm instruction-operand artifact,
      designing shared fresh-artifact production alongside it.
- [x] Add producer-side content-hashed dependency tracking.
- [ ] Add the validated invocation-local bundle before switching any
      instruction consumer.
- [ ] Migrate branch literals, raw-address KPI, negative offsets, suspicious
      immediates, and raw-immediate/store analysis.
- [ ] Add structured equate dependencies and migrate semantic-evidence checks.
- [ ] Migrate the embedded-pointer audit's proof heuristics after its
      instruction, scope, alias, and required dataflow evidence is available.
- [ ] Re-profile migrated paths; select remaining duplication/performance work
      from measurements rather than optimizing the superseded text parsers.
- [ ] Introduce a shared cross-project constant cache, then migrate hardware
      drift and prior-project reuse where useful.
- [ ] Re-audit mixed scripts and remove any remaining assembler-fact parsers.

## Existing Spec Disposition

The draft on `feat/structured-analysis-migration-spec` contains no implementation
and is superseded by this plan. Its history is retained in
the local cleanup archive; the branch need not remain active or be merged.
Useful requirements are incorporated here, with these corrections:

- mark `.DW` pointer inventory as completed by the xref-v2 work;
- add the embedded and split `.DB` migrations;
- add the `Used by`, pass-selection, raw-address, negative-offset,
  raw-immediate, and semantic-evidence candidates;
- state that branch literals require literal-bearing instruction records, not
  ordinary symbol xref;
- remove base-readability from the assembler-fact migration list because it is
  intentionally a source-spelling check;
- explicitly retain the pre-assembly intake compatibility check; and
- classify the embedded-pointer audit as a remaining hybrid migration, not a
  fully structured reference implementation.
