# NESrev Structured-Analysis Migration Plan

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

## Current Boundary

The xasm data-directive xref-v2 work provides per-operand `.DB` and `.DW`
records with directive width, operand and owner-relative indices, lexical
owner, expression, referenced symbols, target symbol/kind/projection/
displacement, addresses, offsets, segment identity, and emitted value.

The corresponding NESrev consumer has replaced the `.DW` pointer-target
scanner. The xasm producer, NESrev consumer, and Kung Fu terminal-vector
inventory correction are landed, so the pinned projects baseline is
self-consistent and passes its own generator gate.

The intermediate state after rebasing `projects` onto the v2 consumer but
before replaying the Kung Fu correction is explicitly unsupported: the v2
generator correctly emits 227 Kung Fu rows while the unreplayed CSV still has
229, so `project-verify`, `project-ci`, and pass closeout fail. Treat the rebase
and correction replay as one atomic operator action, run no project gates
between them, and pin corpus evidence only to the post-replay projects commit.

## Phase 1: Consume Data-Directive Xref v2

These migrations require no additional xasm schema.

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
  pointer pairs because both currently share the same source parser.
- Use xref operand records for table ownership, projection, target expression,
  target kind, and entry order.
- Keep NESrev's suffix-based low/high table pairing policy and mismatch
  diagnostics; these are repository conventions, not assembler facts.
- Prove exact corpus parity and retain refusal tests for incomplete symbolic
  bodies, unequal lengths, wrong projections, and mismatched targets. Preserve
  the existing behavior that ignores a lone suffix match: Balloon Fight has a
  legitimate low-only table whose high byte is supplied elsewhere.

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

## Phase 2: Add a General Instruction-Operand Artifact to xasm

Do not create a separate xasm feature for every remaining NESrev regex. Add one
versioned instruction stream or instruction-operand record that can support the
whole group.

At minimum, each record should provide:

- source file, line, column, and durable origin identity
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

Migrate these consumers after that artifact exists:

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
- comment-quality, stale-comment, inferred-prose, documentation, and naming
  checks
- source-format checks for packet boundaries, table-body representation, and
  declaration comments
- authored inventories, allowlists, crosswalks, scorecards, and review ledgers

Structured output may narrow these checks to relevant source locations, but it
must not erase the lexical evidence they are intended to inspect.

## Migration Contract for Each Work Item

Each migration must satisfy all of the following before the source parser is
removed:

- Pin producer and consumer versions and fail clearly on incompatible input.
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
- Preserve source parsing only for explicitly documented lexical policy.
- Run repository gates and the affected project/corpus verification after the
  final edit.

## Planned Order

- [x] Land xasm data-directive xref v2.
- [x] Merge the NESrev `.DW` consumer, then update local `projects` and replay
      the Kung Fu correction without running gates in the unsupported
      intermediate state. The `projects` branch is local-only and must never be
      pushed.
- [x] Migrate embedded and split `.DB` pointer inventories together.
- [ ] Migrate the `Used by` pointer-table source graph.
- [ ] Replace pass-selection low-address equate parsing with xref symbols.
- [ ] Specify and implement the general xasm instruction-operand artifact.
- [ ] Migrate branch literals, raw-address KPI, negative offsets, suspicious
      immediates, and raw-immediate/store analysis.
- [ ] Add structured equate dependencies and migrate semantic-evidence checks.
- [ ] Introduce a shared cross-project constant cache, then migrate hardware
      drift and prior-project reuse where useful.
- [ ] Re-audit mixed scripts and remove any remaining assembler-fact parsers.

## Existing Spec Disposition

The earlier `feat/structured-analysis-migration-spec` remains useful as prior
analysis but is superseded by this plan where the two differ:

- mark `.DW` pointer inventory as completed by the xref-v2 work;
- add the embedded and split `.DB` migrations;
- add the `Used by`, pass-selection, raw-address, negative-offset,
  raw-immediate, and semantic-evidence candidates;
- state that branch literals require literal-bearing instruction records, not
  ordinary symbol xref; and
- remove base-readability from the assembler-fact migration list because it is
  intentionally a source-spelling check.

## Phase 1 Corpus Evidence

The embedded/split migration is pinned to local-only `projects` commit
`9a6c1f649`. Using xasm `9a404e1`, all 22 projects were assembled read-only and
the old source consumers were compared byte-for-byte with the new xref-v2
consumers per project:

- embedded `.DB` pairs: 608 rows, exact in 22/22 projects
- split low/high tables: 394 rows, exact in 22/22 projects
- combined: 1,002 rows, zero missing, zero extra, zero reordered

The first outlier was investigated rather than normalized away: Balloon
Fight's `HighScoreEntryBasePtrLoTable` has no high-table counterpart because
its three entries share a high byte supplied outside the table. That evidence
corrected the planned missing-counterpart refusal without weakening the
refusals for malformed paired tables. The `projects` branch remains local-only
and must never be pushed.
