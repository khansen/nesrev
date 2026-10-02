# NESrev Structured-Analysis Migration Plan

Status: Phase 1 and Phase 2's xasm instruction-record and consumed-input
manifest producers, separate instruction output, and validated invocation-local
data-analysis bundle are implemented. Branch-literal consumers now use validated
instruction records, as do the raw-address KPI, raw low-address pass selection,
and symbolized raw-RAM owner refresh, all on instruction records version 3. The bounded negative-offset
feasibility check is complete. Its [v4 producer/consumer design](XASM_INSTRUCTION_RECORDS_V4_DESIGN.md)
is technically reviewed but deferred: the current advisory's corpus does not
justify prioritizing a producer extension. The
[raw low-address pass-selection migration](#raw-ram-evidence) corrects pointer
access evidence using xasm v3; tooling and the coordinated ledger cutover are
complete. The [named pointer-table audit](#named-pointer-table-bodies) found
real omissions that existing structured output can expose. Its structured
consumer and coordinated baseline correction are implemented for review;
landing also requires the xasm listing-storage offset fix. The broader
[embedded-pointer feasibility audit](#embedded-pointer-audit) remains separate.
Other Phase 2 consumer migrations and Phase 3 remain planned.

## Purpose

Move process checks away from reparsing assembly text when they are trying to
recover facts that xasm already knows, or should expose. Keep source-text checks
when spelling, comments, naming, or physical layout are the facts being tested.

The migration is intended to reduce duplicated parsers, false positives from
formatting changes, and disagreements between NESrev's interpretation of an
operand and xasm's interpretation of the same operand. It must not increase the
number of xasm invocations in normal wrapper flows.

<a id="classification-rule"></a>
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
- Before prioritizing another producer extension, compare the legacy consumer
  with current structured facts on the project corpus. Distinguish actual
  incorrect findings or evidence from synthetic coverage improvements and
  semantic-policy broadening. Prefer a bounded migration that corrects current
  evidence using an existing producer contract.

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

The separate-output extension in
[`903c02a`](https://github.com/khansen/xorcyst/commit/903c02a2acefc2dfaccb1ed3d3abf4512acdeeb3)
adds `--instruction-records-output=FILE`: the same versioned document, without
requiring legacy xref. Both outputs share one collected context and serializer;
the existing combined opt-in remains compatible. The separate output requires
`--dependency-manifest` in version 1 so its destination participates in the
producer's input, negative-lookup, and output-collision protections. This is
packaging, not a new semantic model or a consumer migration.

The separate opt-in [dependency-manifest producer](https://github.com/khansen/xorcyst/blob/fd9d1100b9b8f88a33d6fa3dee41394924e03aee/XASM_DEPENDENCY_MANIFEST_SPEC.md)
snapshots and hashes actual consumed files and the running executable, records
original arguments and missing lookup probes, and revalidates before publication.
It currently supports macOS and Linux and requires pure-binary mode with JSON
xref when requested. The [NESrev data-analysis bundle](ANALYSIS_BUNDLE_SPEC.md)
adds output hashes, configuration/policy identity, required schema checks, and
reuse validation in `project-ci`. The instruction stream alone carries no such
dependency certificate, and the current data-only profile does not emit it.

Branch-literal and raw-address gates use the instruction stream. Origin IDs survive folding within one
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
- The raw-RAM refresh for fully symbolized bytes reads the pass-prep
  instruction records: the accessed bytes from `memory_access`, the lexical
  owner, and a canonical RAM equate among the operand's additive terms (see
  [instruction records versions 2 and 3](#implemented-dependency-instruction-records-versions-2-and-3)).
  Pass-prep keeps `instructions.json` in the pass cache for it. The same
  script's raw low-address operand scan and source owner index still parse
  source text and are the next functions to migrate onto those records.

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

### Implemented dependency: trustworthy shared data production

Use xasm's consumed-input manifest; do not reconstruct dependencies with an
include regex. Its original arguments, working directory, executable digest,
content hashes, and missing lookup probes identify the producer invocation and
its observed inputs, not future filesystem state. Implement the
[CI-P2 bundle contract](PROJECT_CI_PERFORMANCE_PLAN.md#ci-p2--one-fresh-analysis-bundle-per-invocation):
the wrapper adds configuration/policy identity, validates consistent inputs and
successful output hashes, and rejects invalid supplied bundles without fallback.
Validate negative lookup probes as well as file hashes, since a newly present
candidate can change include resolution without changing the old inputs.
Require producer exit success even if an older manifest remains at the supplied
path. Keep the separately tested no-bundle standalone path explicit. The
[version 1 bundle](ANALYSIS_BUNDLE_SPEC.md) implements this boundary for existing
data consumers; add an instruction-bearing profile with the first instruction
consumer, without making unrelated xref readers load the larger section.

Use the separate instruction document in the instruction-bearing profile;
legacy readers must not repeatedly decode instruction trees they do not use.
Bind both outputs to the same successful producer invocation and validate their
hashes and schemas. Do not partition a combined document in NESrev or introduce
a new derived-artifact cache. Measure wrapper invocation counts, artifact sizes,
and parse costs when wiring consumers.

Migrate the branch-literal consumer first after this boundary is implemented
and tested, then the remaining consumers below. Review active-code, macro,
same-line, and lexical-policy coverage differences explicitly; a changed count
is not automatically equivalent behavior.

### Implemented dependency: instruction records versions 2 and 3

xasm's [instruction records version 2](https://github.com/khansen/xorcyst/blob/f8fe9805ca84186269afd8cb2449e88f3d13b512/XASM_INSTRUCTION_RECORDS_V2_SPEC.md),
landed in xorcyst [`f8fe980`](https://github.com/khansen/xorcyst/commit/f8fe9805ca84186269afd8cb2449e88f3d13b512), adds two fields to every record. `memory_access` gives the data and
pointer bytes an instruction reads or writes, including read-modify-write.
`additive_terms` splits the operand into signed terms, each with its value and
the definition the assembler used for it. The same release replaces xasm's
mnemonic-prefix access classifier. That changes the legacy xref, summary,
index-pattern and data-consumer outputs:

- read-modify-write accesses gain a kind of their own;
- `BIT` and `JMP [addr]` references become reads;
- `CMP` operands, which the old `CP` prefix test missed, become reads, or
  `immediate` for immediates;
- pointer-mode references become reads of the pointer;
- non-projection immediates get their own `immediate` value.

A read-only sweep of all 23 projects against the version 1 assembler found the
same bytes and warnings everywhere, 177,819 records that pass the term-sum
check, and legacy changes limited to that list. Because NESrev's RAM is named
by equates, which never appear in xref references, the read-modify-write,
`JMP [addr]` and pointer-mode changes left project output untouched. What did
change: 1,050 immediates that were `read`; 355 `CMP` operands that were
`other` (233 now reads, 122 now immediates); 16 `BIT` references that were
branches; and 212 new `CMP` index-pattern read sites.

The [version 3 file table](https://github.com/khansen/xorcyst/blob/540b512/XASM_INSTRUCTION_RECORDS_V3_SPEC.md)
retains those facts and replaces repeated span paths with indices into a
document-level `files` array. It supersedes version 2 without a compatibility
mode. This landing unit adopts both the new facts and the compact schema:

- `scripts/instruction_records.py` requires version `"3"` and validates the
  shape of `memory_access` and `additive_terms` and their consistency with the
  addressing mode and operand value, including that the terms add up to
  `operand_value` (allowing xasm's truncation of constant operands). It checks
  consistency only; which mnemonics read or write stays xasm's fact. File-table
  entries must be distinct nonempty paths and every span index must be in range.
  `tests/instruction_records_test.py` refuses each fact independently.
- `scripts/analysis_bundle.py` validates the complete stream at production,
  including each file against consumed inputs and record bytes against the
  binary. Reuse checks artifact hashes and the validating reader fingerprints
  without repeating that work. The index-pattern schema already accepts any
  string as `access_kind`.
- `scripts/project_next_pass.sh`:
  - The symbolized raw-RAM refresh (`instruction_ram_sites`) takes the bytes
    each instruction touches from `memory_access`: the data address and kind,
    and both pointer bytes as reads, with the 6502 page wrap already applied.
    `JMP [addr]` vectors now count as reads of their bytes. Its RAM term is the
    first symbol term in `additive_terms` whose name is a canonical xref RAM
    equate. That canonical set stays: it is policy (global, defined,
    low-address `.equ` names), not a value lookup, and a term binding cannot
    express it, since `.equ` and `=` both bind as constants. The mnemonic and
    addressing-mode tables are gone from the refresh; the source-text raw scan
    below still uses its own until it migrates.
  - Its site kind `readwrite` became `read_modify_write`, xasm's term. Only
    the generated pass cache carries the name, and no other script reads it;
    `raw_ram_review.csv` stores counts and owners, not kinds.
  - Outbound-edge grouping puts `read_modify_write` references in both the
    data-read and data-write groups; `immediate` and `address_compute` stay in
    `other`.
  - The summary sections need no code change, but their contents shift with
    the classifier: labels read only by `BIT` or `JMP [addr]` move from jump
    targets to data labels.
- `scripts/project_pass_prep.sh` copies the validated records and publishes a
  stamp binding their SHA-256 and both reader implementations. Cached next-pass
  skips revalidation only when all match; an absent or stale stamp falls back
  to full schema validation. This does not certify source freshness or replace
  the fresh invocation-local bundles used by verification and CI.
- `scripts/data_extent_missing_scan.py` accepts `read_modify_write`
  index-pattern sites alongside `read`, since both read the table at the
  bounded index. `CMP Table,X` sites now arrive as bounded `read` sites too, so
  the scan can report new advisory findings; review them in the corpus
  comparison.
- `scripts/embedded_pointer_audit.py`: no change; it uses only
  `paired_byte_reads`, which stays read-only.
- `scripts/used_by_xref_check.py`: no change; it takes owners from references
  and data edges whatever their access.
- `scripts/branch_literals.py` resolves span indices through the file table
  before writing portable CSVs, preserving their bytes. `scripts/raw_addresses.py`
  retains its existing fields and policy.

The [migration contract](#migration-contract-for-each-work-item) comparison ran
all 23 projects on the old stack (these scripts' predecessors with xasm
`83a618e`) and the new one (these scripts with xasm `f8fe980`).
`project-verify` gave the same exit status and KPI output everywhere, and
`project-next-pass` the same recommendation and cluster anchors. Every
difference traces to a change above:

- 53 raw-RAM review rows in 14 projects gained one read per indirect `JMP`
  through a canonical RAM vector; each count delta matches the vector bytes in
  the records. Vectors whose bytes have no review row, or an active row that the
  raw text scan counts, are unchanged.
- The pass cache gained the 212 `CMP` index-pattern read sites, and summary
  entries shifted with the classifier.
- The extent scan reports six new advisory tables in four projects, all
  bounded `CMP Table,X` or `CMP Table,Y` sites that the old classifier hid.
  Their `data_extent_assertions.csv` rows belong on the `projects` branch.

After the version 3 file table and validation reuse, five alternating warm
rounds on the largest project measured median wrapper changes against the
pre-migration scripts plus xasm `83a618e`: verification -4.0%, pass preparation
-8.7%, and cached next-pass -9.6%. Every measured invocation completed with
exit 0. Cached next-pass still hashes the complete records before reusing
validation; fresh verification and preparation still produce new evidence.
Local inputs, timing ranges, and raw receipts are recorded in the local-only
performance evidence companion. These measurements cover the three affected
wrappers, not an end-to-end CI speedup claim.

A separate version 2-to-3 assembler comparison on all 23 projects found
identical binaries, diagnostics, index patterns, data consumers, and xref
facts after resolving the file-table indices. Only the build timestamp was
excluded; both runs used the same source and output paths. Thus the file-table
change adds no new semantic differences to the version 2 migration above.

### 5. Branch-literal inventory and KPI

Implemented contract: [BRANCH_LITERAL_POLICY.md](BRANCH_LITERAL_POLICY.md),
with [fixed bundle profiles and owning-wrapper lifecycle](ANALYSIS_BUNDLE_SPEC.md).
Both old parsers are removed. Coverage is active emitted direct-mode
`current_pc +/- integer` uses; immediate/indexed/indirect and symbolic or
nested/unary RHS forms are excluded. CSV v2 retains portable template/use
provenance. Pending calibration precedes final-policy verification; intake
reuses the listing, and prep separates fact production from failed comparison.
Each owning KPI/CSV pair shares one typed collection, with no cross-phase
verdict cache. The [measured migration cost](PROJECT_CI_PERFORMANCE_PLAN.md#branch-literal-consumer-results)
remains explicit; subsequent work migrates consumers, not another text-parser
optimization project.
The acceptance requirements below remain the regression contract, not a second
implementation backlog.

- Replace `scripts/branch_literal_sites.sh` and the corresponding KPI parser.
- Use one typed classifier for both: a direct raw-PC-offset expression such as
  `$+23`, not merely a relative-branch opcode. The old scans also cover valid
  direct-addressing instructions with this syntax. Settle radices, grouping,
  whitespace, unary integers, and immediate/indexed/indirect exclusions in
  explicit synthetic and corpus comparisons; numerical equivalence alone is
  not raw-literal identity.
- Count active emitted uses. Explain inactive text, same-line labels, repeated
  includes, macro/loop expansion, and substituted-argument coverage changes;
  matching totals do not establish equivalent site membership.
- Upgrade the CSV once, retaining producer source/use spans, lexical owner,
  assembly-local origin ID, emitted position/segment, and operand provenance.
  Define portable path presentation, emitted ordering, and the meaning of any
  legacy `line` field. Distinguish template spelling from invocation evidence;
  do not fabricate contiguous expanded source text. Any presentation-only
  source reread must validate against the bundle's consumed-input hashes.
- Wire each owning entry point, including standalone verification, CI,
  pass preparation, inventory refresh/synchronization, maturity summaries, and
  intake/calibration. Share one production across the KPI and CSV consumers;
  do not hide assembly in a leaf or treat persistent pass-prep output as fresh.
- Define intake's assembly, measurement, calibration, and final-policy-binding
  order. Calibration changes hashed policy inputs: an earlier descriptor must
  not silently survive that change. Never calibrate an active-emitted count
  from a lexical fallback without an explicitly reviewed different contract.
- Distinguish a measured threshold failure from unavailable/refused evidence.
  Existing `2>/dev/null || true` collection must not turn invalid supplied
  artifacts into a normal-looking unknown count or a completed inventory.
  Advisory summaries must show refusal; certification and writing paths must
  propagate it. Preserve source-mapped compare-mismatch diagnostics and their
  distinct production-versus-comparison status.

The producer packaging lands independently. The consumer unit owns the new
bundle profile, parser deletion, schema/coverage decisions, atomic inventory
replacement, corpus comparison, and justified local baseline corrections. Both
units require exact-head and public-title/body approvals before PR creation and
merge; neither licenses a project semantic pass or maturity-policy waiver.

### 6. Raw-address KPI

Implemented contract: [policy and recognition corrections](RAW_ADDRESS_KPI_POLICY.md).
The existing instruction producer supplies the required facts; no xasm extension
is needed. One typed classifier replaces the old opcode/addressing parser;
owning wrappers share validated production and propagate refused measurements.
The lexical width/case policy and fixed ROM-store exclusion remain explicit.
Active anonymous-label uses and forced-width stores have reviewed recognition
corrections, not widened ratchets. The [measured cost](PROJECT_CI_PERFORMANCE_PLAN.md#raw-address-consumer-measurements)
remains visible. The requirements below are the regression contract.

- Replace `scripts/raw_address_kpi.sh`'s opcode/addressing parser.
- Preserve its exact policy: exclude immediates, count all qualifying raw low
  address spellings, and retain the fixed absolute-ROM store exclusion.
- Do not substitute the existing raw-address audit blindly: its A100/A120
  findings are narrower than the KPI's counting contract. Either consume the
  general instruction records or extend the audit with the exact categories
  required by the KPI.

<a id="raw-ram-evidence"></a>
### Raw low-address pass-selection scan

`project_next_pass.sh` now shares structured RAM access extraction between raw
and symbolized operands. Its raw operand parser, mnemonic access classifier,
and separate source owner index have been removed. The initial read-only
comparison of all 23 committed project sources produced 177,819 validated v3
instruction records and established the migration priority:

| Candidate | Corpus result | Decision |
| --- | --- | --- |
| Raw low-address pass-selection evidence | All 5,203 operand sites and owners agree, but 76 indirect stores are classified as writes to the pointer byte; 161 reads of pointer high bytes are absent | Migrate next using v3 `memory_access` and `lexical_owner` |
| Suspicious RAM/ZP immediates | No findings in either the legacy gate or the structured candidate scan | Defer; no observed corpus correction |
| Raw immediate followed by a state/request store | All 64 findings and candidate sets agree with the same constant policy; resolved equates add three candidates whose semantic applicability still needs review | Defer; distinguish broader constant coverage from proven corrections |
| Negative indexed data offsets | 105 existing advisory findings; the known synthetic coverage defects do not establish a current corpus payoff for the v4 extension | Defer the producer extension |

The raw access errors affect read/write counts, owner provenance summaries, and
RAM corridor evidence used by pass selection. For `STA [$02],Y`, the instruction
reads pointer bytes `$02` and `$03`; its write destination is indirect. The old
mnemonic-only classifier instead records a write to `$02` and omits `$03`.
The existing symbolized-RAM analysis already used the producer's pointer-byte
facts; sharing extraction removes that disagreement with the raw path.

Implemented contract:

- Consume the existing validated instruction document already supplied to pass
  preparation/next-pass. Closeout and prep refreshes use their supplied fresh
  bundle's instructions and xref, without consulting stale pass-cache copies.
  Supplied bundles are accepted only in raw-RAM refresh-only mode; a full
  next-pass run refuses them with exit 65 before auto-prep or ledger writes.
  Full runs read all structured analysis artifacts from the pass cache.
  No xasm schema change, output, or invocation is needed.
- Keep raw-literal eligibility and the low-address bound explicit. Use the
  preserved expression for literal identity and source spelling only for the
  existing hexadecimal policy; do not reparse operands from text. If xasm
  truncates an out-of-range pointer, retain the written literal as the rename
  candidate while attributing reads to the producer's resolved pointer bytes.
- Take direct data reads/writes/read-modify-writes and both pointer-byte reads
  from `memory_access`, including its resolved wrap behavior. Direct control-flow
  targets without memory accesses are excluded from the RAM candidate queue,
  including direct jumps/calls to RAM-resident code. Indirect jumps still expose
  their pointer-byte reads. Retain source/use provenance
  and use record identity (`origin_id` within the document), not a source line,
  to distinguish instructions that share a span.
- Share access extraction with the existing symbolized-RAM path where practical,
  retaining their separate eligibility policies. Remove the superseded raw
  operand parser, mnemonic access classifier, and its unused source owner-index
  helpers; do not expand this into unrelated source-index migrations.

Queue membership and counts:

- Create raw candidates only for addresses explicitly spelled by eligible raw
  data-access or pointer literals. A pointer high byte alone must not create a
  candidate or a new
  `raw_ram_review.csv` row. Add its read evidence to an address row only if that
  address is already a raw candidate or has a review row. Retain the complete
  pointer pair on the originating site even when the high byte has no row.
- `operand_count` counts distinct instructions explicitly addressing the row's
  byte: the raw literal for an active raw candidate; the resolved direct address
  or pointer base for the existing canonical-equate path. Apply this rule to
  both paths. A high-byte-only touch contributes zero operands. Symbolized
  expressions retain their current resolved-address policy; a base equate plus
  an offset contributes to the resolved address, not the equate's own address.
- `read_count` and `write_count` count per-byte instruction accesses, including
  supporting pointer-high reads. Deduplicate by record and byte; a
  read-modify-write contributes once to each count. Active rows use eligible raw
  records. Existing inactive rows use the symbolized path plus any raw
  pointer-high support; a row with only that support is inactive with
  `operand_count=0`. No new row is added solely by the symbolized path either.
- Keep primary operand sites separate from supporting accesses throughout
  aggregation. Candidate ranking's `operand_count`, cluster operand counts,
  actionable counts, and member site counts use primary instructions only.
  Supporting reads cannot create an actionable cluster member in an owner that
  never spells that raw address. Read/write summaries and distinct access-owner
  counts include supporting owners, so scoping decisions still see shared-byte
  evidence. The owner-count ranking bands and scoped-overlay decision use this
  full access-owner count, so supporting reads may change either result. A
  supporting owner alone is not a new place to rename a literal.
- Preserve authored status, proposed symbol, notes, last-reviewed pass, and row
  order. Refresh generated facts under these rules; do not promote a reviewed
  high-byte row to active merely because a pointer reads it. The raw-address KPI
  keeps its own counting contract. Supporting byte reads are evidence, not
  additional operands or promised new ledger rows.

Paths and owners:

- Emit the configured `ASM_FILE` spelling for the root source and repo-relative
  paths for includes in sites, cluster definitions, and briefs. Keep resolved
  paths internally for identity, validation, and excerpt loading; do not rewrite
  the validated instruction document's file table. Test from two checkout roots
  so machine-specific absolute paths cannot leak into generated prose.
- Use `lexical_owner`, including global data labels. This intentionally replaces
  the legacy owner index's data-label exclusion: an instruction following a
  global data label with no intervening global label belongs to that data label.
  This is lexical provenance, not proof that the label defines a routine. The
  audited corpus has no primary-site owner differences; the policy change still
  needs a fixture and must be recorded in the migration comparison.

Acceptance and landing:

- Test indirect loads/stores, read-modify-write, pointer wrapping, expanded
  instructions sharing spans, and direct control-flow exclusion. Exercise a
  pointer high byte with no row, with an existing inactive row, and with its own
  raw literal elsewhere. Assert operand counts, byte counts, active flags,
  supporting owners, and cluster membership/ranking separately. Update the
  symbolized-owner refresh fixture's high-byte-only expectations to zero
  operands while preserving its read evidence.
- Compare fresh legacy/structured evidence on the same pinned sources for all
  23 projects, including site membership, owners, ledger facts, clusters, and
  recommendations. Retain the source and producer identities with the results;
  a local pass cache that may lag source edits is not a comparison baseline.
  Measure against the existing wrapper performance budget.
- Land the tooling, then integrate it on `projects` at a pass boundary before
  another semantic pass or closeout. Regenerate `raw_ram_review.csv` for all 23
  projects through the canonical wrappers and commit all resulting ledger
  changes together in one dedicated regeneration commit. Review pointer-related
  changes once, verify authored fields are preserved, and account for unchanged
  ledgers too. This is required even without an xasm schema change: pass-prep
  and closeout rewrite these committed counts, while inventory sync checks owner
  names rather than factual count parity and cannot enforce the migration.

The pass-boundary comparison uses 177,819 instructions and 4,829 eligible raw
sites from freshly prepared sources. Primary site membership and owners match
the legacy scan exactly. The migration corrects 76 indirect-store access kinds and retains
158 additional supporting byte reads without introducing high-byte-only queue
rows. Generated facts change in 190 rows across 18 projects; five ledgers remain
identical. Authored review fields, row membership/order, recommended pass types,
cluster ordering, and all 23 committed branch-literal inventories are unchanged.
All 23 project verification wrappers preserve binary identity, with the existing
`ALLOW_UNRESOLVED_LXXXX=1` allowance enabled. All 23 process checks pass with
the refreshed ledgers. This is not a gold-standard maturity claim.

The repository suite passes, including real-producer fixtures and the
single-assembly closeout test with an intentionally stale instruction cache.
Disposable mutations of supplied-bundle mode, pointer access kinds,
primary/supporting roles, access-owner ranking, missing-record refusal, and
expansion identity each fail
the intended regression test. Source/producer pins, detailed comparisons, and
test receipts remain in local evidence; project-specific symbols and commit
identities stay out of this shared plan. The coordinated landing is complete:
all 23 live project ledgers were regenerated through the wrappers at a pass
boundary and matched the reviewed results, preserving authored review state.
The [wrapper measurements](PROJECT_CI_PERFORMANCE_PLAN.md#raw-ram-pass-selection-measurements)
exclude failed closeout paths from budget evidence and distinguish the largest
source file from the largest instruction stream.

### 7. Negative indexed data offsets

Deferred after design review and corpus prioritization. The v4 contract remains
available, but implementation should wait for a concrete additional consumer or
a demonstrated corpus defect needing label-content classification. A future
data-label inventory must be designed against its actual consumers rather than
added solely to amortize this advisory's migration.

The gains are correctness and maintenance: assembler-owned label and expression
facts, consistent recognition of active expanded instructions, and one fewer
assembly-text parser. This advisory check has no demonstrated performance
benefit, so the migration is modest and non-urgent.

Start with a bounded feasibility check. Inspect the existing consumer and the
available xasm facts, using only a small focused fixture if needed, and report
whether the existing schema supports a straightforward migration. Stop before
implementation if substantial producer/schema work or broader infrastructure is
needed; record the gap and reassess the benefit and cost.

Keep execution proportional to this small check: stabilize focused fixtures
before the required final suite, corpus comparison and reviews, and avoid
redundant runs against unchanged inputs. This does not waive mandatory reviews,
final verification or reruns after changes that affect a check.

#### Feasibility result

The [focused synthetic fixture](tests/fixtures/negative_data_offset_feasibility.asm)
was checked with xasm 1.8.0, instruction records v3 and xref v2. Instructions
provide active emitted uses, index registers, lexical owners, source/use spans,
and the subtraction tree. `additive_terms` identifies the actual label or
constant binding; it also distinguishes identically spelled local labels even
where `structural_base` is null.

The missing direct fact is whether each bound label leads data or code:

- Xref symbol `kind` distinguishes labels, local labels and equates; both
  `Table` and `CodeEntry` are `label`. Instruction bindings also call both
  `label`. The default bundle xref omits local symbols.
- `data_directive_references.target_kind` can classify pointer targets, but
  the fixture's literal-only data bodies produce no such records.
- Data-consumer spans choose `Alias` over its same-address `Table` and
  omit local table names. Index-pattern rows cover direct accesses, but omit
  the indexed-indirect uses already accepted by this advisory. Neither is a
  complete replacement for data-label classification.
- A listing/xref join could establish leading emitted content, but needs an
  explicit definition/alias/local-scope contract. The standalone process
  profile has no listing, and the source-only profile has neither listing
  nor xref. That route would expand bundle production and validation.

xasm already keeps a code/data/unknown `definition_kind` internally in
`listing.c` for pending labels and pointer-target classification, but it merges
initialized data, storage, and binary inclusion. The
[v4 design](XASM_INSTRUCTION_RECORDS_V4_DESIGN.md) adds `binding.definition_content`
with the original data/storage datatype, resolves each definition instance
internally, and covers global/local aliases without address or source-span joins. It defines
producer capture before lowering, strict validation, consumer policy, versioning,
standalone invocation, and acceptance cases. Per-use metadata can share producer
classification with a later data-label inventory, but does not enumerate
unreferenced labels. Design review is complete; implementation is deferred.

The fixture also demonstrates compatibility changes that need explicit review:
the current scanner reports inactive code and confuses two `@@row` scopes,
while missing macro expansion, the extra repeated use, and two instructions
on one line. Preserve the literal-subtraction policy separately from expression
evaluation: `Table-(1+1)` and `Table+(-1)` remain distinct policy decisions.

Reproduce the producer evidence without a ROM:

```sh
mkdir -p tmp/negative-offset-feasibility
xasm --pure-binary tests/fixtures/negative_data_offset_feasibility.asm \
  -o tmp/negative-offset-feasibility/output.bin \
  --xref=tmp/negative-offset-feasibility/xref.json \
  --xref-data=true --xref-include-owner=true --xref-instructions=true \
  --data-consumers --data-consumers-format=json \
  --data-consumers-output=tmp/negative-offset-feasibility/consumers.json \
  --analyze-index-patterns --index-patterns-format=json \
  --index-patterns-output=tmp/negative-offset-feasibility/indexes.json
```

The bounded check compared plain assembly, those outputs, and local-symbol
inclusion: bytes and diagnostics agreed, and the 21 instruction records passed
the v3 validator. This is feasibility evidence only; no consumer migration,
corpus equivalence or wrapper-performance result is claimed.

Implementation scope, under the v4 contract:

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

<a id="named-pointer-table-bodies"></a>
### In review: Named pointer-table bodies

The bounded 2026-10-01 audit of `scripts/pointer_table_body_check.py` found
nine omitted raw interleaved pointer tables in the current 23-project corpus.
Manual consumer inspection confirmed their layout. Eight other raw tables in
the affected project contain RAM pointers and should remain excluded; symbolic
tables and procedures are also exclusions. This is a concrete consumer benefit
using existing listing and xref output, with no demonstrated need for xasm v4.
Detailed names, source pins, commands and results belong in the local evidence
companion. The audit did not change production behavior.

The implementation replaces this named-table heuristic with validated
listing/data-xref joins, separate from `embedded_pointer_audit.py`'s dataflow
confirmation. Do not widen
the source parser: a probe shows that interpreting a split low-byte table as
adjacent lo/hi pairs falsely reports ROM pointers when its paired values are
all RAM addresses.

#### Bounded implementation contract

- Keep names as lexical policy. Cover selector forms such as `ImagePtrByIndex`
  and `ImagePointerByIndex`, including variant-qualified forms such as
  `ImagePtrAByIndex` and `ImagePtrBByIndex`. Require an uppercase letter or digit
  immediately after `By`; reject `Byte`, `Bytes`, `Bypass`, `By_x` and a bare
  `By`. Enumerate supported qualifier forms in tests rather than treating every
  name containing `Ptr` and `By` as proof of a pointer table.
- Obtain active definitions, directive kinds, emitted bytes and boundaries from
  validated xref/listing artifacts. Join by definition provenance and output
  position, not CPU address or owner spelling alone. Do not recover missing
  facts from `source_text`. An instruction must terminate a data run; emission
  gaps, origin/segment changes, aliases and repeated definitions need explicit
  handling. Unsupported or ambiguous identity must not silently certify a table.
- Interpret interleaved bytes as adjacent little-endian words. Recognize all
  five existing split-name families before the interleaved case and pair by
  matching prefix and selector. For complete equal-length halves, combine
  corresponding low/high entries. Never decode one half as interleaved words;
  unmatched, unequal or overlapping halves produce unresolved-layout advisories.
  Report and verification modes allow these; maturity rejects them with exit 68.
  Single-label split arrays
  likewise require layout evidence; names alone do not prove interleaving.
- Retain the ROM-address range and whole-body/prefix thresholds. RAM-only pairs
  do not become findings. Preserve the intended `.DW` and symbolic low/high
  projection exclusions using structured directive/reference fields. Specify
  constant-only operands and mixed raw/symbolic bodies explicitly; the audit's
  conservative exclusion of any symbol-bearing data is not a production rule.
- Both owning wrappers already produce listing and data xref. Reuse their one
  fresh validated bundle; reject missing, incompatible or stale evidence with
  exit 65 and no source-parser fallback. Define standalone fresh production and
  validate its arguments before assembly. Rewrite source-only tests that use
  undefined symbols into assembling fixtures; distinguish usage errors (64),
  evidence failures (65) and policy findings (68).
- Preserve the gate distinction: `project-verify` rejects whole-body-ratio
  findings; `project-maturity-check` also rejects prefix-only findings. All nine
  observed omissions meet the whole-body threshold. Correct and verify the
  affected project baseline in the coordinated landing unit, without weakening
  the gate or silently introducing a selector-name exemption. Target naming,
  bank mapping and parity need separate review before those source edits.

#### Implementation and landing

The consumer contract is now specified in
[POINTER_TABLE_BODY_SPEC.md](POINTER_TABLE_BODY_SPEC.md). It adds the
source-only `data-listing-v1` bundle profile for standalone execution; owning
wrappers reuse their existing bundle. Tests exercise active/same-line data,
code and segment boundaries, aliases, exact table-end markers, includes, repeated emissions, selector
boundaries, split pairs, constant-only operands and symbolic tails. Macro-local
and redefined identities with insufficient join evidence refuse with exit 65.
The single-label split-RAM ambiguity case also produces an unresolved-layout
advisory instead of claiming a ROM table. Aliases share one finding per body.
These checks remain a named-byte heuristic; conversion
still requires manual layout and target proof.

The migration exposed existing producer offset bugs: `list_storage()` does not
count code-segment reservations, while `print_listing_line()` counts initialized
data-segment bytes that pure-binary output never emits. Correct both counters
in xasm. Do not work around them by reparsing source or reconstructing offsets
in NESrev. The 28 producer subcases cover byte/word/dword storage and its empty
records, data-segment `.DB` and `.INCBIN`, JSON/NDJSON, debug/non-debug modes,
segment changes, continuations and later instructions. This corrects listing
v1 and does not require instruction records v4. Per-row segment/emission
metadata remains a separate versioned-schema follow-up; initialized data-segment
rows can still be refused by the consumer's binary validation, as the
[consumer contract](POINTER_TABLE_BODY_SPEC.md) specifies.

Validation on installed XORcyst 1.8.1 passes 658 shell and 1,206 Java tests,
including 22 consumer tests. Nine deliberate regressions fail their targeted
tests. Sequential warm before/after measurements on two large inputs keep
median verification overhead at 3.73% and 3.62%; maturity overhead is 3.69%
and 4.11%, within the 5% budget. Exit statuses match; diagnostics differ only
by the new zero-valued unresolved-layout counter.
The maturity measurements cover the same complete, already-failing check
sequence on both sides; they do not establish a passing maturity result.
Detailed wall/user/system samples and corpus pins stay in the local companion.

Land in this order:

1. The xasm fix is merged and published in
   [XORcyst 1.8.1](https://github.com/khansen/xorcyst/releases/tag/v1.8.1).
   `XORCYST_REVISION` in `.github/workflows/ci.yml` pins its release commit
   `383bdbcf793282ad13b183c76f73e6a937911728`. Install the corrected producer
   before the consumer rollout. Before installation, run the implementation
   suite with its build directory prepended to PATH and XASM_BIN selecting
   that same executable. Older v1.8.0 builds lack the fixes and fail the
   storage regression.
2. Review the consumer and the affected project's symbolic target/bank mapping
   independently. Run the full suite, deliberate regression checks, fresh
   cross-project verification/inventory comparisons and affected-wrapper timing
   under the existing performance budget. Keep commands, hashes and detailed
   corpus results in the local evidence companion.
3. At the project pass boundary, land the shared tooling and reconcile the
   affected baseline on current sources. Regenerate committed inventories,
   including branch-literal provenance after source-line movement, and verify
   parity, process and docs. Do not apply a stale inventory patch or weaken the
   newly effective gate. Old bundle fingerprints must refuse and be refreshed.

Instruction records v4 remain deferred. The broader embedded-pointer dataflow
audit below remains separate from this implementation.

<a id="embedded-pointer-audit"></a>
### Follow-up: Embedded-pointer audit proof heuristics

`scripts/embedded_pointer_audit.py` is a hybrid, not a completed structured
migration. Besides listing/index-pattern inputs, `struct_copy_deref_proof()`
and `pointer_store_proof()` scan instruction text; `routine_block()` and
`build_equ_aliases()` reconstruct scope and aliases from source.

#### Next step: bounded feasibility and corpus audit

Establish whether this migration would correct actual evidence before committing
to implementation or another xasm extension. The baseline observed on
2026-10-01 is **zero confirmed findings across 23 projects**, read from the
retained final raw-RAM rollout `project-verify` logs. Those runs used
`ALLOW_UNRESOLVED_LXXXX=1`; the embedded-pointer check remained enabled. This
is an existing-consumer result, not a fresh embedded-pointer audit or proof that
its confirmation heuristics are sound. Confirmed findings fail verification,
so the audit must examine false confirmations as well as missed findings.

1. Pin all 23 projects' sources, configuration, producer and consumer identities.
   Reproduce the legacy baseline through canonical wrappers and obtain fresh,
   validated v3 instruction records and the existing listing/index-pattern
   inputs from the same sources. Do not compare against a stale pass cache.
2. Compare individual byte-run candidates and proof decisions with the available
   structured evidence, including candidates the legacy checker leaves
   unconfirmed. Record supported, contradicted and unresolved relationships;
   aggregate finding-count agreement alone is insufficient. Inspect differences
   manually and distinguish actual corpus defects from synthetic coverage or
   proposed changes in confirmation policy.
3. Use small positive fixtures and independent refusal cases for different copy
   indices, overwritten pointer bytes, unrelated dereferences, register clobbers,
   alias/scope ambiguity, and unproven control-flow or cross-routine reachability.
   A matching name or later indirect read alone must not establish pointer flow.
4. Map each proof requirement to an existing structured field or a concrete
   missing fact. Keep any comparison prototype local and limited to current
   outputs; do not extend source parsers, implement a general dataflow engine,
   change production confirmation behavior, or build a producer extension as
   part of this audit.
5. Record the baseline, per-candidate differences, fixture outcomes, missing
   facts and recommendation in the local corpus evidence companion. Finish with
   a decision: propose a bounded migration using existing output when the
   evidence justifies it, or defer and state what demonstrated consumer benefit
   would justify the missing producer work. Synthetic improvements and Rule One
   cleanup may be useful, but must not be presented as measured corpus gains.

The audit ends with that decision and a concrete scope, not a production
implementation. Keep instruction-record v4 deferred unless this or another
consumer establishes a need for its specific label-content facts.

#### Migration requirements, if justified

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
- `data_label_doc_kpi.sh` reads `Format:` and `Used by:` headers as text, but
  it finds data labels and their contiguous families with label and
  data-directive regexes. That identity is an assembler fact and belongs to
  structured output; only the header reading is lexical.
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
- Treat instruction-record schema changes as coordinated breaking upgrades.
  Update affected NESrev consumers together; reject and regenerate old artifacts
  instead of maintaining backward-compatible readers or format adapters.
  This requires every consumer to reject old artifacts through strict version
  checks or enforced producer/reader fingerprint validation; unversioned outputs
  such as `index_patterns` and `data_consumers` need versioning or exclusive
  access through validated fingerprinted bundles before using this approach.
  Regenerate and commit derived inventories for every affected project in the
  same upgrade when embedded record fields change; unchanged formats require
  byte-identical regeneration as a regression check.
- Establish whether each entry point runs only after successful assembly or
  must support intake before the source assembles. Preserve a required
  pre-assembly path only as an explicit, separately tested, limited text mode;
  never silently substitute it when structured input is missing, stale, or
  incompatible in a post-assembly flow.
- Use one shared xasm result per wrapper invocation; do not hide extra
  assemblies inside leaf scripts.
- Meet the [non-regression requirement](PROJECT_CI_PERFORMANCE_PLAN.md#non-regression-requirement):
  no affected wrapper may become noticeably slower on the largest project.
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
- [x] Add the validated invocation-local data bundle before switching any
      instruction consumer.
- [x] Add independently requestable instruction output using the existing
      producer context and serializer, keeping legacy xref narrow.
- [x] Migrate branch literals with one typed classifier, CSV v2 provenance,
      validated instruction profiles, and explicit refusal in owning wrappers.
- [x] Migrate the raw-address KPI and its owning-wrapper measurement paths.
- [x] Migrate raw low-address pass selection and owner attribution to v3 records.
- [x] Land the tooling and regenerate all project raw-RAM ledgers together at
      a pass boundary, preserving authored review state.
- [x] Audit [named pointer-table omissions](#named-pointer-table-bodies) across
      all 23 projects and separate real ROM candidates from layout exclusions.
- [x] Implement the named-table consumer contract using existing structured
      output and prepare the newly visible baseline correction for review.
- [ ] Land the reviewed listing-storage producer fix, consumer migration and
      current-source baseline reconciliation with recorded validation.
- [ ] Complete the [bounded embedded-pointer feasibility audit](#embedded-pointer-audit)
      separately before deciding whether its dataflow migration is justified.
- [x] Run the bounded negative-offset feasibility check and identify its
      missing bound-label data/code classification.
- [x] Close review of the revised [producer/consumer contract](XASM_INSTRUCTION_RECORDS_V4_DESIGN.md)
      before the negative-offset migration.
- [ ] Deferred: implement xasm instruction records v4 and adopt its strict reader
      when a concrete consumer payoff justifies the label-content extension.
- [ ] Migrate negative offsets, suspicious immediates, and
      raw-immediate/store analysis.
- [ ] Add structured equate dependencies and migrate semantic-evidence checks.
- [ ] Migrate the embedded-pointer audit's proof heuristics after its
      instruction, scope, alias, and required dataflow evidence is available.
- [ ] Re-profile migrated paths; select remaining duplication/performance work
      from measurements rather than optimizing the superseded text parsers.
- [ ] Introduce a shared cross-project constant cache, then migrate hardware
      drift and prior-project reuse where useful.
- [x] Adopt xasm instruction records versions 2 and 3 together, including
      production-time validation and byte-bound validation reuse.
- [ ] Take `data_label_doc_kpi.sh`'s data-label and family identity from
      structured output, keeping its header parsing lexical.
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
