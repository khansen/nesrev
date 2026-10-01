# Instruction records v4: bound-label content

Status: technically reviewed; implementation deferred pending a stronger consumer
payoff. The current negative-offset advisory alone does not justify prioritizing
this producer extension. Revisit it with a concrete additional consumer, or a
demonstrated corpus defect requiring label-content facts. Producer and consumer
changes are not implemented. This document defines the xasm extension and NESrev adoption for
[negative indexed data offsets](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#7-negative-indexed-data-offsets).
It extends the [v3 instruction contract](https://github.com/khansen/xorcyst/blob/f149be6/XASM_INSTRUCTION_RECORDS_V3_SPEC.md)
and its v2 binding semantics. Backward compatibility is not required: NESrev
consumers may change with the instruction-record format. Existing fields remain
unchanged in this proposal because this feature does not need to change them,
not because their encoding must be supported indefinitely.

## Decision

Add `definition_content` to each non-null instruction-term `binding`. A label
binding describes the leading active content at the definition that use assembled;
other binding kinds carry null. Record the original data/storage datatype as
well as code/data classification. Publish instruction records version `"4"`, both
standalone and embedded in xref. The outer xref version remains `"2"`.

The information travels with the resolved use. NESrev needs no symbol-name,
address, source-span, listing, or data-consumer join. It can consume the existing
instructions-only bundle, and normal wrappers need no additional xasm call or
artifact. No new command-line option is added.

This classifies leading content, not a symbol's entire extent, reachability,
runtime role, pointer destination, or whether an offset is safe. In particular,
`code` is an instruction at the definition, not a callable-procedure claim.

## Wire contract

The existing `binding.kind`, `binding.definition`, and optional `binding.enum`
are unchanged. Every non-null binding gains the required `definition_content`
member. A label binding has an object with exactly two members:

| Member | Allowed values | Meaning |
| --- | --- | --- |
| `kind` | `code`, `data`, `storage`, `binary`, `unknown` | Leading active content category |
| `datatype` | `byte`, `char`, `word`, `dword`, `user`, or null | Original parser datatype for `data` and `storage`; null for every other kind |

Example binding for `Table: .DB 1,2` (a binding fragment, not a full document):

```json
{
  "kind": "label",
  "definition": {
    "file": 0, "line": 2, "column": 1, "end_line": 2, "end_column": 6
  },
  "definition_content": {"kind": "data", "datatype": "byte"}
}
```

For `Routine: RTS`, the new member is
`{"kind":"code","datatype":null}`. A trailing label without content has
`{"kind":"unknown","datatype":null}`. `unknown` is a valid, classified
outcome, not a substitute for missing metadata.

Bindings with kind `constant`, `procedure`, `variable`, or `enum_member` have
`"definition_content":null`. An equate to a table remains a constant binding;
the new field must not follow its value or expression to manufacture a label
binding. A named declaration without a colon retains its existing variable
binding, even when its declaration initializes data.

An existing null binding stays null, with no child fields. Anonymous forward/
backward terms retain v3's null binding. This extension does not add binding
support to arbitrary expression terms or change which terms have bindings.
Every label binding that the producer does report must have content metadata,
including locals omitted from the public xref symbol list.

No definition ID or additional span is emitted. `binding.definition` remains
source provenance and may be shared by several macro expansions; it is not a
unique key. The producer resolves the definition instance internally before
serializing the content directly on each use.

The authoritative definition is the exact symbol entry reported by
`analysis_bind_symbol()` when the existing binding is recorded. Content and
`binding.definition` must describe that same entry, consistent with the
assembled operand. Tokens do not introduce source-order binding semantics.
For example, after `Tab: .DB 1,2`, a use of `Tab`, `.UNDEF Tab`, and `Tab: RTS`,
ordinary label resolution binds both earlier and later uses to the second
definition. Both bindings then report code, with that second definition's span.
Preserve this existing behavior rather than binding the earlier use to the data.

## Classification rules

Classify the active statement stream in assembler order after selecting
conditional branches and expanding includes, macros, and repetitions. Capture
each content event before datatype conversion or declaration lowering. Maintain
a pending set of ordinary location-label definitions, initially empty.

| Active event | Effect on pending labels |
| --- | --- |
| Location label, including a named local | Add this definition instance to the pending set |
| Anonymous `+` or `-` declaration | Neither add a definition nor clear the set |
| Instruction | Assign `code`, null datatype; clear the set |
| Initialized data declaration | Assign `data` and its original parser datatype; clear the set |
| Storage reservation | Assign `storage` and its original parser datatype; clear the set |
| Binary inclusion | Assign `binary`, null datatype; clear the set |
| `.ORG`, `.CODESEG`, or `.DATASEG` | Assign `unknown`, null datatype; clear the set, even if the numeric address does not change |
| End of the active translation unit | Assign `unknown`, null datatype; clear the set |
| Non-content directive or expansion/scope marker | Leave the set unchanged |

More precisely:

- Consecutive labels are separate definitions receiving the same content fact.
  No one alias is selected as a representative. A label after a content event
  starts a new group, even when that event emits zero bytes.
- Binding scope determines which definition is used. Local/global name changes,
  include boundaries, macro entry/exit, and procedure entry/exit do not themselves
  break content adjacency. Procedure bodies are traversed in active assembly
  order; an empty procedure is not a content event. Only the barriers in the
  table end adjacency. This is deliberately a placement fact, not scope ownership.
- Equates, assignments, symbol attributes, diagnostics, comments, and blank
  lines do not classify or clear pending labels. Definitions in inactive branches
  and unexpanded macro bodies produce no events.
- `.DB`/`.BYTE` normalize to `byte`, `.ASC`/`.CHAR` to `char`, `.DW`/`.WORD`
  to `word`, and `.DD`/`.DWORD` to `dword`. A user-defined initialized type is
  `user`; its generated primitive fields do not reclassify the preceding label.
- Capture the datatype before `process_data()` converts character strings to
  bytes or expands user-defined types. A `.DB` string remains `byte`; a `.CHAR`
  string remains `char`. The field describes the directive's type, not width
  inferred from emitted bytes.
- Likewise capture storage datatype at entry to `process_storage()`, before
  word/dword reservations are normalized to byte counts. `.DSW` is storage/word;
  `.DB[n]` is storage/byte. Keeping this available fact in the existing field
  avoids losing type information; it does not broaden the advisory to storage.
- An initialized empty string is still a data event. A datatype without an
  initializer or with a reservation count is a storage event. An invalid
  reservation, including a rejected zero count, still fails assembly; v4 does
  not relax input validation to produce an analysis record.
- Classify address declarations by the result of `enter_label()` in pass 1:
  if the address folds to an integer and sets `ADDR_FLAG`, snapshot that fact,
  assign `unknown`, and never add that definition to the pending set. This
  applies even if the integer equals the current PC. `X:`, `.LABEL X`, and
  `.LABEL X = $` all produce current-PC addresses and join the set. No new
  parser distinction is needed. Do not inspect `ADDR_FLAG` later: pass 4 also
  sets it on ordinary location labels after assigning their addresses.
- Data-segment declarations can classify as data or storage without ROM output.
  The field makes no promise that the definition has an output offset.

For example, `Before: .DB ""` followed by `After: RTS` gives `Before` data/byte
and `After` code even though their addresses can match. Two banks at the same
CPU address are equally independent. A source span or numeric address cannot
reconstruct this contract.

## Producer implementation boundary

Inspection baseline: xorcyst 1.8.0, commit `f149be6`. Relevant existing code is
`analysis_bind_symbol()` in `astproc.c`, the `astproc_binding_sink` interface in
`astproc.h`, and `instruction_term`, `record_instruction_term_binding()`, and
`emit_additive_terms()` in `listing.c`.

The existing xref `definition_kind` cannot simply be serialized: it collapses
initialized data, storage, and binary inclusion; character type is already lost
in some lowered nodes. Extending only its final-AST walker would still require
new provenance to recover original datatypes, removed declaration boundaries,
and definition instances. Capture those facts during active processing instead;
retain the legacy classifier's existing output contract. Use this bounded change:

1. When instruction records are requested, allocate an invocation-local registry
   of label definitions. Assign a monotonically increasing internal token at
   each active named label's symbol-table insertion, including local labels.
   Keep the token with that symbol entry for the lifetime of its definition.
   Expansion clones get distinct tokens when entered; cloning a template must
   not copy a live definition token. Never reuse a token after undefinition.
   Anonymous declarations need no token because their output binding stays null.
2. Feed the classification events above from the existing active processing
   visitors into a pending-token vector. Record original data/storage events
   before `process_data()` or `process_storage()` transforms them. Generated
   fields cannot overwrite an already classified token. Named definitions are
   registered in pass 1; label uses, including forward uses, acquire the selected
   entry's token through the existing pass-3 binding callback. Snapshot pass-1
   address classification as described above.
3. Extend `astproc_binding_sink` to carry the resolved label's internal token in
   addition to kind/location/enum. Copy it into the term at the same first-binding
   point used today. Constants and other non-label bindings carry no label token.
   Read the token from the exact entry `analysis_bind_symbol()` selected, at the
   same moment it records kind and definition span. Undefinition/redefinition
   must follow ordinary assembler resolution, including a later label definition
   selected for an earlier use. Once captured, keep that token; do not perform a
   second independent lookup during serialization or impose lexical lifetimes.
4. Finalize pending definitions as unknown at the translation-unit end. Once
   bindings and classification are complete, serialize the immutable registry
   entry for each bound label through the shared instruction serializer.

Store tokens and owned facts, not pointers into a reallocating symbol array or
AST nodes that later lowering frees. No source-span identity map, address map,
public-xref lookup, second parse, or shadow-expression re-evaluation is needed.
The pending vector and registry take space proportional to definitions; each
definition is classified once. Both output forms share the same collection.

Keep this registry opt-in with instruction records. Existing legacy xref
`definition_kind` behavior, data-directive records, data consumers, index
patterns, listings, warnings, use counts, and binary output remain unchanged.
Local visibility flags and debug mode must not alter v4 content facts. Compare
the classifiers on common cases: ordinary uniquely defined labels before code,
primitive data, storage, binary inclusion, and end-of-unit. V4 code maps to legacy
code; data/storage/binary map to legacy data; trailing unknown maps to unknown.
Make this observable with visible, uniquely defined global labels, each referenced
by both an instruction and `.DW Label`, assembled with `--xref-data=true` and
instruction records enabled. Compare the instruction binding's content with
`data_directive_references[].target_kind`; the latter exposes the legacy
classification. Local visibility filtering must not turn a comparison into a
silent skip, and every expected directive-reference row must be present.

Fixed-address definitions are tested separately with v4 unknown regardless of
the legacy classification. Initialized user-type declarations (`STRUC`, `UNION`,
`RECORD`, and `ENUM` instances lowered by `process_data()`) are outside this
primitive-content comparison: their original data/user fact has its own explicit
tests. There is no general "declarations erased by lowering" waiver; any
disagreement inside the comparison's stated domain fails the test.

External and auto-external entries initially have no definition or content
token. A referenced external left unresolved fails pure-binary assembly, so it
cannot produce a successful v4 record. If subsequently defined in the unit,
the actual definition receives a token normally. Never emit unknown as a
fallback for a missing definition/token in a reported named label binding.

An absent token for a reported label binding, an unfinalized registry entry,
allocation failure, or serialization failure is a producer failure, never
`unknown`. New pass-time capture failures set a sticky analysis-failure flag;
they must not call `err()`, increment assembly error counts, or return failure
through an existing hook path that calls `err()`. Once set, disable further v4
capture safely while allowing ordinary assembly diagnostics to complete.

After the passes, before analysis collection/publication, check the flag. For
otherwise valid input, emit one analysis-failure diagnostic, set exit 3, and
follow the existing cleanup path without publishing instruction records or a
success manifest. Genuine assembly errors retain their normal diagnostics and
exit 1; do not add a missing-token diagnostic caused by the invalid input.
Collection/serialization failures follow the existing exit-3 publication rules.
Fault injection must exercise allocation/registration failures in pass 1 as well
as missing-token and serialization failures; successful-analysis diagnostic parity
does not mean suppressing the deliberate failure diagnostic in these cases.
Extend the existing `tests/test_analysis_faults.c` harness for these cases;
keep fault injection out of the production command-line interface.

## NESrev consumer contract

The v4 reader requires the new member on every non-null binding and validates
the table above: label objects have exactly `kind` and `datatype`; `data` and
`storage` require one of the five datatype strings; other content kinds require
null; non-label bindings require null content. Missing fields, unknown enum values,
or contradictory shapes fail validation. A legitimate `unknown` label is valid
input but does not qualify for this advisory.

`negative_data_offset_check.py` reports a record only when all of these hold:

1. The final addressing mode is `zeropage_x`, `zeropage_y`, `absolute_x`,
   `absolute_y`, `preindexed_indirect`, or `postindexed_indirect`.
2. Its preserved expression is exactly binary subtraction with a `symbol` or
   `local_symbol` as the left child and an integer literal as the right child.
   The integer is in `1..MAX_OFFSET` (currently 16). Grouping that the parser
   removes is immaterial; arithmetic and unary operators remain significant.
3. `additive_terms.projection` is `none`. Its two terms correspond to that tree:
   the positive named term and the negative integer term. The named term's
   binding is `label`, with content `data` and datatype `byte` or `word`.

For a matching subtraction tree, inconsistent term kinds, names, signs, or
literal values are malformed evidence (exit 65), not a reason to silently omit
the site. A consistent binding of another kind is an ordinary policy exclusion.

This includes indexed-indirect accesses already covered by the advisory. It
does not require `structural_base`, which is null for some local references.
It does not follow equate aliases, inspect mnemonic spelling, infer runtime
index bounds, or use an evaluated displacement to replace expression structure.

| Example | Decision |
| --- | --- |
| `LDA Table-3,X`, with `Table: .DB ...` | Report |
| `CMP Words-$01,Y`, with `Words: .DW ...` | Report |
| `LDA [Alias-1],Y`, with an adjacent data-label alias | Report |
| `LDA @@row-1,X` | Report only if that resolved local definition leads byte/word data |
| `LDA ConstAlias-1,X`, with `ConstAlias .EQU Table` | Exclude: constant binding |
| Code, storage, binary, character, dword, user-type, or unknown label | Exclude |
| `Table-0`, `Table-17`, `Table+1` | Exclude: policy shape or bound |
| `Table-(1+1)`, `Table+(-1)`, `Table-Count` | Exclude: RHS/root shape |
| Immediate, unindexed, projected, anonymous, or scope/member-expression operand | Exclude |

Count one finding per active emitted instruction, in record order. Do not
deduplicate by source line: macro/repetition uses and same-line instructions
are separate sites. Keep record origin, use/source spans, lexical owner, and
binding definition in the internal finding. Human output identifies the use's
file/line/column and origin ID; show template location when it differs. Use the
provided operand text as provenance, without claiming it is fully expanded text.
Keep internal term names, including generated suffixes such as `@@t#0`, for
machine identity only. Human label spelling comes from the producer's term
source text; if that is a macro parameter or expression, show it as source
provenance with the binding location, not as an invented expanded label name.
Never derive identity by stripping a guessed suffix.
The advisory promises no stable CSV schema and adds no new inventory here.

The old scanner's inactive-code findings and local-scope collisions disappear;
active macro/repetition/same-line findings become complete. Non-content
directives between a label and its data no longer hide the relationship.
Empty/reservation and declaration-form differences follow the rules above and
must be itemized in the migration comparison, not waived by matching totals.

Undefined symbols and invalid instruction syntax now fail fresh assembly and
return 65, rather than being silently skipped by a text scan. In
`tests/shell/cases/negative_data_offset_test.sh`, remove `MissingLabel-1,X` from
the valid non-candidate fixture and add a separate assembly-failure case. Replace
`(PacketBytes-%10,X)` with the valid default-mode `[PacketBytes-%10,X]` form;
test invalid parentheses separately as an input failure. Keep a valid trailing
label case to distinguish classified unknown content from an undefined symbol.

### Invocation and refusal

The Python classifier consumes a supplied, validated instruction bundle.
`project_process_check.sh` already owns a `process-instructions-v1` bundle;
it continues calling `negative_data_offset_check.py` directly with that bundle,
in report mode. This also preserves the literal command token required by
`project_policy_config_check.py` and the universal-advisory shell test. CI
likewise reuses its existing compatible instruction profile. No bundle profile
needs another output or a new name.

Provide `scripts/negative_data_offset_check.sh <asm_file> [--strict]` as the
standalone owner, sharing the branch-literal wrapper's bundle lifecycle. It
reuses a supplied compatible bundle, or explicitly prepares and produces one
fresh `instructions-v1` source bundle before invoking Python. Migrate standalone
callers/tests/docs from the direct Python command in the same change. Direct
Python invocation without a bundle fails with an instruction to use the shell
wrapper; the classifier never assembles implicitly.

Specify its exit handling independently of `branch_literal_analysis.sh`:
validate argument count and the optional exact `--strict` flag before reading
positional parameters under `set -u` and before producing any bundle. Missing
arguments or `--stict` must exit 64 with zero assembler invocations. Check source
availability, then explicitly catch preparation/production failures, preserve
their diagnostics on stderr, and map them to 65 (including producer exits 1
and 3). Preserve cancellation statuses 130 (SIGINT) and 143 (SIGTERM) instead of
mapping them to 65. On cancellation, clean up temporary files and exit without
findings, a clean-result message, or retry. Do not rely on `set -e` for this mapping.

Report mode exits 0 even with findings; `--strict` exits 68 for findings.
Usage errors remain 64. Missing/stale/incompatible supplied evidence, malformed
records, and source/input failures exit 65, including in report mode. Revalidate
the bundle before printing findings or a clean result. A supplied bundle failure
must not trigger fresh assembly or a source-parser fallback.

## Versioning and landing sequence

1. Implement and test the xasm producer contract. Both serializers emit only
   `"version":"4"`; there is no v3 switch. The v3 file table and every existing
   record field retain their encoding. Publish the producer contract with the
   xorcyst change; this design remains the NESrev adoption reference.
2. Adopt the matching xasm revision and strict v4 reader in one NESrev landing
   unit, updating producer/version fixtures and required-version documentation.
   Wire the negative-offset consumer and standalone owner, compare findings,
   and remove its label/operand regex parser in that unit. The reader's version
   error must explain the remedy: "instruction records version 4 required;
   upgrade xasm to a build with v4 record support and regenerate the bundle".
   The new reader accepts only v4. No compatibility reader, format adapter,
   producer v3 switch, or continued operation of old checkouts is required.
3. For pre-landing tests, prepend the v4 build directory to `PATH` in the test
   shell only: `PATH="<v4 build dir>:$PATH"`. Remove an inherited `XASM_BIN`
   override or set it to that same candidate, so explicit and default selection
   agree. This covers bare `xasm` and `command -v xasm`, including the spy in
   `tests/shell/cases/semantic_claims_test.sh` that resolves its real producer
   from PATH. Using only `XASM_BIN` would miss that test. Do not install v4 as
   the global default before the pass boundary. This is test isolation, not
   ongoing support for two installed versions; no test-selection fix,
   `build_mod.sh` change, or general executable-selection audit is required.
4. Perform one coordinated upgrade at a project pass boundary. Finish the active
   pass/review/closeout and prevent another pass from starting during the switch;
   land the NESrev change, rebase/update `projects`, and install the matching xasm
   as the default. Regenerate analysis artifacts and verify the updated stack
   before resuming work. There must be no wrapper invocation between the producer
   and consumer updates. Older checkouts must be updated before further use.
   Regeneration includes committed derived inventories as well as ignored
   `inventory/pass/` caches. For v4, prove every committed
   `branch_literal_sites.csv` stays byte-identical, as detailed below. If a future
   format change alters embedded fields, regenerate and commit the affected
   inventories for every project as part of this same coordinated upgrade,
   before resuming project sync/verification flows.
5. Retain the existing bundle schema and profile names. Producer executable,
   instruction artifact, and reader fingerprints already invalidate older
   bundles and pass-cache validation stamps. Exercise those refusal paths;
   never relabel a v3 artifact or accept an old stamp as v4 validation.

Next-pass cache refresh is a separate mechanism: it checks HEAD and selected
file times, not reader/producer fingerprints. A reader edit without a new commit
can therefore leave a cache that reaches validation and refuses instead of
automatically refreshing. This is correct refusal. Explicitly run pass preparation
with the selected v4 producer to regenerate it; do not weaken stamp validation
or add an implicit fallback to this migration.

Branch-literal, raw-address, and RAM-owner consumers adopt the strict reader
but keep their policies and outputs. An implementation claim requires their
regression checks as well as the migrated advisory's checks.

For branch literals, regenerate `branch_literal_sites.csv` for every project
in the pinned corpus and compare bytes against the committed inventory and a
v3 regeneration from the same source revision. The CSV embeds `origin_id` and
the expression JSON; v4 retains both encodings. Require zero byte differences,
not just equal finding counts or parsed expressions. This proves that committed
outputs stay in sync despite the producer/reader upgrade.

## Acceptance cases

These are implementation acceptance requirements, not results of this design.

| Area | Required proof |
| --- | --- |
| Label identity | Adjacent aliases, local names reused under two owners, forward named uses, same-address banks, empty data beside code, and repeated expansion from one invocation span with different content |
| Binding lifetime | Constant equates to labels and equal-valued RAM equates stay constants; after label undefine/redefine, each use's span/content describe the definition it assembled and agree with operand bytes; procedure/variable/enum bindings stay null-content |
| Content capture | Every data/storage datatype before normalization; character strings; user-type lowering; binary inclusion; empty data; invalid storage rejection; segment/ORG barriers; trailing labels; `X:`, `.LABEL X`, and `.LABEL X = $` equivalence; pass-1 integer-address labels remain unknown after pass 4 |
| Active stream | Inactive branches, macro arguments, REPT/WHILE, includes, adjacent statements, non-content directives, procedure boundaries, and anonymous declarations that neither join nor clear pending labels |
| Policy | Literal radices, 1 and 16 included, 0 and 17 excluded; direct/indirect indexing; local data versus code; all expression exclusions above |
| Serialization | Standalone and embedded records agree; local filters/debug flags do not change facts; common-case agreement with visible `.DW` targets' legacy `target_kind`; v3 and unrelated output fields remain unchanged after removing the v4 extension and normalizing the version |
| Refusal | Missing/null label content, bad datatype/kind combinations, content on a constant, missing producer token, v3 input, stale/corrupt supplied evidence, reader change with unchanged HEAD reaching pass-cache refusal, changed input, undefined/external symbols, invalid syntax, and absent Python bundle |
| Failure injection | Pass-1 allocation/registration failure: sticky flag, exit 3, one analysis diagnostic, no new records/success manifest; serialization failure: exit 3; wrapper maps both to 65; genuine assembly error remains producer exit 1 |
| Invocation/cutover | Missing arguments and misspelled flags: 64 with zero assemblies; fresh producer exits 1/3 become 65; SIGINT/SIGTERM preserve 130/143 with cleanup and no verdict; supplied bundle uses no new assembly; process-check retains the direct Python advisory; test-shell PATH selects v4 for the maturity spy; coordinated upgrade rejects old artifacts and succeeds after regeneration |
| Regression | Existing instruction-reader, branch-literal, raw-address, and bundle tests; old/new bytes and diagnostics; every committed branch-literal CSV is byte-identical after v4 regeneration; full consumer suite after final edits |

Extend the [existing synthetic fixture](tests/fixtures/negative_data_offset_feasibility.asm)
with these cases before corpus work. Assert site membership and per-use bindings,
not just counts. For the unchanged fixture, this policy expects 11 findings:
use lines 12 through 16, 24, 26 twice, 33, and 37 twice. Inactive line 29 and
the code-local use on line 36 are excluded. These are acceptance expectations,
not a claim that a v4 producer has run.

For the shared-span identity case, two separate macro invocations are
insufficient: macro-local definition spans can point to their distinct invocation
lines. The [identity fixture](tests/fixtures/instruction_label_content_identity.asm)
repeats one invocation site, varying a parameter so its local label leads code
in the first expansion and data in the second. V3 already reports the same
definition span for both, distinct term names `@@t#0` and `@@t#1`, and source
spelling `@@t`. V4 must assign code/null to the first and data/byte to the second,
yielding one advisory finding. Assert those facts individually. Also test a
forward use, a data-segment definition, and an external declaration followed
by a definition in the same unit.

Mutation tests must prove malformed metadata and stale evidence
are rejected rather than silently skipping findings. Run producer opt-in versus
plain assembly checks to prove analysis does not change bytes or diagnostics.

Then run the [migration comparison](NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#migration-contract-for-each-work-item)
on the available project corpus, accounting for every added/removed advisory
site. Keep project-specific receipts in the local evidence companion. Measure
the affected wrappers on the largest project using alternating warm rounds:
no extra xasm invocations and no median regression above the existing 5% budget.
Also record producer time and instruction-document size; no speedup is assumed.

The review and follow-up probes cover current v3 binding behavior only:
undefine/redefine resolution, current-PC declaration forms, and the shared-span
identity fixture. They use the installed xasm 1.8.0, not an independently rebuilt
baseline. No v4 implementation, corpus comparison, or wrapper timing result is
claimed here.

## Deliberate scope limit

The registry retains original storage datatypes as an inexpensive fact at
capture time; the negative-offset policy still excludes all storage. It can
later supply data-label documentation checks, but this per-use field does not
enumerate unreferenced definitions, contiguous table families, or their extents.
Migrating `data_label_doc_kpi.sh`
still needs a separately designed definition inventory. Do not add that inventory,
alias graphs, or dataflow to this extension. It closes the negative-offset
consumer's missing fact with one field and one instruction-schema revision.
