# Branch-literal inventory and KPI

The branch-literal gate measures parity-sensitive raw current-PC offsets, not
just relative-branch opcodes. Both the KPI and CSV use one predicate over xasm
instruction records v1, supplied through the [validated bundle](ANALYSIS_BUNDLE_SPEC.md).

## Predicate and coverage

One emitted instruction use is one site when all these conditions hold:

- its final addressing mode is `relative`, `absolute`, or `zeropage`;
- it is neither immediate nor indexed;
- its pre-fold expression root is binary `+` or `-`, with `current_pc` on the
  left and an `integer` node on the right.

Thus `BNE $+2`, `JMP ($ + $03)`, and direct `LDA $+%10` qualify. Radix,
whitespace, case, and grouping do not change the decision. Named/equated RHS
values, nested arithmetic and unary-negative RHS nodes are excluded; numerical
equality with a literal is not evidence of raw syntax. Immediate, indexed and
indirect operands are excluded. This predicate does not infer control flow or
assert that a recorded load is a branch.

Coverage is the active emitted stream: macro arguments are substituted in the
tree, every repeated expansion/include use counts separately, same-line labels
and multiple instructions are included, and inactive branches and uninvoked
macros do not count. Data directives are excluded; a valid data-only assembly
is an explicitly complete zero. This intentionally replaces the old physical-
line decimal-only scans; resulting count/registry changes require reviewed
baseline migration, not automatic ratchet widening or relaxed freshness.

## CSV version 2

Rows are in emitted output order, with LF line endings and standard CSV
quoting. The old column names remain, with these explicit meanings:

| Column(s) | Meaning |
|---|---|
| `line`, `enclosing_label` | Parsed template line and lexical owner, or `(none)`; not inferred procedure ownership |
| `mnemonic`, `operand`, `source` | Canonical mnemonic, exact parser operand-template text, and instruction-template text; `source` is no longer the whole physical line |
| `schema_version` | `2` |
| `source_file`, `source_column`, `source_end_line`, `source_end_column` | Rest of the parsed instruction span; `line` supplies its start line |
| `use_file`, `use_line`, `use_column`, `use_end_line`, `use_end_column` | Invocation/use span |
| `origin_id`, `output_offset`, `segment_id`, `cpu_address` | Assembly-local use identity and emitted location; IDs are not stable across source edits |
| `expression` | Compact, lossless JSON pre-fold tree with individual node provenance |

Spans have one-based byte columns and exclusive ends. For macros, template text
must not be presented as expanded spelling: the tree retains substituted
argument spans and text. No source reread is needed to generate the CSV.

All file paths, including those nested inside expression trees, are presented
relative to the invocation repository root for project profiles, or the root
source directory for source-only CLI use. External includes may therefore use
`..`; same-basename inputs remain distinct. This portable display convention
does not alter the original lookup paths used for dependency validation.

## CLI and failure contract

The existing `branch_literal_kpi.sh`, `branch_literal_sites.sh`, and
`branch_literal_sites_check.sh` interfaces remain. With no descriptor the
wrapper assembles fresh source-only facts once; with a supplied descriptor it
never falls back to assembly. Missing, malformed, incomplete, incompatible or
stale evidence refuses, including an explicitly empty descriptor path or a
data-only bundle. A KPI config used for a limit must be bound to the bundle.

Verification collects rows once for the KPI and registry comparison, preserving
threshold-before-registry diagnostics. Inventory likewise collects once for its
count and staged CSV. These paired operations share in-memory facts only within
that call: no cross-phase verdict/result cache or relaxed publication check.
Schema validation checks every typed provenance span during the same traversal,
including nested expressions and nonmatching records.

The KPI retains `strict_active_branch_literals` and threshold exit 68. Refusal
is not a measured threshold failure and emits no count. Inventory refresh
collects branch evidence before publishing any generated ledger, stages all
generated files, then revalidates before replacement. CSV replacement is atomic
per file; there is no claim of a directory-wide transaction. The advisory
maturity summary explicitly displays `REFUSED/UNAVAILABLE` for operational
failure instead of silently treating it as an ordinary unknown count.

Synthetic acceptance covers predicate exclusions, macro/include identities,
portable CSV regeneration, empty streams, malformed nonmatching records,
freshness/late mutation refusal, KPI/CSV equivalence, calibration publication,
and owner-level production counts. Corpus-specific baselines and reproduction
details remain in local evidence, not in shared source.
