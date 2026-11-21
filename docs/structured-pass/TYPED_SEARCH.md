# Typed search

Both roles in a current-project corridor can call `search`. It reads certified
instruction records or already admitted text. It does not edit candidates,
publish evidence, mark review coverage, admit inputs or run a shell.

Every request supplies `generation` and `query`, with optional `limit` (1–40,
default 40) and `continuation`. The response includes `selection_sha256`, the
complete match count, bounded `rows`, and `complete`. Follow every continuation
with the same generation and query. A full page can still have another page.
The limit counts evidence rows, including context and long-line slices; it is
not necessarily the number of matching instructions or lines.

Continuations bind the query, generation and selected input hashes. Changing
`limit` is allowed; changing a predicate, selection or generation is not.
Explicit historical generations remain readable. Published `E-` identities are
accepted only on this corridor's ancestry and remain distinct from their `G-`
identities. Unknown generations and changed pinned inputs fail before evidence
is returned. The existing 24 KiB bridge ceiling is unchanged.

## Instruction queries

```json
{
  "operation": "search",
  "arguments": {
    "generation": "<generation>",
    "query": {
      "kind": "instructions",
      "alternatives": [[{
        "mnemonics": ["LDA", "STA"],
        "operand": "non_immediate",
        "shapes": ["literal"],
        "ranges": [[512, 767]]
      }]],
      "context": {"before": 2, "after": 2}
    }
  }
}
```

`alternatives` is an OR of at most eight sequences. Each sequence contains one
or two instruction predicates. Fields within a predicate are ANDed; members
of each list, and `values` together with `ranges`, are ORed.

| Field | Meaning and limit |
| --- | --- |
| `mnemonics` | Up to 16 official 6502 mnemonics, uppercase. Unsupported mnemonics fail. |
| `modes` | Up to 16 native final-mode names, such as `IMMEDIATE_MODE`, `ZEROPAGE_X_MODE` or `POSTINDEXED_INDIRECT_MODE`. |
| `operand` | `immediate`, `non_immediate` (an operand exists), or `none`. |
| `shapes` | `literal` (native integer expression), `bound` (symbol/local reference), `compound` (other native expression), or `none`. A compound expression can include bound symbols. |
| `values` | Up to 32 signed 64-bit integers; booleans are rejected. |
| `ranges` | Up to four inclusive `[low, high]` integer ranges. |

An optional `owner_id` selects instructions whose native lexical owner is that
declaration. It selects the first instruction of a sequence. It does not claim
that control flow stays inside the owner. `context` requests at most ten native
instructions before and after each witness. The response states how much
context was available at the boundaries.

Sequence and context traversal require consecutive native instruction records,
contiguous output and CPU locations, and the same segment, without crossing a
data statement. Comments and labels may intervene. This is not physical-line
adjacency or proof of a control-flow path. Separate alternatives can identify
the same starting instruction; `witness_id` includes the alternative index.

Each instruction carries its stable record/owner IDs, source span and preimage,
CPU/output/segment location, parsed and final modes, expression shape, evaluated
operand, and native memory/control-flow facts. `operand_meaning` distinguishes
immediate values, direct operands, branch targets, indexed bases and pointer
expressions. Equal bases do not prove equal runtime destinations or aliases.

`unresolved_candidates` preserves numeric uncertainty; those witnesses have
`certainty: unresolved` and do not enter `total_matches`. An instruction without
an operand is not an unresolved numeric candidate. Current certified fixtures
and the admitted corpus have integer instruction operands; an undefined-symbol
fixture is refused by the producer. A defensive unit test covers unknown-as-zero
handling without calling a fabricated model certified.

## Text queries and selection

First query `{"kind":"catalogue"}`, optionally with
`"kinds":["document"]` or `"kinds":["guidance"]`. Exhaust its pages. Entries
contain an `input_id`, canonical relative name, content hash and availability.
The catalogue uses the existing authored-document registry and the eight names
already offered by `guidance`, pinned to the pass-start policy commit. A missing
pinned guidance file is explicitly unavailable. No path supplied by the caller
becomes an input.

```json
{
  "kind": "text",
  "inputs": ["<catalogue input_id>"],
  "terms": ["frame", "palette"],
  "prefixes": ["## "],
  "ignore_case": true,
  "whole_token": false,
  "context": {"before": 1, "after": 2}
}
```

Select 1–32 distinct IDs and at least one literal term or prefix. At most 32
terms/prefixes are allowed in total, each 1–256 Unicode codepoints. Predicates
are ORed. Prefixes start at column zero. There is no regex engine, ordered-term
predicate, wildcard expansion, or automatic admission of reference extracts,
other projects, scorecards, CSV files or review archives.

`ignore_case` uses Unicode case folding. Match columns refer to the original
text: zero-based codepoint offsets with an exclusive end; lines are one-based.
A match cannot select half of an expanding fold. `whole_token` uses Q09's exact
ASCII identifier-boundary alphabet, `[A-Za-z0-9_@]`, rather than linguistic word
splitting. The response gives the selected input IDs and hashes explicitly.

`total_matches` counts matching lines. Rows carry the witness and line identity,
literal text slices of at most 512 codepoints, and match positions identifying
the predicate and its term index in the query. Dense positions use additional
rows, at most eight positions each. `line_complete` marks the final text slice;
continue through all pages to collect every position and context row. Nothing
is silently cut off. Overlapping context can repeat a line under different
witness IDs.

Text context is bounded to ten lines on either side. For larger policy windows,
use the catalogued fixed-ID `input` in corridor sessions; retained readers also
offer `guidance`. The historical acceptance ledger counted catalogue, search,
context and continuation calls separately. The current
[logical-request rule](SOURCE_SPANS.md#counting-and-task-wording) groups unchanged
query continuations while reporting transport calls separately. The ceiling
remains eight logical requests per independent question. An overflow stays a
gap; it does not increase the threshold.

## Limits and interpretation

Unsupported predicates, foreign input IDs, unavailable inputs, stale tokens and
oversized indivisible metadata have distinct public errors (`SEARCH_SCHEMA`,
`SEARCH_INPUT_UNKNOWN`, `SEARCH_INPUT_UNAVAILABLE`,
`SEARCH_CONTINUATION_INVALID`, `SEARCH_ITEM_TOO_LARGE`). Only a complete query
with zero matches and no unresolved candidates establishes absence on the
selected inputs.

The [acceptance record](TYPED_SEARCH_ACCEPTANCE.md) separates synthetic checks,
cross-project proxies on mature code, unadmitted unit-level volume checks and
historical verification. Scripted offline success does not establish that a
reviewer will choose these operations unaided. That remains an unscripted live
acceptance step, after launcher and task capability dependencies are available.
