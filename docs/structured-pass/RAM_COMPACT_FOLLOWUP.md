# Compact RAM evidence: bounded follow-up

15 November 2026. The owner authorized this offline follow-up after accepting
the [independent judgment writer](RAM_JUDGMENT_SLICE.md). The hard bound is two
active hours. No provider calls or project passes are authorized.

## Decision and alternatives

Try a denser, lossless representation of the existing native RAM evidence. The
previous service experiment needed eight and nine requests, against eight,
while its simpler prototype reached eight for both. This is a measured transport
gap on the path to one unfamiliar-game pass, not a reason to change the semantic
analysis or finish the validation game.

Keeping the ordinary 14-request view is the fallback. Building a new analysis
engine or shared indexed-range model is larger than the measured gap warrants.
Prefer factoring repeated values out of the transport first; the judgment writer
can land independently. This does not select the later input or launcher slices.

## Contract and acceptance

- Preserve every native record, physical identity, category, unknown, alias proof
  and selector. Expansion must equal the legacy RAM view. Indexed possibilities
  remain address-dependent; only unresolved indirect destinations are shared
  across all requested bytes.
- Encode equal top-level field values once, with variable columns in row arrays.
  Repeat enough metadata on each page to decode it independently. No fact is
  dropped to make a result fit.
- Bind shared-set identifiers to the generation and facts. A set fetched for a
  different generation, changed input or unrelated publication must be refused.
- Preserve the 24 KiB full MCP wire ceiling and eight-request practical limit.
  Count status, all selected pages and the first shared-set fetch. Report later
  reuse separately. Existing endpoints keep their formats and limits.
- Measure both retained questions and bytes outside zero page through the
  service, including published/retained reads. Check exact expansion, no-match,
  full/later pages, alias selection, pointer wrap and physically distinct sites.
- Prove tests detect deliberately omitted evidence and weakened shared-set
  identity checks. Real-code acceptance uses copies of the already admitted
  input; no semantic edit or real-game closeout is needed.

The driving agent records the result and returns at the two-hour bound, on a
new dependency, or on an integrity/safety failure. Failure to meet the request
target leaves compaction parked; it does not raise the limit. Preserve failed
observations. Independent review remains required before integration.

## Results

**Implemented; offline acceptance meets the unchanged limit.** The two measured
questions each require eight requests with a cold shared set. Only the transport
changed: indexed possibilities remain per-byte and every unresolved indirect
destination remains present. Shared identifiers are bound to the public
generation, including retained publication identities.

| Selected byte | Legacy rows | Per-byte / shared rows | Selected / shared pages | Cold requests | With shared set already held |
| --- | ---: | ---: | ---: | ---: | ---: |
| Measured field A | 311 | 193 / 118 | 4 / 3 | 8 | 5 |
| Measured field B | 312 | 194 / 118 | 4 / 3 | 8 | 5 |
| Outside zero page, internal RAM | 125 | 7 / 118 | 1 / 3 | 5 | 2 |
| Outside zero page, cartridge range | 118 | 0 / 118 | 1 / 3 | 5 | 2 |

These counts match in a fresh corridor and an independently restored retained
review. Cold counts include one status call plus every selected/shared page at
`limit=128`. Reuse counts are derived from the measured selected pages plus
status, assuming the identical shared set is already held; no agent cache or
live-use saving is claimed. The largest complete MCP response is 18,410 bytes,
below 24,576. Each expanded result equals every field of the legacy native view,
including category, physical site, unknowns and alias-proof state. The
cartridge-range question still returns all unresolved indirect possibilities;
zero direct rows does not mean no possible access.

The service uses the previously admitted early-stage source and pinned producer.
Its complete preparation is reused with source, ROM, profile and capture hashes
checked. The retained probe reads the earlier disposable judgment publication;
this follow-up makes no semantic edit, new real-game publication or closeout.
Both selected fields and both non-zero-page probes use the same game, so these
numbers do not predict other games' response sizes.

Six focused tests pass. They cover full/later and empty pages, exact decoding,
numeric and declaration selectors, aliases and pointer wrap, physically distinct
sites, JSON type preservation, duplicate rows, the actual MCP envelope, reopened
corridors and independent retained reads across two synthetic publications.
Their lifecycle gates are simulated; the native producer is real. Five in-memory
fault controls are caught by assertions: dropping a selected row, dropping
unknown destinations, accepting foreign sets, omitting constant facts, and
collapsing distinct JSON types. The first focused run exposed a test comparison
that depended on object-key insertion order; correcting the comparison preserved
the failed log and required no product change.

The full structured suite passes: 331 tests, one opt-in skip. `make test` passes
692 shell cases and 1,206 Java checks. Strict playbook checks, repository hygiene,
relative links and project-neutrality checks pass. The work took about 21 minutes,
conservatively including test waits, within the two-hour bound. Private
evidence is in `structured-compact-ram-20261115`, including raw responses saved
before reduction, final input/code hashes and fault-control output. The preceding
experiment remains unchanged in `structured-ram-slice-20261115`.
The main project head, owner files, supplied inputs, review state and four stashes
match their starting hashes and records. No provider calls were made.

This closes the measured RAM transport dependency offline. It does not show
that an unscripted reviewer will choose the view or reconstruct its evidence
correctly. The tool description and [API documentation](README.md#supported-work)
explain both sets and the decoder. Independent review accepted implementation
`73f67813a`; the first live pass must still observe whether both roles fetch the
shared set and reconstruct the evidence correctly. Declared inputs and the
launcher remain dependencies before that separately authorized pass. The
[subsequent artifact correction](INPUT_DELIVERY_SLICE.md#one-time-intake-correction)
withdraws the proposed root-document extension.
This follow-up does not implement or authorize those slices.
