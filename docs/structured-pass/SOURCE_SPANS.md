# Source spans and evidence-request counting

An unscripted corridor attempt stopped before editing because source
navigation ended at every global label. Dense early-stage labels divided a
connected routine into many requests. The bounded correction adds an explicit
`navigate` option and clarifies the accounting; it does not raise the ceiling.

`navigate(view=records, span=segment)` crosses global labels within the selected
segment. It returns at most 40 complete records per page, shortened as necessary
to fit the existing 24 KiB response ceiling. It stops before `ORG`, `END` or a
changed segment identity. Selecting an EQU, ORG or END returns only that record.
The default `span=label` preserves the existing view.

Keep the original selector and follow `next_offset`. The new view's
`next_record_id` names the next undelivered statement; it becomes null at the
span boundary. `scope.boundary_record_id` names the excluded boundary. Neither
lexical adjacency nor a global label proves procedure scope or reachability.
All reads still use a checked generation and the admitted model.

## Counting and task wording

The eight-request ceiling now counts **logical requests**, with transport calls
reported separately. Continuation pages count together only when the operation
and every argument except `offset` or its continuation token remain unchanged.
Changing a selector, filters, generation, span or limit starts another request.
Using the next record as a new selector therefore starts another request; use
the original selector and `next_offset` for continuation.

The same question also has a **400 KiB (409,600-byte) text-response ceiling**.
Every text tool response reports `volume.response_bytes`, including its MCP
envelope, JSON escaping and the counter itself. Count refusals and abandoned
queries too, and reserve the next call's 24 KiB maximum before sending it.
The service reports bytes; it does not maintain a question or session counter.

Search's first page reports `total_rows` and `minimum_response_bytes`. The
latter counts every serialized row but excludes envelopes and delimiters, so
it is a lower bound, not an assurance that the query fits. Navigation reports
`total`; compact RAM reports `total_records`, including the shared set's count.
Check those totals before following a continuation. Start instruction searches
with `detail=matches` and zero context: each match includes its owner. Read only the source context
needed for the question through the bounded span. Do not fetch the rest of a
segment merely because another page exists.

Narrow an oversized query, or stop for a decision when the required evidence
cannot fit. Incomplete evidence is not absence evidence. These ceilings take
precedence over generic paging instructions. Images require separate context
accounting. Earlier questions remain in the conversation: preparation must
deliver a numeric investigation allowance derived from the pinned model window,
measured startup, a lifecycle reserve and at least ten percent estimation margin.
The caller uses the smaller of that remaining allowance and 400 KiB. Extra
guidance, analogue reads, refusals and repeated evidence consume the same total;
neither a new question nor a resumed turn resets it. A missing prepared allowance
requires a decision, rather than an estimate by the model. Editing, necessary
document/preimage reads, review, rework and closeout use the separate lifecycle
reserve. It cannot fund new evidence questions.

The optional match detail returns every matching witness, its certainty and
relative position, plus the instruction's identity, owner, segment, mnemonic,
final addressing mode, operand value, evaluation and operand meaning. Each page
carries columns and constants for decoding its row arrays independently. This
is an explicit projection: source preimages and detailed memory/control-flow
facts remain available through navigation. The full search view stays the
default. Match detail refuses nonzero context; it cannot silently discard a
requested neighbor.

The next task must use `operation_contract.REQUEST_COUNTING` verbatim. The
private draft does so; no spent packet or live authorization is modified.

The generated operation reference and the delivered tooling guidance carry the
same rule. Historical search and RAM reports counted transport pages; those
measurements remain unchanged and must not be presented as logical counts.
The service does not infer question boundaries or enforce a question counter.

## Authorized offline work

The bound is four active hours with a one-hour checkpoint and at most two
credential-free loopback declaration captures. There are no provider calls or
game edits. Acceptance requires neutral dense-label, boundary and generation
tests; a regression control; and the same real-input replay on the old and new
service using the new counting rule for both. The old replay must exceed eight
and the new replay must fit with headroom. A changed declaration needs new pins.
The subsequent capacity review brings the optional RAM access summary into
this correction. The owner authorized selecting relevant canonical sections
for startup, preserving their prose and keeping complete files on demand.
Neither change raises the transport or input-item limits.
Publication, CI, merge and fresh preparation precede any separately authorized
live attempt.

## Initial replay and capacity failure

Both replays use the new counting rule and the same frozen question and source.
They retrieve the vector, the complete contiguous entry-to-return path, the
frame-handshake and input-state operand searches with all context pages, and
one complete RAM view including the shared unknown set.

| Measure | Previous service | Segment span |
| --- | ---: | ---: |
| Logical requests for the question | 16 | 6 |
| Transport calls | 67 | 62 |
| Source-record calls, including vector | 12 | 7 |
| Instruction-search pages | 48 | 48 |
| Local and shared RAM pages | 7 | 7 |
| Largest response, bytes | 22,527 | 22,527 |

The old view needs eleven selections for the connected source path. The span
delivers the same 116 required records through six pages of one selection.
The vector, search rows and expanded RAM rows match. The replay fixes its
evidence requirements before modifying navigation; no semantic findings or
edits are credited. Search identifies operand bases and lexical owners, not
proven exclusive RAM ownership. Indexed possibilities and indirect destinations
remain unknown. The 62 calls delivered 1,259,299 bytes. At the retained live run's estimated
3.3 bytes per token, that is about 382K tokens before startup inputs. The
pinned window was 258,400 tokens. This is a capacity failure; the request-count
result alone was insufficient for acceptance.

## Capacity correction

The first volume plan was rejected. Its flat 3.3-byte token estimate left only
8,066 tokens, omitted the required analogue reads, and underpriced RAM evidence.
The retained live run measured about 2.6 bytes per token for that format. The
revised acceptance bar includes both analogue routines and the unchanged
48,000-token lifecycle reserve, with at least ten percent of the 258,400-token
window left for estimation error.

Three changes reduce the input volume without shortening canonical prose:

- Preparation selects whole canonical anchor sections and captures them in the
  fixed `guidance-startup` record. Each section is byte-equal to its source and
  carries source identity, selected anchors and hashes. All six complete files
  remain available under their original IDs. Both roles receive the same plan;
  the retained review restores the same captures.
- The operation reference uses compact JSON instead of pretty-printed JSON.
  Its fields, descriptions and argument contracts are unchanged. The final
  record is 39,999 bytes across five pages, within the existing item limits.
- `evidence(view=ram_summary)` retains every original access row, native memory
  fact, owner, alias proof, certainty, indexed possibility and unresolved
  indirect destination. It omits only `preimage`, `span`, `cpu_address`,
  `output_offset` and `segment_id`; navigation supplies those when needed.
  This is an explicit projection, not an assertion that the full views are
  byte-identical. The original RAM views remain available.

The summary includes the shared unknowns, so it does not need a second shared
set download. Decode each page by combining constants and columns, then expand
its dictionary fields. Each page carries all dictionary entries it needs.
Dictionary bytes are included before applying the response-size check. All
310 access rows in the replay remain, including every possible alias and
unresolved indirect destination; none is promoted to a proven owner.

## Final capacity measurement

The fresh disposable preparation uses the frozen source and a tooling overlay.
Both roles read the complete compact operation reference, selected guidance,
all declared text references, intake receipt and reference decision through
normal bridge calls. The historical archive remains available on demand.
Startup delivers 214,070 response bytes across 25 calls. The selected guidance
record is 103,825 bytes, including provenance headers; its 102,738 source bytes
are copied verbatim. The assembled prompt carries the exact numeric allowance.

The flow replay reads 120 source records to cover the same 116 required records,
using ordinary 20-record pages and stopping after the return instruction. It
retains the vector, all projected search matches and all RAM access facts. Both
analogue reads use `analogue_index`: one complete 63-record frame-service
routine and one 24-record input routine with its helper. The operator selected
these analogues manually. Their vocabulary still requires local revalidation;
the current-project flow, operand searches and RAM facts supply that evidence.
No semantic decision or game edit is credited by this scripted replay.

| Delivered work | Logical requests | Transport calls | Response bytes |
| --- | ---: | ---: | ---: |
| Current-project question | 5 | 15 | 164,175 |
| First analogue question | 1 | 6 | 68,437 |
| Second analogue question | 2 | 3 | 28,763 |

Token accounting uses the retained live rollout's next-request input growth,
matched to each preceding result. Conservative rates are 2.952 bytes/token for
source records and 3.86 for prose. Previously measured operation-reference
text is priced at 2.97 in the rejected-plan comparison. New compact search,
RAM-summary and operation-reference encodings, structured receipts and request
arguments use 2.58, rounded below the worst observed RAM rate. The seven RAM
pages in the retained run grew context by 41,088 tokens. Initial context,
new prompt growth, declaration allowance and a separate 2,000-token framing
cushion are included in startup.

| Capacity component | Estimated tokens |
| --- | ---: |
| Startup, including prompt and framing | 76,181 |
| Current-project question | 60,175 |
| Both analogue questions | 33,563 |
| Edit, validation and closeout reserve | 48,000 |
| Total | **217,919** |
| Remaining window | **40,481 (15.7%)** |

Preparation budgets 78,000 startup tokens and reserves 25,840 for estimation
error. At 2.58 bytes/token, the remaining investigation allowance delivered in
both assembled prompts is **274,924 response bytes**. The replay uses 261,375.
Before every call, cumulative bytes plus the maximum next 24 KiB response fit;
the largest such reservation is 274,101 bytes. This check applies across the
local question and both analogues. It is audited caller accounting, not an
automatic service counter. The final prompt explicitly separates investigation
from the lifecycle reserve so the byte allowance cannot block an otherwise
budgeted edit, validation or closeout.

The lifecycle reserve is sized from the earlier successful five-turn fixture's
complete three implementer turns: 42,774 request/response bytes, about 16,579
tokens at the worst rate. Adding 16,000 tokens for further reasoning and
authoring still leaves about 15,421 within the reserve. This fixture establishes
transport size, not a forecast of semantic reasoning. The reserve was not
reduced to make the capacity result pass.

The previous full-startup plan, priced with these rates and including the
analogue reads, totals 310,437 tokens and fails the margin bar. The unchanged label view with wide searches
also fails both request and capacity limits. These are retained negative
controls. Fresh preparation after merge must repeat the calculation with its
actual inputs; extra evidence, images or changed startup are not free capacity.
No image allowance or compaction credit is included. This is an estimate with
explicit headroom, not a tokenizer measurement or a guarantee of pass closure.

## Validation and remaining gates

The neutral span fixture crosses eight global labels in at most two calls for
both roles. Tests cover the unchanged default, segment changes with and without
`ORG`, `END`, generation binding, complete comments under size pagination and
restored retained review. The previously captured declaration changes only by
`navigate.span`. Its native pin remains
`6d6918483e5c50c1bec6dd80b4e3dc78379a91d91896fca5fe435aadb9e7e54e`.
The two corridor listings are byte-equal to their earlier native captures;
the retained-review listing is unchanged.
Description/argument lengths remain 4,027/3,822 for the implementer,
3,403/3,113 for the reviewer and 1,211/2,285 for retained review. No additional
native invocation was used for the capacity continuation.

New tests cover verbatim selection, invalid anchors, budget arithmetic,
missing/inflated delivered allowances, both prepared adapter prompts,
restoration and summary decoding across pages. Six deliberate faults are
caught: shortened prose, inflated allowance, missing delivered allowance,
a dropped shared unknown, a wrong dictionary category and a summary size
bypass. Each has a passing unmodified control. Earlier span and volume fault
results are carried forward, rather than described as rerun.

The final local structured suite on macOS arm64 passes 429 tests, with one
opt-in skip. Final `make test` passes the playbook, hygiene and shell checks
and all 1,206 Java tests. Linux and macOS CI remain required before merge.

The replay records preserve failed intermediate projections and harness
corrections, including a too-large analogue page, code imports from an older
preparation, and a comparison decoder that initially omitted the selection
fields when expanding an old shared set. None is credited as passing evidence.
Frozen code imports and final preparation pins are checked before the final
replay. No native clients or provider calls were used by these corrections.

Guidance remains readable. Its addition against master is 49 lines and 437
words; the three affected reading budgets grow by exactly that amount,
preserving prior headroom. Catalog, item, response and invocation limits are
unchanged. The owner checkout and stashes remain untouched, and the isolated
logins were already retired. Review, publication, Linux and macOS CI, merge,
project rebase and fresh packet review still precede a separate live grant.
