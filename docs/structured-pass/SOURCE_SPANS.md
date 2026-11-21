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
budget delivered inputs, evidence and room for editing, validation and closeout
against the pinned model window, and lower the question allowance when needed.

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
RAM summarization remains outside this correction. The capacity correction
reduces search context and repeated field names without trimming the delivered
guidance or increasing the transport limit.
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

Fresh disposable preparation delivers the revised operation reference and
guidance from the proposed tooling. The replay compares the label default,
the previously proposed span with wide search context, and a span with
matches-only searches. All use the same frozen question. The first two remain
negative controls, rather than being credited for their logical counts alone.

| Replay | Logical requests | Calls | Response bytes | Estimated question tokens |
| --- | ---: | ---: | ---: | ---: |
| Label default, wide search | 16 | 67 | 1,252,925 | 388,295 |
| Segment span, wide search | 6 | 62 | 1,265,664 | 391,967 |
| Segment span, match detail | 6 | 19 | 249,224 | 76,901 |

Token estimates include request arguments at the retained run's 3.3 bytes per
token. The response totals include the new byte counters. The 116 required
flow records, vector and all local/shared RAM rows remain equal. Every search
match retains its identity, owner, value and uncertainty. Unneeded neighboring
rows and detailed instruction fields are intentionally not projected; this is
not a claim that the complete wide-search response is byte-identical.

Startup is measured through both roles' real input routes: the full operation
reference, six applicable guidance documents, every declared text reference,
the intake receipt and reference decision. The historical intake archive stays
available on demand, as the assembled prompts already specify. Both roles receive
identical bytes: 429,988 response bytes across 50 pages. The reference is 64,136 bytes
across eight pages, within the unchanged catalog and item limits. Startup is
estimated at 123,433 tokens by adding the delivered growth to the retained
run's observed 80,694-token startup.

Reserve 48,000 tokens for editing, validation and closeout. The earlier full
five-turn fixture delivered 42,774 bytes of lifecycle requests and responses
across its three implementer turns, estimated at 12,962 tokens. The reserve
covers twice that traffic plus 16,000 tokens for additional reasoning and
authoring. A separate 2,000-token framing margin gives a total of **250,334 of
258,400 tokens**, leaving **8,066 tokens beyond the reserve**. Both wide-search
controls exceed the window and the 400 KiB question limit. The effective
question-response allowance is 275,844 bytes after startup, request arguments
and the reserves. Before every call, the replay leaves room for a full 24 KiB
response under that smaller allowance. Its worst next-response reservation
reaches 256,097 tokens, leaving 2,303 beyond the reserves.

This is a narrow estimated margin, not a tokenizer measurement or a guarantee
of semantic completion. No images are included. The historical archive, other
guidance documents and analogue documents remain available on demand; reading them uses the same
remaining context, not a new allowance. Fresh post-merge preparation must repeat
the calculation with its actual delivered inputs. The live task must preserve
the reserved space and narrow or stop when further evidence would consume it.

An intermediate dictionary projection was measured and rejected: its total
estimate was 269,939 tokens with the same reserve. The final columnar encoding
preserves the projection's fields while removing repeated keys. Both failed
capacity results and their raw calls are retained.

Reading the entire historical archive at startup was also measured: its final
total fit, but reserving a maximum next response would consume lifecycle space.
That plan is rejected. The passing plan uses the existing on-demand archive
policy; it does not shorten guidance, text references or the lifecycle reserve.

The neutral fixture crosses eight global labels in at most two transport calls
for both roles. Tests also cover the unchanged default, overlaid segment
boundaries, END, invalid selections and generations, comment-preserving size
pagination, and restored retained review. Four deliberate regressions were
caught: restoring the one-label restriction, crossing boundaries, bypassing the
size limit, and dropping the continuation identity.

Both credential-free native captures received the generated declaration
exactly. Only the optional `navigate.span` key changes the declaration. The
native pin is `6d6918483e5c50c1bec6dd80b4e3dc78379a91d91896fca5fe435aadb9e7e54e`.
Description/argument lengths are 4,027/3,822 for the implementer, 3,403/3,113
for the reviewer, and 1,211/2,285 for the retained reviewer, against 4,096 each.
The initial operation reference was 61,688 bytes, below the 256 KiB item limit.
The volume rule is delivered through that existing paginated record. It changes
no tool declaration or native pin. Guidance reading budgets grow by the measured
prose addition, preserving their previous headroom instead of forcing fragments.
Transport, catalog and item limits are unchanged.

This is offline evidence. The revised preparation uses a disposable tooling
overlay on the frozen project base, so the delivered guidance includes the new
rule. It does not rebase or alter the owner checkout. Post-merge preparation
must bind the actual merged project commit and recheck the context calculation.
Neither the new declaration nor the source-span option has been used by a real
model yet.

The retained evidence includes harness corrections: the replay initially used
the records key for search rows, the retained-review fixture omitted its ledger
row, and the capture driver omitted its output directory. Each was corrected
without changing the evidence requirements; the capture setup failed before
any native invocation. The first full-suite run encountered the command
sandbox's refusal to execute the process-equivalence test's `ps` baseline;
the unchanged suite must pass outside that sandbox. All failed logs remain in
the private evidence. Linux and macOS CI remain publication gates.

The capacity correction's final local structured suite passes 423 tests with
one opt-in skip. Six additional regression controls cover exact byte counting,
first-page size bounds, owner and certainty preservation, a segment-identity
change without `ORG`, and budget delivery through the input lifecycle. Earlier
span controls are carried forward. The interim suite's two failures compared
the new transport counter as semantic data; those tests now compare the same
semantic payload and verify the transport-dependent byte count separately.
