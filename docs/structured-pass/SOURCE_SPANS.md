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

Use this paragraph in the next task, alongside its existing stop conditions:

> The practicality ceiling is eight logical requests per independent evidence
> question. Continuation pages of an unchanged operation and query count as one
> request: only offset or the returned continuation token may differ. Keep
> generation, selector, filters, span and limit unchanged. A changed selector,
> including record_id, is a new request; use next_offset with the original
> selector to page a segment span. Report logical requests and transport calls
> separately. Retrieve every page needed for the question; an incomplete page
> is not absence evidence. Do not relabel an unchanged question to evade the
> ceiling.

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
RAM summarization and input-cost optimization remain outside this correction.
Publication, CI, merge and fresh preparation precede any separately authorized
live attempt.

## Offline replay result

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
remain unknown. The remaining 62 calls are a cost concern, not a transport
optimization claim.

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
The real preparation's operation reference is 61,688 bytes, still eight pages
at limit 8,192 and below the existing 256 KiB item limit. Transport, catalog and
item limits are unchanged. Two playbook reading ceilings increase by the
guidance addition's measured 16 lines and 125 words, preserving their previous
headroom. This keeps the new contract readable; other reading ceilings and the
eight-request limit are unchanged.

This is offline evidence. The project preparation still uses the previously
merged project base; its pinned guidance remains historical until the required
post-merge rebase and fresh preparation. The new task wording and tooling
guidance must be included and checked in that packet. Neither the new
declaration nor the source-span option has been used by a real model yet.

The retained evidence includes harness corrections: the replay initially used
the records key for search rows, the retained-review fixture omitted its ledger
row, and the capture driver omitted its output directory. Each was corrected
without changing the evidence requirements; the capture setup failed before
any native invocation. The first full-suite run encountered the command
sandbox's refusal to execute the process-equivalence test's `ps` baseline;
the unchanged suite must pass outside that sandbox. All failed logs remain in
the private evidence. Linux and macOS CI remain publication gates.
