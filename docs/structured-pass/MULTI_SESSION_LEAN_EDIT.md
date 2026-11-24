# Lean edit operands and the editor price

The owner authorized one edit projection and one reprice after the
[first checkpoint](MULTI_SESSION_CHECKPOINT.md). The reprice passes by **51
tokens above the required margin**. Integration can continue under the existing
24-hour bound. This is feasibility evidence, not admission of a runnable session
plan; final delivery must still fit before any client starts.

`navigate view=edit` returns exactly the selected native statements. The page
declares columns for records and expressions and shares repeated preimages in a
page-local table. It retains exact source text, declaration names, statement
IDs and hashes, lexical owner IDs, ordered expression IDs, expression values and
bindings, and each expression's own preimage. Statement and expression hashes
are not interchangeable. No assembly text is parsed for facts. Full analysis
records and the dedicated trivia/comment views remain available.

The fixed operation reference names the view in the edit field-source tables.
Tests collect that complete reference through the real bridge for implementer,
reviewer and restored reviewer. Each page decodes independently, and shortening
a page for the response cap cannot skip selected records.

The comparison retains all 274 edit targets. Independently decoded lean fields
equal the full records plus the existing expression-identity view, including
every preimage. The record-sourced arguments for rename, declaration insertion,
expression replacement, declaration deletion, localization, data regrouping and
comment insertion compare equal. This does not claim every operation is valid
on every target: existing kind, scope, layout and semantic checks still apply.
Authored names and expressions are decisions, not fields recovered by the view.

| Charge | Prior full records | Lean edit operands |
| --- | ---: | ---: |
| Target records | 274 | 274 |
| Target response bytes | 120,269 | 67,489 |
| Total estimated tokens | 240,933 | 232,509 |
| Remaining headroom | 17,467 | 25,891 |
| Required margin | 25,840 | 25,840 |

Startup stays at 80,909 tokens. The 64 KiB handoff cap, two 8 KiB transition and
contract caps, decisive source re-reads, 48K lifecycle reserve, measured
unscripted overhead and full next-response reservation are unchanged. Every
long hexadecimal run in the lean responses and their arguments is charged at
one token per character: 19,648 characters in this measurement. Other new-view
bytes retain the worst measured rate. The response requirement is 231,878 of
264,604 bytes. There is no capacity reduction credited to omitted targets or
more favorable startup inputs.

The lean response is larger than the reviewer's initial estimate because it
also supplies expression preimages. Its conservative price is close to the
floor; this result does not permit unpriced delivery growth. The editor must
confirm each name from its checked envelope or defer it.

Focused checks cover projection equality, exact selection, pagination, oversized
records, restored delivery and the hash charge. Deliberately dropping statement
preimages or expression IDs fails; removing the special hash charge also fails.
The prior full-record price remains the negative capacity control. No native
client invocation or provider call was needed for this change.
