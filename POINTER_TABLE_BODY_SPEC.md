# Named pointer-table body contract

`pointer_table_body_check.py <asm>` checks named raw pointer bodies through
validated listing v1 and data xref v2. It includes the legacy table/list names,
`PtrBy<Index>` / `PointerBy<Index>`, and single uppercase-letter variants such
as `PtrAByIndex`. The character after `By` must be uppercase or a digit.
Split families `PtrLo/PtrHi`, `PointerLo/PointerHi`, `PtrLow/PtrHigh`,
`LoPtr/HiPtr` and `LowPtr/HighPtr`, ending in `Table` or `By<Index>`, are
paired before interpreting bytes; equal
low/high halves contribute one finding at the low declaration. RAM-only pairs
remain excluded. A raw lone half, unequal/overlapping pair, ambiguous definition,
or body interrupted by a label whose scope is unavailable refuses with exit 65.
If an interleaved finding could instead be two equal halves containing only RAM
pointers, the checker refuses that ambiguous single-label layout with exit 65.
These are naming/byte heuristics; conversion still requires target and layout
review, including any other possible single-label split layout.

Consecutive same-address aliases share a body. A `NameEnd` declaration is an
extent marker only if `Name` has a nonempty body ending at that exact binary
offset and CPU address; it does not claim the following payload as a pointer table. An orphan
or displaced `NameEnd` gets the ordinary name/body check. Code, origin/segment directives
and other emission kinds end it. Same-line declarations, includes and repeated
data emissions are supported. Macro-local or redefined identities that cannot
be joined exactly refuse rather than falling back to source parsing. `.DW` and
symbolic low/high projections exclude the body, including merged symbolic tails.
Constant-only operands do not contribute raw words; literal expressions do.

Listing output offsets must include code-segment storage bytes and exclude
non-emitting data-segment bytes. The xasm 1.8.0 storage and initialized-data
offset bugs require a producer fix before rollout. `test_listing_offsets.py`
covers storage widths and their empty records, data-segment `.DB` / `.INCBIN`,
segment switches and subsequent data/instructions in 28 subcases.
Incorrect listing/binary joins refuse with exit 65 rather than reconstructing
offsets in the consumer.

Listing v1 still gives non-emitting data-segment rows byte arrays and numeric
offsets without a per-row segment/emission marker. Such initialized data can
therefore cause this consumer's binary validation to refuse otherwise valid
assembly. The offset fix does not resolve that schema limitation; a separate
versioned emission contract is needed before claiming general support for
joining those rows. Data-segment storage with an empty byte array is supported.

Owning wrappers reuse their fresh bundle without extra assembly. Standalone
execution assembles once using the source-only `data-listing-v1` profile.
Bad arguments exit 64 before assembly; bad/stale evidence and failed production
exit 65 (interrupt statuses 130/143 pass through). Report mode exits 0;
`--strict-whole-body` rejects whole-body-ratio findings with exit 68, while
`--strict` also rejects prefix-only findings. `project-verify` uses the former;
`project-maturity-check` uses the latter. Recipe:
[REVIEW_AUDITS.md#pointer-byte-consolidation-audit](agent_playbook/REVIEW_AUDITS.md#pointer-byte-consolidation-audit).

Implementation: `scripts/pointer_table_body_check.py`. Real-assembler regression
cases live in `tests/pointer_table_body_test.py`. This contract is separate from
the embedded-pointer audit's consumer/dataflow proof.
