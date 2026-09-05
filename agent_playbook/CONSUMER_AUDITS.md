# Bounded consumer audits

Use `scripts/consumer_audit.py` when project-owned audits need the same byte
arithmetic, assembled-byte contracts or read-domain accounting. This optional
library is not a new project gate or a general 6502 proof engine. Record grammars
and game semantics stay project-local.

## Evidence contract

`assemble(source, cwd=repository_root)` runs the resolved `xasm` executable in
fresh temporary storage, producing binary, JSON xref and JSON listing together.
It never loads ignored pass caches or old standalone outputs. The returned
`Assembly` records binary/xref/listing hashes and the assembler's resolved path
and file hash. This is assembled evidence, not reference-ROM parity: retain the
project's separate reference comparison and canonical verification wrapper.

`Assembly.offset(name)`, `value(name)`, `data(name, size, delta=0)` and
`unique_local(name)` resolve structured symbols and refuse missing, ambiguous or
out-of-image requests. CPU values and output offsets are distinct; use output
offsets for banked-image byte access. Do not infer one global CPU-to-file mapping
for a banked image.

Bind each modelled instruction sequence with `require_bytes(name, expected)`;
include helper bodies and relevant branch/operand bytes, resolving label operands
from the same assembly. An opcode-contract mismatch requires model review.
Checking a table's physical extent alone does not bind its consumer's behavior.

The `Assembly(binary, xref)` constructor supports existing pure inspectors and
synthetic tests, but sets no freshness provenance by default. It cannot establish
that separately supplied outputs came from current source. Executable entry
points should call `assemble()`; a populated hash field alone is not proof of
a fresh invocation.

## Bounded models

- `adc8` and `sbc8` return the byte result and carry/no-borrow flag. They model
  NES binary arithmetic, not decimal mode, overflow or other flags. Pass carry
  explicitly between dependent operations; do not substitute unbounded integer
  arithmetic or discard helper effects.
- `walk_u8(initial, step)` records the current index before calling `step`.
  `step` returns the next byte index, or `None` after the consumer's stop test.
  A repeated index fails instead of silently asserting a finite extent.
  The index must be the model's complete deterministic state. If another
  counter, carry bit, timer or channel affects advancement, this helper alone
  is insufficient: use a project-local model of the complete state.
- `read_footprint(allocation, selected_record, reads)` reports all three domains
  separately. `Span` uses half-open boundaries in one chosen address/offset
  domain. Reports include repeated-read count, exact unique offsets and reads
  outside either span. They do not automatically reject overlaps, infer padding,
  or treat unread bytes as unreachable. The owning audit decides which overlaps
  are legal and binds its expected result with an assertion.

For a post-decrement byte counter, initial zero can mean 256 iterations;
record the stop-test order rather than assuming an empty record. For sentinel
streams, count the tested sentinel and any complete record emitted before its
test, not merely the payload's apparent size.

## Review and reuse

Project scripts can add the repository's `scripts` directory to their Python
import path. Reuse the helpers without copying them into each project. Keep the
audit's command and proof limits in its existing command index or audit document;
do not add another narrative format specification.

Local evidence must identify entry index/selector sets, seeding writers, test
order, helper effects, address domain, and per-channel scheduling/timer
invariants. A union of every channel's possible frames does not establish what
one gated reader can observe. Multi-channel timing stays local unless the same
complete-state contract genuinely recurs; this library does not infer it.

Include positive controls and bad-direction fixtures for the old incorrect
model. The synthetic suite exercises carry, wrap, helper-dependent read counts,
zero-count underflow, overlapping tails, missing evidence and changed helper
opcodes after fresh assembly. Enumeration proves only the stated model; source
contracts plus manual caller proof must connect it to the code.
