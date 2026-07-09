# NESrev Explicit Inline-Record Recovery Specification

## 1. Decision

Implement a small, configuration-driven feature. Do not add automatic
inline-call inference, stack symbolic execution, or game-specific detection.

NESrev currently assumes that execution continues at the byte immediately
after every `JSR`. Some 6502 programs place a record there and have the callee
resume after it. Some records contain code pointers encoded as
`destination-1` for later `RTS` dispatch. Some programs also have data islands
inside otherwise linear code regions.

The feature consists of two explicit inputs:

1. `inlinecalls.csv` describes records immediately following direct `JSR`
   callsites. Rows may apply to every call to a callee or to one exact
   callsite.
2. `dataranges.csv` describes data islands that NESrev must skip while tracing
   and resume after.

This is enough to make regeneration deterministic without building a general
control-flow inference engine.

## 2. Scope

### 2.1 Required

- Parse both optional configuration files.
- Support one default inline-record layout per callee.
- Support exact callsite-specific layouts for helpers whose inline record
  length varies by callsite.
- Keep configured record/range bytes as data even when they decode as valid
  opcodes.
- Resume tracing after each inline record or data range.
- Trace code pointers embedded in inline records.
- Label, but do not trace, data pointers embedded in inline records.
- Support signed pointer adjustments, including `+1` for `RTS` dispatch.
- Emit inline pointer fields as symbolic `.DW` expressions.
- Produce deterministic output independent of traversal order.
- Fail on contradictory configuration instead of silently choosing code or
  data.
- Preserve current behavior when neither file is supplied.

### 2.2 Non-Goals

- Automatic discovery or confidence scoring.
- Symbolic execution of stack-generated control flow.
- Register-derived inline-record lengths.
- General dual-use code/data representation.
- Automatically adding comments or semantic names.
- Replacing `codeentries`, `codepointers`, or `datapointers`.
- Supporting ROM layouts not already supported by NESrev.

Intentional opcode/table overlaps may be covered by a data range when data is
the preferred source representation. NESrev then does not model execution
through those bytes. Any otherwise-unreachable outbound target remains an
ordinary `codeentries.txt` seed.

## 3. Command-Line Interface

Add these NESrev options:

```text
java NESrev ROM.prg -inlinecalls FILE
java NESrev ROM.prg -dataranges FILE
```

They may be combined with each other and with the existing options.

Each option must validate a non-empty readable path before analysis starts.
NESrev is usable as a standalone command-line tool; other tooling may invoke
these options, but integration behavior is outside this specification.

## 4. Expected Standalone Workflow

This feature is configuration-driven, not automatic. For a newly encountered
ROM:

1. Generate the initial disassembly using the existing vectors, pointer tables,
   and any already-known code entries.
2. Identify helpers whose direct callers place records immediately after
   `JSR`.
3. Add one proven layout per helper to an inline-calls configuration file.
4. Run NESrev with `-inlinecalls`. NESrev then discovers all reachable callsites
   for those helpers, skips their records, follows embedded pointers, and
   resumes at their continuations.
5. Inspect the remaining false code/data boundaries. Add only genuine embedded
   data islands to a data-ranges configuration file.
6. Regenerate again and remove explicit code-entry seeds that are now derived
   automatically.
7. Repeat Steps 5-6 only if regeneration exposes another previously hidden
   corridor.
8. Assemble the generated output and compare the resulting PRG bytes against
   the input.
9. Run NESrev a second time with the same configuration and confirm the
   generated assembly is byte-identical.

The expected first-time cost is a small number of evidence-driven
configuration iterations, not zero input. Once the configuration files are
complete, subsequent regeneration should work in one command without manual
source repairs.

## 5. Inline-Call File

### 5.1 Format

Pipe-delimited UTF-8:

```text
callee|layout
$EB0A|u8,ptr16(code,+1)
$EA17|counted8
$C963|bytes(6)
$C8BB|u8,ptr16(data)

callsite|callee|layout
$C120|$C27C|ptr16(code),ptr16(code),ptr16(code)

bank|callsite|callee|layout
0|$8027|$C27C|ptr16(code),ptr16(code)
```

Rules:

- The header is required and exact.
- Blank lines and lines beginning with `#` are ignored.
- `#` and `;` begin inline comments.
- Whitespace around fields and layout tokens is ignored.
- Addresses accept `$XXXX`, `0xXXXX`, or bare hexadecimal.
- Addresses are canonical CPU addresses in NESrev's supported ROM range.
- In `callee|layout` and `bank|callee|layout` files, a callee may occur
  only once and the layout applies to every reachable direct `JSR` to that
  callee.
- In `callsite|callee|layout` and `bank|callsite|callee|layout` files, the
  callsite is the CPU address of the `JSR` opcode. A callsite may occur only
  once and the row applies only to that exact `JSR`. For bank-qualified
  callsite rows, `bank` qualifies the callsite; a `$8000-$BFFF` callee is
  resolved in the same bank, while a `$C000-$FFFF` callee resolves to the
  fixed bank.

### 5.2 Layout Grammar

```text
layout       := field ("," field)*
field        := "u8"
              | "bytes(" positive_integer ")"
              | "counted8"
              | "ptr16(" pointer_kind ["," signed_integer] ")"
pointer_kind := "code" | "data"
```

| Field | Size | Meaning |
|---|---:|---|
| `u8` | 1 | Untyped data byte |
| `bytes(N)` | N | Untyped fixed-size data block |
| `counted8` | 1 + first byte | Count byte followed by that many payload bytes |
| `ptr16(data)` | 2 | Little-endian data pointer |
| `ptr16(code)` | 2 | Little-endian code pointer |
| `ptr16(K,+N)` | 2 | Pointer of kind K with signed target adjustment |

`counted8` must be the final field.

Pointer decoding:

```text
target = (encoded_word + adjustment) & $FFFF
```

The adjusted target must be in canonical ROM space.

For:

```text
ptr16(code,+1)
```

an encoded word `$C121` traces `$C122` and emits:

```asm
.DW LC122-1
```

No register-derived field is required. Variable-length helpers that store the
payload count in the first inline byte use `counted8`.

## 6. Data-Range File

### 6.1 Format

Pipe-delimited UTF-8:

```text
start|length
$CE1A|8
$D84F|12
```

Rules:

- The header is required and exact.
- Comments, whitespace, and address syntax follow `inlinecalls.csv`.
- `start` is a canonical CPU address.
- `length` is a positive decimal integer.
- The range is `[start, start + length)`.
- Ranges must not overlap or directly touch each other; merge adjacent ranges.
- The range must fit entirely inside the ROM.

### 6.2 Meaning

A configured range:

- is emitted as data
- is never decoded as instructions
- receives a label at its start
- causes its end address to be queued as a code continuation

This file is specifically for data embedded in an otherwise executable stream.
Use `datapointers` for ordinary data tables that do not imply code resumes at
the end.

## 7. Deterministic Analysis

### 7.1 Separate Role Maps

Keep the existing `map` for final code/data output and add:

```text
boolean[] blockedFromCode
```

`blockedFromCode` is true for:

- configured data ranges
- resolved inline-record bytes

`processCodeSingle` must stop before decoding a blocked byte. The existing
`DATA` value cannot serve this purpose because it currently also means
"unclassified and eligible for tracing."

Keep parsed inline-field metadata separately for output.

### 7.2 Why Analysis Must Restart

A configured callee schema is applied only when a reachable `JSR` to that callee
is discovered. That record may already have been decoded through another path
earlier in the same traversal. Mutating the current map would make results
depend on worklist order.

Use full analysis restarts:

1. Parse and validate both files.
2. Initialize the known inline-callsite set as empty.
3. Build `blockedFromCode` from data ranges and known inline records.
4. Reset the normal code/data map.
5. Apply vectors, code-pointer tables, data-pointer tables, and code entries.
6. Seed inline code/data targets and continuations from known records.
7. Trace code normally.
8. When tracing finds a reachable `JSR` whose callee has a configured schema:
   - resolve that callsite's record from raw ROM
   - add it to the known inline-callsite set if new
9. If any callsite was added, restart from Step 3.
10. Stop when a full run adds no callsites.

The process terminates because each restart adds at least one previously
unknown direct `JSR` address and the ROM is finite.

Version 1 must always perform the full restart when a callsite is added. Do not
add a conditional fast path based on whether the current run touched the record
bytes; the simpler rule is deterministic and sufficient for 16 KB inputs.

Do not scan arbitrary ROM bytes for `JSR` patterns. Configured schemas apply only
to callsites reached as code.

### 7.3 Applying a Known Inline Record

For a known callsite:

1. Confirm raw bytes encode `JSR` to the configured callee.
2. Set `record_start = callsite + 3`.
3. Parse the layout and calculate `record_end`.
4. Block `[record_start, record_end)` from code.
5. Add a label at `record_start`.
6. For every pointer field:
   - code: label and seed the adjusted target as code
   - data: label the adjusted target without tracing it
7. Label and seed `record_end` as code.

A data-pointer target is not added to `blockedFromCode` and is not otherwise
forced to remain data. It begins with the normal unclassified `DATA` map state,
matching existing `datapointers` behavior, but may still become code if reached
independently through valid control flow. Use `dataranges.csv` when a target
must be protected from instruction decoding.

When the tracer reaches the `JSR`, queue the callee and terminate that linear
path. The continuation is already a separate seed.

### 7.4 Applying a Data Range

Before every tracing run:

1. Block the configured range from code.
2. Label its start.
3. Label and seed its end as code.

If linear tracing reaches the range start, stop that path without decoding any
range bytes.

## 8. Conflicts and Errors

Fail before producing asm when:

- a configuration file has invalid syntax
- an inline record or data range exceeds ROM
- a counted payload exceeds ROM
- an adjusted pointer target is outside canonical ROM
- two inline records overlap
- an inline record overlaps a data range
- data ranges overlap or touch
- a blocked byte is targeted by:
  - a vector
  - `codeentries`
  - an explicit code-pointer table
  - a direct `JSR` or `JMP`
  - a relative branch
  - an inline `ptr16(code,...)`

Fallthrough into the first byte of a blocked range is allowed and ends that
linear path. It is the intended use case.

An error must include:

- conflicting CPU address or range
- callsite and callee when applicable
- schema or data-range row
- source of the conflicting code claim

Example:

```text
error: inline-data conflict at $C51C
  callsite: $C518 -> $EB0A
  layout: u8,ptr16(code,+1)
  record: $C51B-$C51D
  conflicting target: codeentries line 12
```

No explicit input silently overrides another explicit input.

## 9. Output

### 9.1 Inline Records

Field boundaries control directives:

- adjacent `u8` and `bytes(N)` fields may share a `.DB` line
- `counted8` emits the count followed immediately by its payload as one logical
  `.DB` record; existing line-width wrapping may split that record across
  multiple `.DB` lines, but the count does not receive a dedicated line
- each pointer field emits one `.DW`
- fields from separate callsites are never merged

Example:

```asm
    JSR LEB0A
LC0F3:
.DB $05
.DW LC122-1

LC0F6:
    ...
```

Pointer expression rules:

- adjustment `0`: `.DW Label`
- adjustment `+N`: `.DW Label-N`
- adjustment `-N`: `.DW Label+N`

The expression must reproduce the original encoded word.

### 9.2 Data Ranges

Emit using the existing `.DB` wrapping style. Never merge a configured data
range with adjacent generic data. Its start and end remain distinct boundaries.

### 9.3 Compatibility

Without `-inlinecalls` and `-dataranges`:

- output must remain unchanged
- existing option behavior must remain unchanged

## 10. Example Configuration

Configuration files are external inputs to NESrev. They are not required to
live at any particular path.

### 10.1 `inlinecalls.csv`

```text
callee|layout
$EB0A|u8,ptr16(code,+1)
$EA17|counted8
$C963|bytes(6)
$C8BB|u8,ptr16(data)
```

### 10.2 `dataranges.csv`

```text
start|length
$CE1A|8
$D84F|12
```

Configured ranges may include bytes that also decode as legal opcodes. Choosing
data presentation means NESrev will not model execution through those bytes.
Any otherwise-unreachable outbound target must be supplied through an explicit
code-entry input.

## 11. Implementation Order

1. Add parsers and immutable configuration models.
2. Add `blockedFromCode` and data-range barriers.
3. Add configured-callee discovery with full-map restart.
4. Add pointer target seeding and conflict diagnostics.
5. Add inline-field-aware output.
6. Add CLI options and diagnostics.
7. Add tests and run the acceptance sequence.

## 12. Verification

### 12.1 Unit Tests

Add tests to `NESrevTest.java` for:

1. valid files, comments, and accepted address forms
2. malformed headers, rows, layouts, counts, and duplicate keys
3. fixed payload bytes that resemble instructions remain data
4. `counted8` resumes at the correct byte
5. adjusted code pointers are labeled and traced
6. data pointers are labeled but not traced
7. blocked-byte control-flow conflicts fail
8. overlapping records/ranges fail
9. range and counted-payload overruns fail
10. a newly discovered continuation containing another inline call causes a
    restart and reaches the final continuation
11. output uses correct `.DB`, `.DW`, and pointer expressions
12. data-range output remains bounded
13. no-option output remains unchanged

### 12.2 Synthetic Integration Test

Generate a 16 KB fixture in test code containing:

- a reset vector to a routine with an inline call
- payload bytes that decode as valid instructions and `RTS`
- a `ptr16(code,+1)` target
- a continuation containing another inline call
- a `ptr16(data)` target whose first byte is a valid opcode
- a data range followed by executable code

Verify:

- payload/range bytes are not instructions
- continuations and adjusted code targets are code
- the data target remains data
- output directives and pointer expressions are correct
- generated asm reassembles byte-identically

Do not check in an opaque or commercial binary fixture.

### 12.3 Regression Test

```sh
javac NESrev.java NESrevTest.java -Xlint:unchecked
java NESrevTest
```

All existing tests must pass.

### 12.4 Standalone Acceptance

Run NESrev directly:

```sh
java NESrev Game.prg \
  -codeentries codeentries.txt \
  -inlinecalls inlinecalls.csv \
  -dataranges dataranges.csv \
  > Game.asm
```

Then assemble `Game.asm` with a compatible 6502 assembler and compare the
assembled PRG bytes against `Game.prg`. Regenerate a second time with the same
command and confirm the generated assembly is identical.

Acceptance criteria:

1. No manual source edits are needed to restore the configured inline records or
   data ranges in the fixture under test.
2. All configured inline pointers are emitted symbolically.
3. Destination-minus-one scheduler pointers trace the adjusted destinations.
4. Inline continuations are discovered recursively.
5. Explicit code-entry seeds needed only because NESrev previously decoded
   through these configured records/ranges are no longer required.
6. Remaining explicit code entries are still accepted and traced.
7. Assembled bytes match the input PRG.
8. Regeneration is deterministic.

## 13. Completion Criteria

The feature is complete when:

- both parsers, mapping barriers, restart analysis, CLI options, diagnostics,
  and output are implemented
- unit, synthetic, and existing regression tests pass
- standalone acceptance satisfies every criterion
- no game-specific address or signature exists in NESrev
