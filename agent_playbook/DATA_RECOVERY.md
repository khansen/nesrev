# DATA_RECOVERY Playbook

This playbook owns code/data recovery mechanics, recovery artifacts, and
readability rules for data blobs and command streams. `ASM_STYLE.md` owns
label-math syntax and symbol naming.

## Ownership

This playbook owns code- and data-recovery mechanics:

- code-pointer and inline-call recovery
- recovery artifacts: `codepointers.csv`, `datapointers.csv`,
  `codeentries.txt`, `inlinecalls.csv`, `dataranges.csv`
- BIT-skip and overlapping-code cleanup
- listing-assisted pointer-blob audits
- computed-pointer consumer recovery
- orphan opcode-blob detection
- pointer-table conversion
- consumer-driven discovery of table boundaries, embedded offsets, and
  conversion opportunities
- PPU packet streams
- audio, motion, metasprite, script, and other command-stream formatting
- data blob readability and boundary rules
- hardcoded length and counter elimination in data consumers

This file owns the evidence needed to prove a table offset or bound is
derivable; [ASM_STYLE.md](ASM_STYLE.md#label-math) owns expression syntax,
symbol spelling, and literal bases.

## Playbook Sections

The sections below are the canonical recovery rules for hidden code,
tracked NESrev controls, data boundaries, and structured data formatting.

<a id="code-pointer-recovery"></a>
## Code-Pointer Recovery

**Do this before naming/refactor work.** NESrev traces linearly from known
entry points; routines reached only by indirect dispatch remain raw `.DB`
blobs. Decode common indirect-dispatch patterns early to avoid late rework.

### Core concept: inline return-table dispatch

A frequent 6502 pattern is **inline return-table dispatch**: the dispatcher
pops the caller's return address, treats it as the base of a pointer table
embedded in the caller's code stream, then jumps to the state-selected handler.

This pattern is dangerous because:

- The disassembler traces linearly and decodes the inline table as instructions, producing a spurious `RTS` (from the `$60` low byte of entry 0) and leaving the actual handler routines as unreferenced `.DB` blobs.
- The misread `RTS` terminates linear tracing at the callsite, so no handlers beyond the table are discovered automatically.
- The handler blobs accumulate unreferenced-label warnings that look like normal WIP housekeeping items.

### Step 1: Identify dispatcher signatures

After initial regeneration, scan for indirect control flow. New-project intake
remains blocked until this records either no required controls or a tracked
control configuration.

**A) General indirect flow:**

```sh
# Indirect JMP forms (pointer consumer candidates)
rg -n "JMP \(|JMP \[" Game.asm
```

**B) Inline return-table dispatchers (most common hidden-entry pattern):**
Look for routines that pop the return address from the stack.

```sh
# Double-PLA sequences are a strong signal
rg -n -A1 "^\s+PLA\b" Game.asm | rg "PLA"
```

Focus particularly on routines that:

- Call `PLA` twice in succession to recover the caller's return address.
- Store it in a zero-page pointer pair.
- Use a mode/state byte (often `ZP_*_MODE`) as an ASL-doubled index into the recovered pointer.
- Then `JMP` indirectly to the selected target.

**C) Suspected inline tables:**
Look for data blobs immediately following a `JSR`.

```sh
# Raw .DB byte streams immediately following JSR calls
rg -n -A1 "^\s+JSR\s+[A-Za-z_][A-Za-z0-9_]*" Game.asm | rg "^\s+\.DB"
```

### Step 2: Detect and decode inline tables at callsites

For every `JSR` to a suspected dispatcher routine, inspect the following bytes.

**Decoding procedure:**

1. Inspect bytes immediately after the `JSR` in the assembled/reference binary.
2. **If the first byte is `$60`, do not treat it as an RTS.** It is the low byte of the first table entry.
3. Read the following byte pairs. If the high byte of each pair falls in the ROM bank range (e.g. `$C0-$FF` for a 16 KB NES game), classify the pair as a little-endian 16-bit code pointer.
4. Stop when a byte pair clearly falls outside the mapped ROM range, or when the next region begins with a clear instruction boundary.

### Step 3: Validate extracted target addresses

For each candidate address recovered from an inline table:

1. Confirm the address is within ROM code space.
2. Inspect for coherent 6502 flow (plausible operands; terminates in
   `RTS`/`JMP`/`RTI`).
3. If decoding is coherent through a return, classify as a **confirmed code entry point**.
4. If ambiguous, mark as a **suspected code entry** and track for manual validation.

### Step 4: Re-run NESrev if multiple entry points are found

**Decision rule:**

- **1-2 new entry points:** Manually add labels at the target sites and convert the inline `.DB` bytes to `.DW` pointers. No re-run is needed.
- **3 or more new entry points,** or any target in a large untraced region: **Stop, report to the user, and re-run NESrev.** A larger number of entry points suggests a significant amount of undiscovered code that the tool should trace automatically.

Before re-running, provide a summary:

- Which dispatcher routines were identified.
- Which callsites carry inline tables.
- The list of extracted target addresses and their validation status.

Hint-file formats (`codepointers.csv`, `datapointers.csv`,
`codeentries.txt`, `inlinecalls.csv`, `dataranges.csv`), the
`make project-regenerate-asm` wrapper invocation, and configuration notes
live at [TOOLING.md#nesrev-controls](TOOLING.md#nesrev-controls). After
re-running, repeat the [NESrev Intake Sanity Gate](../AGENTS.md#nesrev-intake-sanity-gate).

### Step 5: Document all inline tables

Whether you re-ran NESrev, the final disassembly must be documented.
**Correction and documentation procedure:**

1. Remove any spurious `RTS` that was a misread table entry.
2. Convert the `.DB $lo,$hi` raw pairs to `.DW TargetLabel` entries.
3. Disassemble each handler routine that was previously a `.DB` blob.
4. Keep the inline table anonymous unless code/docs need its address. The owner
   is the dispatching callsite; do not add a global `...HandlerTable` label just
   for inventories or warnings.
5. Name the shared A-indexed return-address helper `DispatchInlineJumpTable`
   when the implementation pops the caller return address, reads the inline
   `.DW` table after the `JSR`, and tail-calls the selected handler. Do not
   invent project-local variants such as `DispatchJumpTableFromReturnAddress`
   or `DispatchViaReturnInlineTable`.

Terminal NES CPU vector words follow the same rule: ROM layout imposes their
address, so keep them anonymous unless a symbol has a real source-level use.

### General code-pointer scan procedure

When indirect dispatch hides code entrypoints from linear disassembly
*outside* the inline-return-table pattern above, use this consumer-first
process:

1. **Find candidate pointer consumers in code first.** Scan for indirect control flow (`JMP [addr]`, `JMP (addr)`) and table-driven dispatch (`ASL`/`TAY` followed by `LDA table,Y` / `LDA table+1,Y`). Identify routines that load `ZP_PtrLo` / `ZP_PtrHi` and then jump or call indirectly.
2. **Identify likely pointer tables in nearby data.** Look for low/high split tables (`...PtrLoTable`, `...PtrHiTable`); interleaved word arrays (`.DB lo,hi,...`) that should become `.DW`; repeated high bytes in the ROM-bank range (`$C0-$FF`) implying same-bank targets.
3. **Decode candidate targets and classify each one.** For every pointer target: confirm address is in mapped ROM/code space; inspect bytes at target for valid opcode flow; classify as true code entrypoint, data record start, or mixed-region boundary.

Conversion mechanics (the `.DW Label` vs `<Label`/`>Label` choice,
exact-target placement, byte-count preservation, mixed-region handling,
boundary labels, and discovery-confidence documentation) live at
[Pointer-Table Conversion](#pointer-table-conversion) and apply to every
recovered pointer table.

<a id="inline-call-recovery"></a>
## Inline-Call Recovery

Use inline-call recovery when a `JSR` is followed by inline data that the
callee consumes before returning to the byte after the record. NESrev
control-file formats and wrapper invocation live at
[TOOLING.md#nesrev-controls](TOOLING.md#nesrev-controls); conflict and
barrier behavior is specified in the standalone
`NESREV_INLINE_CALL_RECOVERY_SPEC.md`. This section owns when to recognize
the pattern and where to route the recovery work.

<a id="recovery-artifacts"></a>
## Recovery Artifacts (codepointers, datapointers, codeentries, inlinecalls, dataranges)

Recovery artifacts are tracked NESrev controls under
`projects/<slug>/config/nesrev/`. Their file formats and wrapper variables
are canonical at [TOOLING.md#nesrev-controls](TOOLING.md#nesrev-controls).
Keep recovery controls tracked with the project so regeneration is
reproducible; do not rely on ignored `reference/` hints for committed asm.

<a id="bit-skip-cleanup"></a>
## BIT-Skip and Overlapping-Code Cleanup

**Do this at intake time, before any naming or branch-literal cleanup in
affected procedures.**

NESrev preserves the raw 6502 BIT-skip overlay idiom verbatim: a
multi-entry routine where each alternate entry is reached by skipping
over the previous entry's immediate-load via a `BIT abs` instruction.
The 2-byte BIT operand happens to encode the next entry's `LDA #imm`
(or `LDX #imm` / `LDY #imm` / `LDA $zp`) opcode pair, so executing the
chain top-down loads the first immediate and BIT-skips all the rest;
entering mid-instruction at offset 1 of any BIT executes the
corresponding load instead.

### Intake symptoms

Left unprocessed, this idiom causes three intake-time problems:

- **Spurious cross-procedure references.** If the BIT operand happens to resolve to a labeled address elsewhere in the ROM, NESrev emits `BIT InitPlayer1ObjectLoop` or `BIT BonusBoxInitialStateTable-3` — references that read as semantically meaningful but are pure byte-coincidence (the operand bytes were the next entry's `LDA #imm` opcode pair, and the address happens to have low byte `$A9`).
- **Cryptic callsite arithmetic.** Alternate entries have no symbol, so callers reach them via `JSR Label+3` / `JSR Label+6` / `JSR Label+9` / `JSR OtherLabel-14` byte-offset arithmetic. Renaming the parent procedure does not update these offsets, and a reader must count bytes to locate the actual entry.
- **Cryptic relative branches.** When the dispatch into a BIT-overlay chain uses `BMI $+NN` / `BPL $+NN` PC-relative branches, the byte offsets are correct but opaque — changing the chain shape silently breaks every branch.

### Cleanup pattern

Replace each `BIT $XXyy` (where `$yy` is `$A0`/`$A2`/`$A5`/`$A9`, the
opcode for `LDY #imm` / `LDX #imm` / `LDA $zp` / `LDA #imm`
respectively) with `.DB $2C` followed by the actual labeled load
instruction. The emitted bytes are byte-identical: `BIT $XXyy` assembles
to `2C yy XX`, and `.DB $2C` + the load `(yy XX)` produces the same
three bytes. Binary parity is preserved.

Worked example: pinball's three-entry APU-note-table-dispatch chain
selects the APU channel register offset (Pulse 1 = `$00`, Pulse 2 = `$04`,
Triangle = `$08`, indexing `APU_PULSE1_TIMER_LO,X` and adjacent channel
registers) for the shared note-frequency code that follows.

Before cleanup (what NESrev would emit verbatim — entries 2 and 3 are
hidden inside `BIT` operands):

```asm
APU_NoteTable_Dispatch_P1:
    LDX #$00
    BIT $04A2          ; offset 3 -> LDX #$04 (Pulse 2)
    BIT $08A2          ; offset 6 -> LDX #$08 (Triangle)
    TAY
    ; ... shared note-frequency code
```

After cleanup:

```asm
APU_NoteTable_Dispatch_P1:
    LDX #$00
    .DB $2C
APU_NoteTable_Dispatch_P2:
    LDX #$04
    .DB $2C
APU_NoteTable_Dispatch_Tri:
    LDX #$08
    TAY
    ; ... shared note-frequency code
```

Callsites change from `JSR APU_NoteTable_Dispatch_P1+3` (Pulse 2 entry)
to `JSR APU_NoteTable_Dispatch_P2`, and `JMP APU_NoteTable_Dispatch_P1+6`
to `JMP APU_NoteTable_Dispatch_Tri`. See
`projects/pinball/asm/pinball.asm` (`APU_NoteTable_Dispatch_P1` /
`APU_NoteTable_Dispatch_P2` / `APU_NoteTable_Dispatch_Tri`).

### Pattern detection at intake

Symptoms that flag a routine for this cleanup:

- A run of consecutive `BIT $XXyy` instructions where `$yy` is `$A0`/`$A2`/`$A5`/`$A9` and `$XX` follows an arithmetic progression (or any other pattern consistent with immediate-load values).
- A `BIT` operand whose resolved label is an unrelated procedure or data table (`BIT InitPlayer1ObjectLoop`, `BIT FooTable-3`, etc.).
- Callers using `JSR Label+N` or `JSR OtherLabel-N` for small `N` that doesn't have an obvious semantic meaning.
- Relative branches like `BMI $+NN` / `BPL $+NN` clustered in dispatch-like code with `NN` values that decrease monotonically by small amounts (consecutive branches targeting alternate entries 3 bytes apart).

### Branch-target mapping

When converting `BMI $+NN` / `BPL $+NN` dispatches into named branches:

- Each entry in a `BIT $XXyy` chain is 3 bytes wide (the BIT-abs opcode plus its 2-byte operand). The cleaned-up chain uses the same 3 bytes per entry (1 byte `.DB $2C` + 2-byte load instruction).
- Consecutive `CMP #$XX; BMI $+NN` pairs are 4 bytes apart in the source. If their offsets decrease by 1 each, they target alternate entries 3 bytes apart in the chain (4 source bytes minus 1 offset delta = 3 target-byte delta).
- A final `BMI $+NN; BPL $+NN+1` pair (no intervening CMP) targets the next two entries: BPL source is 2 bytes after BMI source, and the +1 offset gives a 3-byte target advance.

### Cleanup-time housekeeping

- If a `BIT label` operand kept a label artificially alive, the label may be dead after cleanup. Check whether it has any other use; if it was only the BIT operand, either delete the label or baseline it with rationale "former BIT-overlay operand".
- If a `BIT $XXA9` cluster previously paired with literal `LDX #$XX; LDY #$YY; JSR ProcessPpuPacketStream` pointer setups, the literals often resolve to a real data label. Convert to symbolic `#<Label / #>Label` form in the same pass, so the data label has a real reference.
- `make project-verify` will report a branch-literal count drop proportional to the relative branches converted to named targets; this is the desired direction. Refresh the inventory before the next gate run.
<a id="listing-assisted-pointer-audit"></a>
## Listing-Assisted Pointer-Blob Audit

Use listings to find unresolved `.DB`-embedded ROM pointers safely.
Numeric `$C0-$FF` high bytes alone are not sufficient proof of pointers.

### Step 1: Build listing from current source

```sh
xasm --pure-binary --listing=Game.lst.json --listing-format=json Game.asm
```

(See [TOOLING.md#xasm-options](TOOLING.md#xasm-options) for listing-format details.)

### Step 2: Parse listing

JSON format treats continuation bytes as first-class records — `jq` over
the per-line `bytes` array yields exact address/byte pairs without
heuristics. Plaintext listings are reserved for human inspection — see
[TOOLING.md#xasm-options](TOOLING.md#xasm-options).

### Step 3: Restrict candidate source lines

Only audit raw numeric `.DB` payload lines (for example `.DB $12,$34,...`).
Exclude:

- `.DW` lines
- `.DB` lines already using `<Label` / `>Label`
- `.DB` lines with symbolic expressions or labels

### Step 4: Pair bytes by record alignment (not sliding windows)

By default, read candidate pointers as little-endian pairs at even offsets
(`[0,1]`, `[2,3]`, ...).
Do not classify every adjacent byte pair (`[1,2]`, `[2,3]`, etc.) as
pointer candidates unless consumer code proves that misaligned packing is
intentional.
### Step 5: Require consumer-proven pointer semantics

Before conversion, identify the consumer path:

- table load pattern (`LDA Table,Y` + `LDA Table+1,Y`)
- pointer staging into `ZP_*PtrLo` / `ZP_*PtrHi`
- indirect use (`JMP [ptr]`, `LDA [ptr],Y`, etc.)

If no such consumer exists, treat `$C0-$FF` hits as probable payload data
(common in audio streams, PPU/OAM packets, velocity/attribute tables, and
sentinels like `$FF`).

### Step 6: Convert only confirmed pointer fields

For confirmed fields:

- convert to `.DW Label` (true word tables), `<Label`/`>Label` (embedded record fields), or paired split low/high tables when the consumer really reads separate byte tables
- split blobs and introduce labels at exact target bytes as needed
- keep byte count/order identical

For unconfirmed fields:

- keep raw bytes
- annotate as non-pointer payload (`inferred` if needed)

### Step 7: Inventory sync gate

After pointer-field conversion:

```sh
make project-inventory PROJECT=<slug>
make project-verify PROJECT=<slug>
```

- ensure `inventory/pointer_targets.csv`, `inventory/embedded_pointer_targets.csv`, and `inventory/split_pointer_targets.csv` are synchronized for present shapes
- ensure no unreviewed `unknown_pointer` entries remain
<a id="computed-pointer-recovery"></a>
## Computed-Pointer Consumer Recovery

### Computed-base pointer construction

Use this pass before declaring any large contiguous data tail as
unreferenced.

#### Step 1: Computed-base audit (mandatory)

- Search for pointer construction paths that use arithmetic base constants rather than pointer tables.
- High-signal pattern: shift/index math (`ASL`/`ROL`) followed by `ADC #$lo` and `ADC #$hi`, then `STA ptr_lo/ptr_hi`.
- Once the base byte is proven, replace raw immediates with `#<Label` / `#>Label`.

#### Step 2: Indirect-read backtrace (mandatory)

- Trace all `[ZP_*],Y` (and similar indirect) consumers for the subsystem.
- For each indirect read, identify where the corresponding ZP pointer pair is populated.
- Do not rely on direct xref hits alone for unlabeled continuation bytes.
#### Step 3: Exact-entry boundary rule

- If a proven pointer or consumer reaches a byte currently claimed by an earlier blob/table, treat that as proof that the earlier declaration was too long.
- Split the earlier declaration so it ends before the newly proven target byte, and introduce an exact label at the discovered entry byte.
- Document each resulting label's semantics in `Format:` / `Used by:` comments.
- Preserve byte layout; do not duplicate or relocate bytes.
#### Step 4: Stride validation and formatting

- Infer record stride from consumer loops (for example `Y=0..7` means 8-byte records).
- Reformat the blob to one `.DB` line per inferred record while preserving exact bytes/order.
- If leftover bytes remain after full records, keep one explicit trailing `.DB` line with a parity-preserved comment.
#### Step 5: Unreferenced-tail prohibition

- Do not mark a tail as "unreferenced" until Step 1 and Step 2 are complete.
- If consumer proof exists, document the consumer chain in code comments and reverse-engineering docs in the same pass.
### Pointer-byte load sweep

Run the recipes below once the corridor's symbolization is mature enough
that the recipes produce useful candidates — typically once raw-address
debt is at or near zero and high-use RAM/ZP owners are named. Recipes
produce *candidates*, not proven pointers. For each candidate, classify
it before acting:

- *proven pointer* — pointer construction is unambiguous and the target
  resolves to a real semantic label (`#<Label` / `#>Label`), a known
  a `RAM_*Base` symbol plus field offset, or equivalent. Symbolize in the same
  batch.
- *unresolved plausible pointer* — pointer shape matches but the target
  is not yet stable enough to substitute. Leave the bytes raw and record
  an `inferred` annotation with rationale.
- *non-pointer* — false positive from the recipe's grep. No code
  annotation needed.

When a corridor's symbolization meets the maturity threshold, treat the
recipes as same-batch obligations for the proven-pointer sites the
corridor touches. The project-wide consolidation audit across all
remaining sites — including the canonical collect/classify/group/process
flow — is owned by
[REVIEW_AUDITS.md#pointer-byte-consolidation-audit](REVIEW_AUDITS.md#pointer-byte-consolidation-audit);
it is not gated on any phase, but it will typically wait until enough
symbolization has stabilized that the recipes match cleanly.
1. **Adjacent immediate-pair pointer construction.** Two `LDA #$NN` immediates whose bytes form a 16-bit pointer, typically followed by `STA ptr_lo` / `STA ptr_hi`.
   ```sh
   rg -n -B1 "LDA #\\\$[0-9A-F]{2}\\b" Game.asm | rg -A1 "STA.*[Pp]tr|STA ZP_"
   ```
   Replace with `#<Label` / `#>Label`. For RAM targets derive from a
   `RAM_*Base` symbol.

2. **Synthetic return-address push (PHA/PHA before JMP).** The two pushed bytes encode `Target-1` so the called routine's terminal `RTS` pops and adds 1, falling through into `Target` instead of returning to the caller.
   ```sh
   rg -n --multiline "LDA #\\\$[0-9A-F]{2}\\s*\\n\\s*PHA\\s*\\n\\s*LDA #\\\$[0-9A-F]{2}\\s*\\n\\s*PHA\\s*\\n\\s*JMP" Game.asm
   ```
   Verify `(high << 8 | low) + 1` lands at a real label, then replace with `LDA #>(Target-1) / PHA / LDA #<(Target-1) / PHA / JMP foo`.

3. **`LDX #lo` / `LDY #hi` argument-pair setup before JSR.** Common when a routine takes a 16-bit pointer in X/Y.
   ```sh
   rg -n -B2 "JSR " Game.asm | rg "LDX #\\\$|LDY #\\\$"
   ```
   Replace immediates with `#<Label` / `#>Label`.

4. **Raw RAM addresses inside pointer tables.** A `.DW $NNNN` (or `<addr,>addr` byte pair) where `$NNNN` falls inside a structured RAM region.
   ```sh
   rg -n "\\.DW \\\$0[0-7][0-9A-F]{2}\\b" Game.asm
   ```
   Express as `RAM_Foo+FIELD_OFFSET` instead of the raw hex word, when the address resolves into a known `RAM_*Base` / slot group / OAM shadow region.

5. **Raw `.DB`-embedded ROM pointers.** See
   [Listing-Assisted Pointer-Blob Audit](#listing-assisted-pointer-audit)
   for the full procedure. Run it inside the same corridor batch against
   any `.DB` blob whose record format is known.

<a id="orphan-opcode-decode"></a>
## Orphan Opcode-Blob Detection

After pointer-table recovery, scan for opcode-like `.DB` blobs (frequent
code bytes: `$A5`/`$A9`/`$8D`/`$85`/`$20`/`$60`).

- Convert to instructions only if decoding is coherent through `RTS`/`RTI`/`JMP`. Keep behavior identical.
- If decoded helpers are unreferenced, keep only labels required by structure
  or future recovery and curate the warning baseline with concrete rationale.
  Do not add filler comments merely because the helper lacks a static caller.
- **Parity-safe decode protocol:** capture pre-edit byte windows (`od -An -tx1`); preserve exact branch-anchor addresses; keep target labels on exact original opcode bytes. If parity fails, roll back and keep placeholder label.
### Blob-decode KPI pre-assessment

Converting `.DB` to instructions triggers cascading KPI failures. Run
this checklist BEFORE the first `make project-verify`:

1. **Raw-absrom:** replace `JSR`/`JMP $XXXX` with labels where they exist; add mid-routine labels at exact target bytes.
2. **Magic immediates:** replace `#$NN` with existing constants where applicable. Do not invent low-value constants for standard NES idioms already immediately readable to an NES developer (e.g. palette-area high byte `$3F`) unless a named constant materially improves editability or repeated semantics. Raise MAX_* only if needed.
3. **New callable procedures:** review every `JSR` target in the decoded
   region under
   [DOCUMENTATION.md#procedure-comments](DOCUMENTATION.md#procedure-comments).
   Localize internal labels where possible; add only useful non-obvious
   contract headers, never KPI filler or body narration.
4. **New data labels:** add `Format:`/`Used by:` blocks for all data labels in the decoded region.
5. **WARNING_BASELINE.txt:** remove entries for labels now referenced by newly-visible instructions.

Only after all five steps, run `make project-verify`.
<a id="pointer-table-conversion"></a>
## Pointer-Table Conversion

Canonical conversion rules for any recovered pointer table.

1. **Prefer `.DW LabelName`** for true pointer arrays. For split tables: `...PtrLoTable` with `<Label`, `...PtrHiTable` with `>Label`.
2. **Never use `.EQU` for ROM pointer targets.** Define concrete labels at real target addresses.
3. **Insert labels exactly at target byte offsets** (pointers may land mid-blob). Do not snap to nearby labels — if the target lands mid-stream, add a new entry label at that exact byte.
4. **For mixed code/data targets:** keep byte stream unchanged, add entry labels, document region type. If target is code, disassemble that region instead of leaving raw `.DB` opcodes.
5. **Preserve alignment and byte count exactly.** Tiny-table guard: confirm byte count and indexing math are unchanged after rename/reformat. Reassemble + binary compare after each batch; on mismatch use `cmp -l` and `od` windows to locate first drift and re-check endianness + label placement.
6. **Treat `BaseLabel+$NN` in pointer tables as a red flag** — split blob and introduce label at exact target byte. See [Table-offset literal elimination](#table-offset-literal-elimination) below for the rewrite pattern.
7. **Keep docs synchronized** with pointer-table renames.

<a id="embedded-record-header-pointer-sweep"></a>
### Embedded record-header pointer sweep

- Detect record-header pointer patterns: code loads bytes `+0/+1` into
  `ZP_Ptr*`. Convert `.DB $LO,$HI,...` to
  `.DB <TargetLabel,>TargetLabel,...`.
- Introduce exact labels at pointer targets. Sweep all records in the family in one batch.
<a id="table-offset-literal-elimination"></a>
### Table-offset literal elimination

- Replace `BaseLabel+$NN` and selector/request `.DB $NN` offsets into known
  record/row/stream/payload boundaries with exact labels and
  `TargetLabel-BaseLabel`; preserve order and byte count.
- Apply during the first pointer/offset-table normalization pass. If target
  rows are proven but offsets stay raw, record the evidence gap in the
  scorecard.
<a id="pointer-table-readability-normalization"></a>
### Pointer-table readability normalization

- Prefer 4 entries per `.DB` line for split pointer tables. Preserve order exactly. Keep tiny tails explicit. Verify after rewrap.
<a id="documenting-discovery-confidence"></a>
### Documenting discovery confidence

For each recovered dispatch table, document at the declaration site:

- producer routine
- consumer routine
- target classification (code / data / mixed)
- confidence (`high confidence`, `medium confidence`, `inferred`)
<a id="table-boundary-discovery"></a>
## Table Boundary and Embedded-Offset Discovery

When a blob has multiple plausible starts, first prove the consumer's
indexing expression, stride, sentinel, or embedded offset before moving
labels or reflowing rows. Pointer-table mechanics live at
[Pointer-Table Conversion](#pointer-table-conversion); hardcoded length and
counter replacement hazards live at
[Hardcoded Length Elimination](#hardcoded-length-elimination). Record
unproven boundaries in `WORKING_NOTES.md` instead of inventing labels that
only satisfy formatting.

<a id="ppu-packet-streams"></a>
## PPU Packet Streams

Treat this as a default high-probability pattern in NES projects unless
proven otherwise.

### Canonical stream format

PPU stream = zero-terminated sequence of packets:

- byte 0: PPU address high
- byte 1: PPU address low
- byte 2: control
  - bits 0-5: run length
  - bit 6: RLE flag
  - bit 7: PPU address stride flag
- payload bytes:
  - RLE packet (`bit6=1`): 1 payload byte (repeated by consumer)
  - non-RLE packet (`bit6=0`): `run_length` payload bytes

Terminator rule:

- If packet byte 0 (PPU high) is `$00`, treat as stream terminator.
- Represent terminator as its own line: `.DB $00`
### Required formatting for decoded streams

When this pattern is identified, normalize declaration layout immediately:

- one `.DB` line per packet
- one standalone `.DB $00` line for the terminator
- keep stream bytes/order identical (parity-preserved)
- if bytes exist after terminator for parity/layout reasons, keep them on a separate trailing `.DB` line with a comment (for example `; trailing bytes after stream terminator (parity-preserved)`)
### Variant: flag bits in address high byte

Some games pack the control flags into byte 0 (address high) instead of
byte 2 (length):

- bit 7: PPU address stride flag (vertical increment)
- bit 6: RLE flag (0=literal, 1=repeat single byte)
- bits 5-0: PPU address high bits (bits 13-8)
- byte 2 is a full 8-bit length (no flag bits), allowing payloads up to 255 bytes.

This works because NES PPU addresses are 14-bit — bits 6-7 of the high
byte (bits 14-15) are ignored by the hardware, so the flag bits pass
harmlessly through PPUADDR writes. When documenting this variant, use
`ppu_hi|flags` (not `ctrl`) for byte 0 to make the dual role explicit,
and show effective PPU addresses with the flag bits stripped (e.g.,
`$2380` not `$6380`).

Check for this variant when the length byte appears to use all 8 bits or
when address high bytes have unexpected bit 6/7 values.
### Detection heuristics (use early)

Prioritize this pattern when you see:

- pointer tables selecting many in-blob stream targets
- consumers that stage destination + run metadata then emit to PPU paths
- blobs with frequent `[hi, lo, ctrl, ...]` structure and regular `$00` terminators
### Packet integrity

Validate packet bounds vs copy lengths. Classify each blob as
complete/intentional-split/orphan-tail. Use exact `Start/End` labels per
copied blob. Format as one packet per `.DB` line. Treat count bits 6/7
as mode flags (RLE/stride) when applicable.
### Packet window normalization

Normalize raw `$03xx` window offsets to `RAM_PpuPacketQueueBase+offset`
in executable code. Apply as a subsystem sweep, not one-off lines. Keep
data payload blobs unchanged.
### Packet header naming

Do not use symbolic nametable/attribute/palette base addresses in PPU
packet headers — use raw hex bytes for the PPU address (e.g.,
`.DB $20, $70`). Symbolic math like `>(PPU_NT0+$070)` is harder to read
and audit than the direct VRAM address.

Do use symbolic constants for control byte flags — constants like
`PPU_PACKET_RLE` (`%01000000`) and `PPU_PACKET_STRIDE32` (`%10000000`) clarify the
packet configuration.
<a id="command-stream-formatting"></a>
## Audio, Motion, Metasprite, and Script Command-Stream Formatting

Command streams should be formatted by decoded command boundaries, not by
arbitrary byte counts. Once a consumer proves opcode/operand sizes,
sentinels, repeat/count fields, or pointer-embedded subrecords, reflow the
stream into one command or record per `.DB`/`.DW` line and document the
format at the owning label or dedicated format doc. If command boundaries
are still speculative, keep the bytes unchanged and record the evidence gap
in `WORKING_NOTES.md`.

<a id="data-blob-readability"></a>
## Data Blob Readability and Boundary Rules

When a data label has a known or strongly inferred record format,
format its `.DB` payload by logical records instead of leaving long
byte runs:

- fixed-size records: one record per `.DB` line
- standalone pointer fields: prefer `.DW Label`
- embedded pointer fields inside mixed records: use
  `<Label` / `>Label` (no `#` prefix — `#` is for instruction
  operands, not `.DB` data)
- rectangle/bounds records: one `[left, top, right, bottom]` per
  line
- PPU packet streams: one packet or logical packet row per `.DB`
  block (full canonical format at [#ppu-packet-streams](#ppu-packet-streams))
- nametable rect payloads: dimensions/control byte on its own line,
  then one row per `.DB` line when row width is known
- `$FF`-terminated streams: format complete records per line, then
  put `$FF` on its own final line when practical
- mixed-format blobs: split into labels at proven substructures;
  format only the proven windows and leave uncertain tails
  byte-preserved with a concise comment

Do this in the same pass that documents, renames, or otherwise
touches the data format. Do not defer record reflow to a later
cosmetic pass when record boundaries are already known.
### Mixed tail regions
Preserve byte layout exactly. Add boundary labels only when
producer/consumer is known. Document confirmed substreams first.
<a id="hardcoded-length-elimination"></a>
## Hardcoded Length and Counter Elimination in Data Consumers

Replace hardcoded loop bounds and counter constants with label math
derived from the data they iterate over. Concrete expression syntax
(`#(TableEnd-TableStart)`, `#(TableEnd-TableStart-1)`,
`#((COUNT*STRIDE)-1)`, etc.) lives at
[ASM_STYLE.md#label-math](ASM_STYLE.md#label-math); the rules below
govern *when* to apply them and what data-recovery hazards to watch for.

### Boundary labels for bounded blobs

Add explicit `...End` labels for blobs consumed by loops — use them for
copy/fill/scan bounds so the consumer's counter derives from the data's
shape, not from a hardcoded literal.

### Semantic count constants for slot scans

Use semantic count constants for slot scans (`ACTOR_SLOT_COUNT`).
Descending scans use `(COUNT-1)`.
### Parity-preserved counter bugs

When a hardcoded counter encodes a known ROM bug (e.g. off-by-one that
the original developer shipped), convert to a dynamic expression that
encodes the same buggy value. The inline-comment format that must
accompany the expression lives at
[DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments);
the registry expectation lives at
[QUALITY_REVIEW.md#parity-bug-registry](QUALITY_REVIEW.md#parity-bug-registry).

### Packet payload/header guard

Do not replace packet payload or header field literals unless the field's
meaning is confirmed. Do replace true semantic sentinels and enums.
### Re-verify after every rewrite

Re-verify after every counter/length rewrite. On mismatch, check
inclusive vs exclusive bound first — that's the most common drift cause.
