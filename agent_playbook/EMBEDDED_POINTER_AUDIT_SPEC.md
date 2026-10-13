# Embedded Pointer Audit — Advisory Contract

Contract for `scripts/embedded_pointer_audit.py`. Discovery and the retained
consumer-pattern matchers produce review candidates, not pointer-flow proof.
The [feasibility audit](../NESREV_STRUCTURED_ANALYSIS_MIGRATION_PLAN.md#embedded-pointer-audit)
reproduced false confirmations and missed relationships. A replacement proof
engine remains deferred; this change does not complete the structured migration.

The generic examples below describe the discovery shapes and their limits.
Addresses alone do not establish consumption or target-bank identity.

## Status

Implemented in `scripts/embedded_pointer_audit.py`: improvements
**1, 2, 3, 4, 5**. Improvement **6** (fixed-stride record mode) is deferred as
a stretch. All logic is generic — parameters are derived at runtime from the
assembled listing (`.ORG` spans → windows) and the asm text (`.EQU` aliases,
consumer patterns); no game/label/address is hardcoded. Validation is via
generic synthetic fixtures in `tests/shell/cases/embedded_pointer_test.sh`
(mirror rejection, `.EQU`-alias resolution, and non-monotonic struct
matching with a no-deref negative control). CLI and bundle controls in
`tests/embedded_pointer_audit_test.py` include genuine pointer use and overwritten
pointer bytes that still match. Both must remain advisories.

## Output and failure policy

- Keep the discovery counters `embedded_pointer_raw_runs_total`,
  `embedded_pointer_raw_runs_strong` and `embedded_pointer_struct_candidates`.
  These count detected shapes, not proven tables or executed entries.
- `embedded_pointer_heuristic_matches` replaces
  `embedded_pointer_confirmed_unrelocated`. The count combines the two legacy
  consumer-pattern matchers; no compatibility counter claims confirmation.
- Print at most twenty `ADVISORY:` details with owner, bank, CPU location,
  pair count, value range, matched text and **pointer flow unproven**. Report
  omitted matches separately. Matching bank windows are candidate filters, not
  runtime bank proof. No match is not a completeness claim.
- Valid analysis exits `0` with or without findings. Findings no longer exit
  `68`. Wrong argument counts exit `64`; a non-integer `min_run`, missing source
  and rejected supplied evidence exit `65`; a missing assembler exits `66`.
  The non-integer refusal preserves the existing numeric-input behavior.
  Assembly failure retains its nonzero status and diagnostics. Invalid supplied
  evidence never falls back to a standalone assembly.
- `project-verify` and `project-maturity-check` still run the audit and expose
  its report. They propagate operational failures. Independent pointer
  inventories, split-table checks and named pointer-body policies are unchanged.

### Advisory disposition

A validated disposition route for these matches is deferred until the first
real-project match under this policy. That follow-up must define how the
finding is resolved or recorded; exit `0` does not resolve a finding. No new
ledger or disposition gate is introduced by this change.

## Current model (what exists)

1. Scan contiguous raw `.DB` spans for runs of `(lo,hi)` pairs that are
   **monotonic non-decreasing** and land in `$8000-$FFFF`.
2. Keep "strong" runs (`same_window >= 0.7*count` or `labeled >= 0.3*count`).
3. Add an unproven match when xasm `--analyze-index-patterns` reports
   `paired_byte_reads` near the run and `pointer_store_match` finds matching
   load/store text for `owner`/`owner+1` and a `…PtrLo`/`…PtrHi` pair, plus
   indirect-read text naming the low byte.
4. Also discover non-monotonic runs and match indexed load/store and
   indirect-read text through `struct_copy_deref_match`.

These matches do not establish register flow, clobbers, reachable entries,
runtime bank identity or preservation of copied bytes until use. They can match
contradicted relationships and miss genuine ones. No new parsing or flow
analysis is added by the advisory policy.

## Retained discovery shapes and deferred extensions

### 1. Mapper-aware target window

**Original problem.** The former `in_same_window` returned the full
`$8000-$FFFF` when `fixed_bank <= 0`:
```python
if fixed_bank <= 0:
    return 0x8000 <= address <= 0xFFFF
```
For NROM-128 (16 KB) the audit computes `prg_bank_count == 1` → `fixed_bank == 0`
→ this branch accepts the entire 32 KB CPU space, **including the `$8000-$BFFF`
hardware mirror where no real data lives.**

**Evidence.** A representative flat-PRG (NROM-128) project is `.ORG $C000`,
16 KB. Its ROM occupies `$C000-$FFFF` only; `$8000-$BFFF` is an unused mirror.
The audit reports **38 strong runs** — e.g. a wide PPU-stream data blob with
targets like `$8125-$C2FA` — spans wider than 16 KB, impossible for a real
table, made of bytes that decode into the mirror.

**Change.** Derive the valid target window(s) from the **assembled `.ORG`
spans** (the CPU ranges the ROM actually occupies), not a hardcoded banked
assumption. Apply the window to **both** the monotonic-scan acceptance test
(formerly `0x8000 <= addr <= 0xFFFF`) and `same_window` scoring:
- NROM-128 assembled at `$C000` → `{$C000-$FFFF}`
- NROM-128 assembled at `$8000` → `{$8000-$BFFF}`
- NROM-256 (32 KB) → `{$8000-$FFFF}`
- banked (MMC1) → per-bank `{$8000-$BFFF}` + fixed `{$C000-$FFFF}`

**Acceptance.** The flat-PRG project's strong count drops 38 → ~0. Banked
(MMC1) detection is unchanged (regression guard).

### 2. Non-monotonic struct-of-pointers detection

**Problem.** The scan only yields monotonic runs, so a heterogeneous pointer
**struct** (several pointers to *different* tables, not a sorted array) is
skipped.

**Evidence.** `BankedStateBlockBank1` is a 7-pointer struct:
`.DW SubTablePtrTableBank1` then six raw pairs `$A372, $AEF0, $9DE0,
$9EE0, $9F0E, $9D6A` — **not monotonic**, but **6/6 resolve onto/just past real
labels**. Only entry 0 was relocated; entries 1-6 are raw. The family repeats
across banks 1-5 (30 raw pointers total). The monotonic scan misses all of it.

**Implemented shape.** In addition to monotonic runs, flag stride-two raw `.DB`
runs where every pair is in-window, the values are not monotonic, and a
monotonic run does not already contain the candidate. Label counts are
diagnostic, not an admission threshold. Shape 3 can add an unproven
consumer-pattern match.

**Acceptance.** The raw form of `BankedStateBlockBankN` is
reported as a candidate. Scalar/graphics controls must not gain a heuristic
match without the required text patterns.

### 3. Indexed-copy + indirect-read heuristic

**Problem.** `pointer_store_match` only recognizes the `LDA table,Y` /
`LDA table+1,Y` → `…PtrLo`/`…PtrHi` shape. A struct copied wholesale into a ZP
region and dereferenced word-by-word is not recognized.

**Evidence.** `CopyStateBlockToZp` block-copies the state block into
ZP `$3B-$48`; the consumer then dereferences `[ZP_StateBlockBase],Y`,
`[ZP_SubTableAPtrLo],Y` ($3D), `[ZP_SubTableBPtrLo],Y`
($41), etc. — one dereference per struct word.

**Implemented shape.** Match indexed source load and destination store text
using the same index, plus indirect-read text naming the destination.
This neither validates the destination's ZP address nor proves a complete copy,
control-flow connection or absence of intervening writes.

**Acceptance.** `BankedStateBlockBankN` (raw form) is
reported with a heuristic match. Overwriting the destination before the read
still matches and must also remain report-only.

### 4. Follow `.EQU` aliases in `pointer_store_match`

**Problem.** The heuristic matches the consumer by the raw span's literal owner
label. When the consumer references the table via an `.EQU` alias, the names do
not match and the heuristic misses even a genuine table.

**Evidence.** The banked subtable is anchored by
`BankedSubTablePtr .EQU BankedSubTablePtrBank1`;
the consumer does `LDA BankedSubTablePtr,X`. With the span
owner `…Bank1`, `pointer_store_match` searches for `LDA …Bank1` and finds
nothing. Verified: reverting that subtable to raw yields a strong run that is
**not** matched without alias handling, solely because of the name mismatch.

**Implemented shape.** Recognize direct `<alias> .EQU <label>` text and include
the alias when matching loads from the owner. This is not general expression
resolution or a completed migration to structured symbol facts.

**Acceptance.** Reverting `BankedSubTablePtrBank1` to raw →
an unproven heuristic match (combined with shape 5).

### 5. Within-table displacement matching

**Original problem.** Matching required the run to start exactly at
`label_cpu[owner] + displacement`. Composite / shared-heavy tables fragment, so
the detected run starts mid-table and the equality check rejects it.

**Evidence.** For the banked subtable, xasm reports `paired_byte_reads` at
displacement 0 (`$860B`), but the fragmented monotonic run starts at `$866E`;
`anchor + 0 != $866E` rejects it.

**Implemented shape.** Match when the run start falls within
`[anchor, anchor + 0x400]`, not only at the exact anchor. That fixed search
window is not a reviewed table extent; the matcher does not read
`data_extent_assertions.csv` or prove the candidate bytes are consumed.

**Acceptance.** A fragmented run can receive an unproven heuristic match.

### 6. Fixed-stride record pointer-field mode (stretch)

**Problem.** A pointer stored as one field inside a fixed-stride record is
invisible: consecutive `(lo,hi)` pairs mix the pointer with other fields.

**Evidence.** `PpuTransferDescriptorTable` = 29 records of
`[prg_bank, src_lo, src_hi, ppu_lo, ppu_hi, count_lo, count_hi]`; `src` is a
pointer field at offset 1 of a 7-byte stride, dereferenced `[src],Y` →
`PPUDATA`.

**Change.** Add an optional record mode: for candidate strides `S` in 3..16 and
field offsets `F` in `0..S-2`, extract the `(lo,hi)` column at `F` across records
and filter candidates by window and label-hit ratio. Report the best-scoring
`(S, F)` without claiming pointer flow.

**Acceptance.** Reverting the descriptor `src` fields to raw → the record mode
flags the table. Lower priority; may ship after 1-5.

## Historical corpus controls

These raw-form examples belong to the earlier discovery proposals, including
the deferred record mode. They were not rerun for the advisory policy change;
the current regression method is described below.

Discovery/matching controls (raw form; always report-only):
- `ScriptPtrTableBank1-5` — regression guard, must keep working.
- `BankedStateBlockBankN` — new (improvements 2+3).
- `BankedSubTablePtrBank1` reverted to raw — new (4+5).
- `PpuTransferDescriptorTable` src reverted to raw — new (6, stretch).

No-match controls when the required consumer text is absent:
- `TitleStartupNametablePacket` (nametable data, immediate copy-source)
- `MetaspriteAnimationOffsetTable` (scalar deltas via `ADC`)
- a wide PPU-stream data blob (immediate copy-source, not pointers)
- a coordinate-delta stream (signed deltas via `ADC`, not pointers)
- a sine/trig table (inherently monotonic, not pointers)

## Current regression method

Use synthetic genuine and contradicted matches, no-dereference and
comment-only controls, and standalone/bundle output parity. Prove that restoring
the findings-as-failures behavior breaks the advisory tests. Separately inject
assembly and evidence errors and require nonzero exits. In an otherwise passing
synthetic project, make only the audit fail and require both verification and
maturity to fail with its diagnostic. Preserve independent
pointer gates with their own failing fixtures. Mutate only disposable copies.

## Non-goals

- No auto-rename or auto-relocation — the audit reports; conversion stays a
  human/Codex pass.
- No finding hard-fails. Shape and consumer-pattern matches are reported,
  never gated; neither is semantic proof.
- Semantic correctness of names is out of scope (a separate review concern).

## Rollout

- Run the audit for every project; missing canonical inventories are defects,
  not a way to suppress the check.
- Keep discovery and match membership stable for this policy change. Measure
  corpus output and wrapper cost; zero observed legacy confirmations does not
  prove that no future protection is lost.
- Shapes 1–5 remain heuristics. Shape 6 and any replacement proof engine need
  separate scope, evidence and authorization.
- Cross-link from `TOOLING.md` once implemented.
