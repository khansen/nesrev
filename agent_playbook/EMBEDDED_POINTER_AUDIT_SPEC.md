# Embedded Pointer Audit — Improvement Spec

Design spec for `scripts/embedded_pointer_audit.py`. It captures gaps found by
manual review that the current audit cannot see, with concrete evidence and
acceptance tests. Implement improvements independently; each must pass the
validation corpus before it is relied on.

Addresses/bytes cited below are parity-invariant, so they stay valid across
relabeling passes. Metroid cases are validated against the `projects` branch;
the flat-PRG cases (clu_clu_land, tennis, pinball) likewise.

## Status

Implemented in `scripts/embedded_pointer_audit.py` (this branch): improvements
**1, 2, 3, 4, 5**. Improvement **6** (fixed-stride record mode) is deferred as
a stretch. All logic is generic — parameters are derived at runtime from the
assembled listing (`.ORG` spans → windows) and the asm text (`.EQU` aliases,
consumer patterns); no game/label/address is hardcoded. Validation is via
generic synthetic fixtures in `tests/shell/cases/embedded_pointer_test.sh`
(mirror rejection, `.EQU`-alias resolution, and non-monotonic struct
confirmation with a no-deref negative control), not by pointing at a specific
game.

## Current model (what exists)

1. Scan contiguous raw `.DB` spans for runs of `(lo,hi)` pairs that are
   **monotonic non-decreasing** and land in `$8000-$FFFF`.
2. Keep "strong" runs (`same_window >= 0.7*count` or `labeled >= 0.3*count`).
3. Confirm (→ hard fail) only when xasm `--analyze-index-patterns` reports
   `paired_byte_reads` at the run's address **and** `pointer_store_proof` finds
   the consumer storing `LDA owner`/`owner+1` into a `…PtrLo`/`…PtrHi` pair that
   is dereferenced.

This reliably prevents regression of the **sorted-pointer-array** class and
rejects gradient/scalar/pixel false positives. It is blind to several real
layouts and miscalibrated for non-banked mappers, documented below.

## Improvements

### 1. Mapper-aware target window (highest priority — fixes false positives)

**Problem.** `in_same_window` returns the full `$8000-$FFFF` when
`fixed_bank <= 0`:
```python
if fixed_bank <= 0:
    return 0x8000 <= address <= 0xFFFF
```
For NROM-128 (16 KB) the audit computes `prg_bank_count == 1` → `fixed_bank == 0`
→ this branch accepts the entire 32 KB CPU space, **including the `$8000-$BFFF`
hardware mirror where no real data lives.**

**Evidence.** `clu_clu_land` is `.ORG $C000`, 16 KB. Its ROM occupies
`$C000-$FFFF` only; `$8000-$BFFF` is an unused mirror. The audit reports **38
strong runs**, e.g. `HiddenGoldPatternPpuStream*` with targets like
`$8125-$C2FA` — spans wider than 16 KB, impossible for a real table, made of
bytes that decode into the mirror.

**Change.** Derive the valid target window(s) from the **assembled `.ORG`
spans** (the CPU ranges the ROM actually occupies), not a hardcoded banked
assumption. Apply the window to **both** the monotonic-scan acceptance test
(currently `0x8000 <= addr <= 0xFFFF`) and `same_window` scoring:
- NROM-128 assembled at `$C000` → `{$C000-$FFFF}`
- NROM-128 assembled at `$8000` → `{$8000-$BFFF}`
- NROM-256 (32 KB) → `{$8000-$FFFF}`
- banked (Metroid, MMC1) → per-bank `{$8000-$BFFF}` + fixed `{$C000-$FFFF}`

**Acceptance.** `clu_clu_land` strong count drops 38 → ~0. Metroid banked
detection is unchanged (regression guard).

### 2. Non-monotonic struct-of-pointers detection (highest priority — fixes false negatives)

**Problem.** The scan only yields monotonic runs, so a heterogeneous pointer
**struct** (several pointers to *different* tables, not a sorted array) is
skipped.

**Evidence.** `ActiveBankRoomLoadDefaultStateBlockBank1` is a 7-pointer struct:
`.DW RoomObjectStreamPtrTableBank1` then six raw pairs `$A372, $AEF0, $9DE0,
$9EE0, $9F0E, $9D6A` — **not monotonic**, but **6/6 resolve onto/just past real
labels**. Only entry 0 was relocated; entries 1-6 are raw. The family repeats
across banks 1-5 (30 raw pointers total). The monotonic scan misses all of it.

**Change.** In addition to monotonic runs, flag fixed-stride raw `.DB` runs of
`(lo,hi)` pairs where a high fraction (e.g. `>= 0.8`) resolve within a few bytes
of a known label, **regardless of ordering**. Report as a candidate; confirm via
improvement 3.

**Acceptance.** The raw form of `ActiveBankRoomLoadDefaultStateBlockBankN` is
reported as a candidate. Guardrails in the corpus stay unconfirmed.

### 3. ZP-copy + indirect-deref consumer proof

**Problem.** `pointer_store_proof` only recognizes the `LDA table,Y` /
`LDA table+1,Y` → `…PtrLo`/`…PtrHi` shape. A struct copied wholesale into a ZP
region and dereferenced word-by-word is not recognized.

**Evidence.** `CopyDefaultRoomLoadState` block-copies the room-load struct into
ZP `$3B-$48`; the game then dereferences `[ZP_RoomLoadDefaultStateBase],Y`,
`[ZP_RoomScreenObjectDefTablePtrLo],Y` ($3D), `[ZP_EnemyMetaspriteFrameDataPtrTableLo],Y`
($41), etc. — one dereference per struct word.

**Change.** Add a second consumer-proof form: a raw block whose bytes are
copied into a contiguous ZP region, where words of that ZP region are
dereferenced as `[ptr],Y`. Confirm the candidate from improvement 2 when this
holds.

**Acceptance.** `ActiveBankRoomLoadDefaultStateBlockBankN` (raw form) is
**confirmed**, not merely a candidate.

### 4. Follow `.EQU` aliases in `pointer_store_proof`

**Problem.** The proof matches the consumer by the raw span's literal owner
label. When the consumer references the table via an `.EQU` alias, the names do
not match and confirmation fails even for a genuine table.

**Evidence.** The ActiveBank metasprite subtable is anchored by
`ActiveBankObjectMetaspriteDataPtrTable .EQU ActiveBankObjectMetaspriteDataPtrTableBank1`;
the consumer does `LDA ActiveBankObjectMetaspriteDataPtrTable,X`. With the span
owner `…Bank1`, `pointer_store_proof` searches for `LDA …Bank1` and finds
nothing. Verified: reverting that subtable to raw yields a strong run that is
**not** confirmed, solely because of the alias-name mismatch.

**Change.** Resolve `.EQU` aliases (name → value → labels at that value) and
accept a consumer `LDA <alias>` when `<alias>` resolves to the owner label or
its address.

**Acceptance.** Reverting `ActiveBankObjectMetaspriteDataPtrTableBank1` to raw →
confirmed (combined with improvement 5).

### 5. Within-table displacement matching

**Problem.** Confirmation requires the run to start exactly at
`label_cpu[owner] + displacement`. Composite / shared-heavy tables fragment, so
the detected run starts mid-table and the equality check rejects it.

**Evidence.** For the ActiveBank subtable, xasm reports `paired_byte_reads` at
displacement 0 (`$860B`), but the fragmented monotonic run starts at `$866E`;
`anchor + 0 != $866E` rejects it.

**Change.** Confirm when the run start falls **within** `[anchor,
anchor + table_extent]` (extent from `data_extent_assertions.csv` or the span
length), not only at the exact anchor.

**Acceptance.** ActiveBank subtable confirmed even with a fragmented run.

### 6. Fixed-stride record pointer-field mode (stretch)

**Problem.** A pointer stored as one field inside a fixed-stride record is
invisible: consecutive `(lo,hi)` pairs mix the pointer with other fields.

**Evidence.** `PpuTransferDescriptorTable` = 29 records of
`[prg_bank, src_lo, src_hi, ppu_lo, ppu_hi, count_lo, count_hi]`; `src` is a
pointer field at offset 1 of a 7-byte stride, dereferenced `[src],Y` →
`PPUDATA`.

**Change.** Add an optional record mode: for candidate strides `S` in 3..16 and
field offsets `F` in `0..S-2`, extract the `(lo,hi)` column at `F` across records
and validate as pointers (in-window + label-hit ratio). Report the best-scoring
`(S, F)`.

**Acceptance.** Reverting the descriptor `src` fields to raw → the record mode
flags the table. Lower priority; may ship after 1-5.

## Validation corpus (teeth tests — run every version against these)

Must be **confirmed** (raw form):
- `EnemyMovementScriptPtrTableBank1-5` — regression guard, must keep working.
- `ActiveBankRoomLoadDefaultStateBlockBankN` — new (improvements 2+3).
- `ActiveBankObjectMetaspriteDataPtrTableBank1` reverted to raw — new (4+5).
- `PpuTransferDescriptorTable` src reverted to raw — new (6, stretch).

Must **not** be confirmed (false-positive guardrails):
- `TitleStartupNametablePacket` (nametable data, immediate copy-source)
- `MetaspriteAnimationOffsetTable` (scalar deltas via `ADC`)
- `clu_clu_land HiddenGoldPatternPpuStream*` (PPU stream data)
- `tennis ContactAnimCoordDeltaStream*` (coordinate deltas)
- `pinball Trig_SinTable*` (sine table — inherently monotonic)

Method: prove teeth against a known-bad state (revert a converted table to raw
in a scratch copy, confirm the audit fails), and prove precision on the
guardrails (confirm the audit passes). Never mutate the repo to test.

## Non-goals

- No auto-rename or auto-relocation — the audit reports; conversion stays a
  human/Codex pass.
- Only `confirmed` findings hard-fail. Strong/advisory candidates are reported,
  never gated (they include false positives by design).
- Semantic correctness of names is out of scope (a separate review concern).

## Rollout

- Keep per-project opt-in (`EMBEDDED_POINTER_AUDIT_REQUIRED=1`).
- Land improvements incrementally; gate each behind the corpus above so no new
  false-positive confirmation reaches the guardrail list.
- Prioritize 1 and 2 (they fix the observed false-positive inflation and the
  confirmed false negative); 3-5 raise confirmation coverage; 6 is a stretch.
- Cross-link from `TOOLING.md` once implemented.
