# ASM_STYLE Playbook

This playbook is the canonical home for assembly-source style and symbolization rules. The root `AGENTS.md` retains the compact naming summary; the sections below carry the full rule text and cross-link to neighboring playbooks where another file owns a related rule.

## Ownership

This playbook owns assembly-source style and symbolization:

- naming conventions
- local/global label rules
- placeholder-name policy
- relocatability rules
- literal-base readability
- NOP, padding, and parity-preserved oddity representation
- hardware, OAM, joypad, PPU, and APU constants
- structured field offsets and overlays
- fixed-point naming
- state/action constants
- the normative requirement and expression conventions for replacing hardcoded
  pointers, lengths, counts, and offsets with label math
- tail-call and parity-preserved redundant-instruction annotations
- RAM/ZP naming evidence, overlay restraint, structured-field naming, and
  symbol-family conventions

Canonical ownership decisions:

- Literal-base readability lives only here.
- Hardware constant names and values live only here.
- Label-math syntax and the requirement to prefer derivable expressions live
  only here. [DATA_RECOVERY.md](DATA_RECOVERY.md) links here for the rule and
  owns only discovery and evidence.
- RAM symbolization prioritization lives in
  [PASS_WORKFLOW.md](PASS_WORKFLOW.md#raw-ram-prioritization); naming and
  overlay rules live here.
- Data-oriented playbooks link here when showing literals or symbolic fields.

## Playbook Sections

The sections below are the canonical style rules for assembly naming,
literal formatting, symbolic expressions, and RAM/ZP symbolization.

<a id="naming-conventions"></a>
## Naming Conventions

### Principles

These mirror the compact summary in
[AGENTS.md#core-naming](../AGENTS.md#core-naming) and expand it with the
canonical wording from `AGENTS.md` for use during in-depth work:

- **Semantic, role-oriented names.** Choose names that describe what the
  symbol *is*, not where it lives. Address-coded names like
  `Byte8FTimerPairTable` or `Group03C0Slot` are anti-patterns unless
  address identity itself is the meaning. Prohibited: broad placeholder
  alias sweeps (`ZP_XX`, `RAM_XXXX`) whose primary purpose is lowering KPI
  counts.
- **No address/value-coded placeholders unless explicitly tracked.** See
  [Placeholder Name Policy](#placeholder-policy) for the WORKING_NOTES.md
  revisit-entry requirement.
- **Canonical cross-project vocabulary.** Use the canonical names for
  standard NES hardware, OAM, joypad, PPU, and APU constants — see
  [Hardware Constants](#hardware-constants). Do not invent project-local
  variants for cross-project standards. When uncertainty exists, keep
  neutral but semantically scoped names plus `inferred` notes, then
  promote confidence as evidence improves.
- **Localize branch-only labels when scope permits** — see [Local label
  cleanup](#naming-conventions) below.

### Symbol prefix families

- Zero-page and RAM symbols:
  - `ZP_<UpperCamelRole>` and `RAM_<UpperCamelRole>`.
  - The prefix separator is the only underscore: use `ZP_PpuCtrlShadow`,
    `ZP_PlayerPosXLo`, and `RAM_OamShadowBase`, not
    `ZP_PPUCTRL_SHADOW`, `ZP_PLAYER_POS_X_LO`, or
    `RAM_OAM_SHADOW_BASE`.
  - Title-case acronyms inside the semantic body (`Ppu`, `Nmi`, `Oam`,
    `Apu`, `Bcd`, `Rng`, `Sfx`, `Dmc`, `Prg`, `Chr`, `Vram`). Preserve
    single-letter axes and player designators (`X`, `Y`, `P1`, `P2`) and
    use `Lo`, `Hi`, `Idx`, and `Base` suffixes.
  - `project-process-check` and `make test` reject nonconforming
    definitions.
- Procedures:
  - `InitX`, `UpdateX`, `RenderX`, `RunX`, `HandleX`, `ResolveX`, `QueueX`, `SetX`, `CheckX`
  - `DispatchInlineJumpTable` for the common A-indexed helper that pops the
    caller return address, reads the inline `.DW` target table immediately
    after the `JSR`, and tail-calls the selected handler. Wrappers that seed
    the index before entering that helper should keep the canonical base name
    plus a source suffix, for example `DispatchInlineJumpTableByMainMode`.
  - CPU vector entry labels are exactly `Reset`, `NMI`, and `IRQ` when present.
    Do not use project-local variants such as `ResetHandler`,
    `ResetEntryPoint`, `NmiHandler`, `NMI_Handler`, or `IRQ_Handler`.
- Tables:
  - `...Table` (lookup)
  - `...PtrLoTable` / `...PtrHiTable` (pointer tables)
- RAM arrays:
  - Use the same UpperCamelCase body, for example
    `RAM_ActorPosXBySlot`.
  - Use a `...Base` suffix for offset aliases into larger arrays.
- Scoped overlays:
  - If one corridor proves a role for a globally mixed byte, use a narrow
    `ZP_`/`RAM_` alias at the proven sites, leave unrelated owners raw, and
    record `confidence=scoped-overlay`.
  - Reject broad global names that hide mixed ownership, not the overlay
    corridor itself.
- Bulk memory loops: use bases such as `ZP_ZeroPageBase`; do not use
  semantic field aliases as indexed range bases.
- Confidence:
  - Use suffix comments like `; inferred: ...` where needed

### Local label cleanup

- Convert global `LXXXX` labels that are only locally referenced into `@@` local labels.
- **Localization expectation:** In line with [Guiding Pass Philosophy](../AGENTS.md#guiding-pass-philosophy), localize all safe internal branch labels while the routine is open. Skip only if: cross-scope reference, `JSR`/`JMP` target, jump-table target, or wrapper marks unsafe.
- **Naming style:** `@@lowerCamelCase` (`@@checkInput`, `@@loop`, `@@next`, `@@exit`). No snake_case/PascalCase. Concise names; do not repeat the routine prefix.
- **Loop labels:** Default to explicit `@@loopName`. Use anonymous `-` only for short linear backward loops with no intermediate branches. Place `-` on the instruction line (`- LDA ...`).
- **Pre-conversion scope audit (mandatory):** Grep all references for each candidate. Only convert labels whose every reference falls within a single non-local scope. Build the safe list before editing. Retrofitting scope promotions causes rework.
- **Scope rules:** `@@` labels are visible only until the next non-local label. Check for mid-routine scope splits (intervening non-local labels/helpers). Targets reachable across scope splits must stay non-local.
- **Do not localize:** `JSR`/`JMP` targets from outside, jump/dispatch table entries, labels anchored on opcode bytes shared with table data.
- **Opcode-anchored labels:** Keep at exact original address. Do not move across instruction boundaries. Verify table base address is unchanged after edits.
- **Relative branch literals (`$+N`/`$-N`):** Treat as parity-sensitive. Do not rewrite to named labels unless target is proven instruction boundary.
- **Parity trampolines:** Do not collapse `JMP` trampolines into fallthrough without verifying byte-for-byte parity.
- **Doc hygiene:** Update `Used by:` lines and docs that mention localized internal labels in the same pass.
- **Dual KPI tracking:** Track both definition count (`^L[0-9A-F]{4,5}:`) and total occurrence count in scorecard.
- **Constraint notes:** Record in scorecard when a label is intentionally left non-local (scope split, parity risk, shared entry).
<a id="local-global-labels"></a>
## Local and Global Label Rules

See [Naming Conventions → Local label cleanup](#naming-conventions) above.

<a id="placeholder-policy"></a>
## Placeholder Name Policy

Placeholder names are temporary evidence markers, not durable style. This
section expands the compact placeholder principles in
[AGENTS.md#guiding-pass-philosophy](../AGENTS.md#guiding-pass-philosophy).

- Use semantic, role-oriented names as soon as evidence is strong enough.
- Do not run broad placeholder alias sweeps (`ZP_XX`, `RAM_XXXX`, address
  table names, value-coded constants) whose primary effect is KPI movement.
- Mechanical symbolization is allowed only when it immediately enables
  semantic naming in the same pass or a recorded continuation plan in
  `current_pass_plan.*` or `WORKING_NOTES.md`.
- If an address-bearing or structural placeholder is unavoidable, record
  the exact revisit condition in `WORKING_NOTES.md`; do not let it silently
  fossilize.
- Once semantics are known, replace placeholder/value/address vocabulary
  (`StateNN`, `ModeNN`, `FieldNN`, `AddrNNNN`, raw hex suffixes) with the
  semantic name in the same corridor batch.

<a id="relocatability"></a>
## Relocatability Rules

Treat the asm as if a byte inserted at `$C000` should not require manual address repair.

1. No hardcoded ROM addresses in executable logic when labels can be used.
- Replace:
  - `JSR $XXXX` / `JMP $XXXX`
  - `LDA #$LO` + `STA ptr_lo` / `LDA #$HI` + `STA ptr_hi`
- With:
  - `JSR Label` / `JMP Label`
  - `#<Label` / `#>Label`

2. No raw embedded pointers when target meaning is known.
- Convert embedded pointer bytes in records/streams to `<Label` / `>Label`.
- Add labels at exact target bytes (including mid-blob targets).
- If consumer code reads an anchored overlap byte such as `Table-1`, `Table+N`, or another exact byte adjacent to the main blob, do not leave that byte buried anonymously inside the neighboring data declaration.
- Introduce an exact label at that byte and document both semantics when the byte is shared.

3. No hardcoded loop/table sizes when derivable.
- Use `Start/End` label expressions for counts and bounds.
- Prefer `#(End-Start-1)` for reverse loops and `#(End-Start)` for forward bounds.
- Mandatory: when a bounded table/stream is consumed by loops, add explicit boundary labels
  (for example `TableStart`/`TableEnd`) and derive bounds from those labels.
- Mandatory: do not keep fixed numeric `*_COUNT` / `*_LAST_IDX` constants when the value is
  derivable from labels. If reuse is needed, define the constant from label math
  (for example `.EQU (End-Start)` or `.EQU (End-Start-1)`), not a hardcoded literal.
- Preferred at use sites:
  - reverse loop init: `LDX #(End-Start-1)`
  - forward bound compare: `CPY #(End-Start)`
  - reusable aliases: `TABLE_COUNT .EQU (End-Start)`, `TABLE_LAST_IDX .EQU (End-Start-1)`

4. Symbolize indirect addressing operands.
- Replace `JMP [$NNNN]`, `[$NN],Y`, etc. with symbolic pointer names where known.

5. Symbolize structured field operands once pointer shape is known.
- When an indirect pointer is proven to address a structured record (actor slot,
  sprite strip, OAM record, packet descriptor, status record, etc.), replace raw
  `LDY #$NN` field offsets with the appropriate `*_FIELD_*` symbol across that
  pointer corridor.
- Include overlay field aliases when a shared record page is intentionally reused
  with local semantics; do not force a misleading global slot-field name when a
  contextual alias is clearer.
- If code advances through adjacent fields with `INY` instructions instead of loading
  each offset, keep the byte-saving instruction sequence and add inline comments
  naming the field reached after each meaningful increment, for example
  `INY ; SLOT_FIELD_POS_Y`. The comment is not redundant: unlike
  `LDY #SLOT_FIELD_POS_Y`, `INY` does not encode the destination field.
- Do not symbolize stream cursors, packet payload bytes, or descriptor indexes as
  record fields unless the format is already proven.
6. Pointer tables must be label-per-entry (no base+offset).
- Applies to all pointer tables once the target byte is known, including fixed-size tables and mutable variable-length streams.
- Do not use `BaseLabel+Offset` pointer expressions in pointer tables (`<(Base+$NNNN)`, `>(Base+$NNNN)`, `.DW Base+$NNNN`).
- Instead, create a dedicated label at each pointed-to target byte and reference that label directly from the table.
- If the target currently lies inside a larger blob, split the blob and introduce the new label at the exact byte.
- Rationale: label-per-entry tables are easier to edit, easier to review, and avoid hiding real target structure behind offset arithmetic.

<a id="literal-base-readability"></a>
## Literal Base Readability

Choose numeric base by semantics, not habit.

- Prefer decimal for human-readable quantities such as:
  counts, durations, score limits, hole counts, decimal divisors (`100`, `10`, `1`), and simple unit-step arithmetic (`ADC #1`, `SBC #1`) when the value is naturally understood in base 10.
- Prefer signed decimal for two's-complement quantities when the code is
  semantically reasoning about a negative value rather than a raw byte, such as
  pre-increment/pre-decrement scan seeds (`#-1`, `#-3`, `#-5`) or signed wrap
  cursors. Do not rewrite when the same byte is clearer as a mask, token,
  sentinel, tile/control value, or range discriminator.
- Prefer hexadecimal for machine-oriented values such as:
  hardware control values, tile ids, packed non-bit tokens, pointer math,
  sentinel bytes, and encoded stream tokens.
- Prefer binary for bit flags and bit masks, including project-local packed
  flag/state bytes, joypad masks, PPU/APU shadow masks, and hardware status
  bits. When one bit in a packed family is named, audit the whole touched
  family and introduce composite masks for repeated groups rather than
  leaving nearby raw `#$NN` bit tests. Clear masks must be derived from the
  positive bit or mask constant (`~FOO_BIT` or `~FOO_MASK`) instead of
  restating the inverse literal. For compound clear masks, introduce the
  positive `*_MASK` first, then define the clear mask from it.
- When a literal has a stable semantic role and appears more than once, prefer introducing a named constant over relying on either raw decimal or raw hex.
- Do not churn literals mechanically; only rewrite base when it clearly improves readability.
<a id="hardware-constants"></a>
## Hardware, OAM, Joypad, PPU, and APU Constants

### Hardware bitmask handling (same-corridor obligation)

When a corridor touches I/O register usage, shadow update paths, or hardware-control immediates, close the bitmask work in the same batch — do not defer to a dedicated repository-wide pass.

- Replace active hardware-control immediates touched by the corridor with named masks/constants.
- Use canonical NES I/O register aliases in executable logic; do not leave raw `$200x` / `$401x` register operands once the hardware role is known.
- Required domains when touched: `PPUCTRL`, `PPUMASK`, `APU_*` control paths, and joypad button masks.
- Do not leave raw `#$NN` masks in shadow update paths unless explicitly documented as unknown payload semantics.
- **All projects must use the canonical register and constant names listed below.** When introducing new hardware constants, check the table first. When renaming across projects, update authored docs (not just asm) and regenerate inventories in the same commit.
- Project-wide residual searches near maturity belong to [QUALITY_REVIEW.md#residual-magic-number-and-hardcoded-offset-review](QUALITY_REVIEW.md#residual-magic-number-and-hardcoded-offset-review). They may surface a new coherent corridor; they do not authorize blind repository-wide replacement.
### Canonical NES hardware constant names (cross-project standard)

All projects must use these names for standard NES hardware registers and constants. Do not invent project-local variants. Project-local `.EQU`s that use a canonical hardware prefix but are absent from this table are flagged by an advisory drift check ([PASS_WORKFLOW.md#hardware-drift](PASS_WORKFLOW.md#hardware-drift)): rename, promote here if globally reusable, or allowlist a project-local composite/encoding.
The value notation follows [Literal Base Readability](#literal-base-readability): register addresses and structured
offsets use hexadecimal, bit flags and masks use binary, and human-readable
counts use decimal.

**I/O registers (mandatory aliases in executable logic):**
| Constant | Value | Notes |
|---|---|---|
| `PPUCTRL` | $2000 | |
| `PPUMASK` | $2001 | |
| `PPUSTATUS` | $2002 | |
| `OAMADDR` | $2003 | |
| `PPUSCROLL` | $2005 | |
| `PPUADDR` | $2006 | |
| `PPUDATA` | $2007 | |
| `APU_PULSE1_CTRL` | $4000 | |
| `APU_PULSE1_SWEEP` | $4001 | |
| `APU_PULSE1_TIMER_LO` | $4002 | |
| `APU_PULSE1_TIMER_HI` | $4003 | |
| `APU_PULSE2_CTRL` | $4004 | |
| `APU_PULSE2_SWEEP` | $4005 | |
| `APU_PULSE2_TIMER_LO` | $4006 | |
| `APU_PULSE2_TIMER_HI` | $4007 | |
| `APU_TRI_LINEAR` | $4008 | |
| `APU_TRI_TIMER_LO` | $400A | |
| `APU_TRI_TIMER_HI` | $400B | |
| `APU_NOISE_CTRL` | $400C | |
| `APU_NOISE_PERIOD` | $400E | |
| `APU_NOISE_LENGTH` | $400F | |
| `APU_DMC_CTRL` | $4010 | DMC flags/rate |
| `APU_DMC_DA` | $4011 | DMC direct load (DAC) |
| `APU_DMC_ADDR` | $4012 | DMC sample base address |
| `APU_DMC_LEN` | $4013 | DMC sample length |
| `OAMDMA` | $4014 | |
| `APU_STATUS` | $4015 | |
| `JOY1_STROBE` | $4016 | |
| `APU_FRAME_COUNTER` | $4017 | |

Do not leave raw `$2000..$2007` / `$4000..$4017` operands in executable logic once the hardware role is known. If a project uses a register through indexed access (for example `APU_PULSE1_TIMER_LO,X` or `JOY1_STROBE,X`), keep the canonical base alias and let the index express the variant port/register.
When a pass touches hardware-register logic, symbolize the touched register operands and any proven associated bitmasks/shadow writes in the same pass instead of deferring them as cleanup debt.

**Joypad buttons and d-pad:**

| Constant | Value | Notes |
|---|---|---|
| `PAD_BTN_A` | %10000000 | |
| `PAD_BTN_B` | %01000000 | |
| `PAD_BTN_SELECT` | %00100000 | |
| `PAD_BTN_START` | %00010000 | |
| `PAD_DIR_UP` | %00001000 | |
| `PAD_DIR_DOWN` | %00000100 | |
| `PAD_DIR_LEFT` | %00000010 | |
| `PAD_DIR_RIGHT` | %00000001 | |
| `PAD_DIR_MASK` | %00001111 | All d-pad bits |
| `PAD_STROBE_ON` | %00000001 | Write to $4016 to latch |
| `PAD_STROBE_OFF` | %00000000 | Write to $4016 to release |
| `PAD_SERIAL_BIT_COUNT` | 8 | Joypad shift register pulses only; leave project-local name if used in broader serial protocol context |

Compound joypad masks (e.g. `PAD_BTN_A_B`, `PAD_DIR_UP_DOWN_MASK`, `PAD_BTN_START_SELECT_MASK`) use `PAD_BTN_` for face-button combos and `PAD_DIR_` for d-pad combos. Clear-masks use suffix `_CLEAR_MASK` (e.g. `PAD_BTN_CLEAR_A_MASK`) and are defined from the bit/mask they clear, not as inverse literals.

**PPUCTRL ($2000) bits:**

| Constant | Value | Notes |
|---|---|---|
| `PPUCTRL_NMI_ENABLE` | %10000000 | |
| `PPUCTRL_NMI_DISABLE_MASK` | `~PPUCTRL_NMI_ENABLE` | AND clear-mask |
| `PPUCTRL_NAMETABLE_2800` | %00000010 | Base nametable bit for $2800 |
| `PPUCTRL_NAMETABLE_2800_CLEAR_MASK` | `~PPUCTRL_NAMETABLE_2800` | AND clear-mask |
| `PPUCTRL_SPRITE_8X16` | %00100000 | 8x16 sprite size (clear = 8x8) |
| `PPUCTRL_BG_PT_1000` | %00010000 | Background pattern table at $1000 |
| `PPUCTRL_SPRITE_PT_1000` | %00001000 | Sprite pattern table at $1000 |
| `PPUCTRL_VRAM_INC_32` | %00000100 | Column-mode increment |
| `PPUCTRL_VRAM_INC_CLEAR_MASK` | `~PPUCTRL_VRAM_INC_32` | AND clear-mask to revert to increment-1 |

Composite PPUCTRL init values (e.g. `PPUCTRL_NMI_ENABLE|PPUCTRL_BG_PT_1000`) are project-specific and may use project-local names.

**PPUMASK ($2001) bits:**

| Constant | Value | Notes |
|---|---|---|
| `PPUMASK_GRAYSCALE` | %00000001 | |
| `PPUMASK_SHOW_BG_LEFT` | %00000010 | Show background in leftmost 8 pixels |
| `PPUMASK_SHOW_SPRITES_LEFT` | %00000100 | Show sprites in leftmost 8 pixels |
| `PPUMASK_SHOW_BG` | %00001000 | |
| `PPUMASK_SHOW_SPRITES` | %00010000 | |
| `PPUMASK_EMPHASIZE_RED` | %00100000 | |
| `PPUMASK_EMPHASIZE_GREEN` | %01000000 | |
| `PPUMASK_EMPHASIZE_BLUE` | %10000000 | |
| `PPUMASK_HIDE_SPRITES_MASK` | %11101111 | AND clear-mask for sprite rendering |
| `PPUMASK_RENDER_ENABLE_MASK` | %00011000 | BG + sprite rendering bits |
| `PPUMASK_RENDER_DISABLE_MASK` | %11100111 | AND clear-mask for BG + sprite rendering |

**PPUSTATUS ($2002) bits:**

| Constant | Value | Notes |
|---|---|---|
| `PPUSTATUS_VBLANK_BIT` | %10000000 | VBlank flag (bit 7) |
| `PPUSTATUS_SPRITE_0_HIT` | %01000000 | Sprite 0 hit flag (bit 6) |
| `PPUSTATUS_SPRITE_OVERFLOW` | %00100000 | Sprite overflow flag (bit 5) |

**APU control:**

| Constant | Value | Notes |
|---|---|---|
| `APU_STATUS_ENABLE_ALL` | %00001111 | Enable pulse 1+2, triangle, noise |
| `APU_STATUS_DISABLE_ALL` | %00000000 | |
| `APU_FRAME_COUNTER_5STEP_NOIRQ` | %11000000 | 5-step mode + IRQ inhibit |

**OAM sprite attributes:**

| Constant | Value | Notes |
|---|---|---|
| `OAM_SPRITE_STRIDE` | $04 | |
| `OAM_FIELD_Y` | $00 | |
| `OAM_FIELD_TILE` | $01 | |
| `OAM_FIELD_ATTRIBS` | $02 | |
| `OAM_FIELD_X` | $03 | |
| `OAM_ATTR_PRIORITY` | %00100000 | Behind-background bit |
| `OAM_ATTR_FLIP_H` | %01000000 | Horizontal flip |
| `OAM_ATTR_FLIP_V` | %10000000 | Vertical flip |

<a id="structured-field-offsets"></a>
## Structured Field Offsets and Overlays

Once a pointer corridor is proven to address a structured record, define
record field offsets and sweep the whole corridor instead of replacing one
literal at a time. Proof normally comes from pointer setup plus repeated
indirect access (`LDY #$NN` / `LDA|STA [ptr],Y`) or from an existing
shaped record family. Replace raw `LDY #$NN` offsets with `*_FIELD_*`
constants, replace residual raw indirect operands with the pointer
symbol, and comment byte-saving `INY` field walks with the field reached
after each meaningful increment. These comments preserve structure that the
operand-free instruction cannot express. Keep the pass shape-oriented: cover all
slots/records/status rows/sprite strips that share the same layout, but
do not force field names onto unrelated byte streams, PPU payloads, or
opaque descriptor indexes.
<a id="fixed-point-naming"></a>
## Fixed-Point Naming

Fixed-point and split-byte math naming follows the same rules as
[State and Action Constants](#state-action-constants) and
[Label Math](#label-math): name the semantic quantity, preserve `Lo`/`Hi`
or signed/unsigned role only when code uses those halves independently,
and prefer derived expressions over duplicated numeric scale factors.

<a id="state-action-constants"></a>
## State and Action Constants

Use named symbols for semantics; keep literals for opaque payload bytes.

### Core rules

1. **Replace semantic immediates with symbols.**
   - Good candidates:
     - sentinel values (`INDEX_INVALID`, blank tile ids)
     - enum/state values (`ACTOR_STATE_*`, `ACTOR_ACTION_*`)
     - gameplay thresholds/cooldowns (`BONUS_CATCH_TARGET_MAX`, frame timers)
     - loop/count bounds tied to ownership (`*_COUNT`)

2. **Keep literals when bytes are packed format payload unless fully decoded.**
   - If a byte belongs to script/token/packet content and semantics are uncertain, keep literal and document format nearby.

3. **Prefer expressions over duplicated constants.**
   - For bounds derived from table sizes, prefer `TableEnd-TableStart` style expressions over repeated numeric literals.

4. **If semantics are inferred, mark it.**
   - Mark the uncertain semantic claim once at the declaration or nearest owning
     block when a reader needs the caveat. Do not append `; inferred:` to every
     use. If the uncertainty is not locally important, record the evidence gap
     in `WORKING_NOTES.md` instead.

5. **Never substitute by numeric equality alone.**
   - A constant with the same byte value is not interchangeable across domains.
   - Before replacing `#$NN` with an existing symbol, verify the producer/consumer variable and subsystem match.
   - Example anti-pattern: replacing gameplay counters or PPU fields with audio trigger constants just because both equal `$02/$20`.
   - If no domain-correct symbol exists, create one in the owning subsystem instead of reusing an unrelated symbol.
6. **Address-as-Constant Red Flag (Critical).**
   - Do not use address labels as immediate constants (`LDA #Label`) unless the *address itself* is the intended data (e.g. pointer arithmetic).
   - If a math/physics constant happens to match a RAM address (e.g. `$A8` velocity vs `$00A8` variable), define a separate `PHYSICS_*` constant.
   - Never use a `RAM_*` or `ZP_*` symbol in an immediate (`#`) operand to represent a magnitude or coordinate value.
   - Treat `#ZP_*` and `#RAM_*` as suspicious by default.
     - Allowed only when the numeric address value itself is intentionally the data.
     - Otherwise introduce a semantic constant and use that instead.
     - `project-process-check` is expected to fail on suspicious `#ZP_*` / `#RAM_*` immediates.

### Detailed constantization rules

- **Hardware shadow handling:** Before closing the current corridor batch, ensure all `LDA ZP_Ppu*Shadow` / `AND|ORA|EOR #$NN` / `STA PPUCTRL|PPUMASK` paths touched by the corridor use named bitmask constants with correct domain prefixes (`PPUCTRL_*`, `PPUMASK_*`). Add intent comments for non-obvious masks. See [Hardware Constants](#hardware-constants) for the canonical name list.
- **Math constants:** Once the corridor proves the owning RAM/ZP field and the arithmetic role (motion/physics/collision/scoring math), name the math immediates in the same batch. Use subsystem-prefixed constants (`BALL_MOTION_*`, `SCORE_*`). Only replace immediates in executable logic, not packed data payload bytes. Do not stage a dedicated repository-wide math-constant pass.
- **OAM shadow addressing:** Derive OAM page from NMI DMA setup (`STA OAMDMA`), not convention. Define `RAM_OamShadowBase`, `OAM_PAGE_HI .EQU >RAM_OamShadowBase`, and canonical field/stride constants (`OAM_FIELD_Y/TILE/ATTRIBS/X`, `OAM_SPRITE_STRIDE`). OAM byte-lane roles are fixed: `0/4/8/C`=Y, `1/5/9/D`=tile, `2/6/A/E`=attribs, `3/7/B/F`=X. Replace raw `$02xx` accesses with `RAM_OamShadowBase+OAM_FIELD_*` expressions.
- **Base-derived page constants:** Derive page/high-byte constants from base symbols (`FOO_PAGE_HI .EQU >RAM_FooBase`). Do not duplicate standalone page literals.
- **Stride-indexed table formatting:** When consumer code indexes by fixed stride (`ASL`/multiply, `Table,Y`/`Table+1,Y`), format the table as one `.DB` line per record. Add `Record format:` and `Index:` comments.
- **Constantization workflow:** Magic immediates are overloaded; frequency-first planning is required. Audit existing constant gaps before defining new ones. Use line-targeted perl scripts for overloaded values; account for EQU insertion line drift. Prioritize immediates by confidence tier within the current corridor, not across a prescribed multi-pass project sequence. Define complementary constant pairs together. Audit label-embedded hex suffixes.
- **Constant-KPI exceptions:** Do not suppress intentional unsymbolized literals with inline asm comments. Record them in `docs/reverse_engineering/inventory/constant_magic_allowlist.csv` as structured `(label, mnemonic, immediate, reason)` rows, and keep the file pruned to the small set of literals that are clearer raw than symbolized.
- **Readability-first constantization:** Constantization must improve understanding, not just reduce KPI. Prioritize physics thresholds, state enums, mode flags, hardware masks. Avoid low-value index aliasing (`FOO_INDEX_04` when `#4` is obvious). Keep literal indices when clearer. Reject passes dominated by mechanical index aliases.
- **Constant name maturity:** When closing the current corridor, check the constants the corridor introduced or renamed for raw-hex leakage in symbol names. Prefer role-oriented over value-oriented names. Keep strict domain boundaries. Accept address-coded names only when address identity is the meaning. Project-wide residual searches for hex-suffixed `.EQU` names belong to [QUALITY_REVIEW.md#stale-placeholder-audit](QUALITY_REVIEW.md#stale-placeholder-audit), not to per-corridor passes.
- **Dual-purpose state bytes:** When a byte appears in unrelated paths, prefer neutral/base names. Do not force single-owner names on cross-domain bytes. Track ambiguity in `unknowns.md`.
- **Indexed input-state bases:** Use a `...Base` suffix for indexed pad state arrays (`ZP_PadHeldBase`). Document stride/index assumptions.
- **Shared queue/base symbolization:** Symbolize high-fanout queue/index RAM early (`..._WRITE_IDX`, `..._BASE`). This is a readability multiplier across many routines.
- **Paired-array symbolization:** Symbolize coupled fields together (`..._X_BASE`/`..._Y_BASE`, `..._MIN_*`/`..._MAX_*`). Replace callsites for both in the same batch.
- **PPU packet integrity** and **PPU packet window normalization** live with the packet-stream format spec in
  [DATA_RECOVERY.md#ppu-packet-streams](DATA_RECOVERY.md#ppu-packet-streams).

For the **Pointer-byte load sweep** (raw immediate pairs forming pointers in
executable code), see
[DATA_RECOVERY.md#computed-pointer-recovery](DATA_RECOVERY.md#computed-pointer-recovery).

### Packed-state promotion
Introduce mask/flag constants early. Replace threshold literals. Keep
lane aliases explicit. Promote only fields with repeated transition
evidence.

### Init-loop trap

When a routine streams data from a table into a slot via an indexed
copy, the X register increments across **all** slot bytes. The hex
literals written near the loop's tail
(e.g. `LDA #5 / STA Slot,X / LDA #8 / STA Slot,X`) are NOT state-byte
writes unless X has been reset to the state offset. Always re-derive
X at every store before claiming a value's role.
<a id="label-math"></a>
## Label Math for Pointers, Lengths, Counts, and Offsets

### Counter and length expressions

Prefer label math derived from the data's shape over hardcoded counter
or length literals:

- `#(TableEnd-TableStart-1)` for reverse loops (descending counter to 0)
- `#(TableEnd-TableStart)` for forward loops (count of bytes)
- `#((COUNT*STRIDE)-1)` for packed records iterated in reverse
- `#(End-Start)` for byte counts, `#((End-Start)/STRIDE)` for record counts
Pair these with explicit `...End` labels on the consumed blob — see
[DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination)
for the *when* and the data-recovery hazards (packet-payload guard,
parity-preserved counter bugs, re-verify-after-rewrite).

### Indirect addressing literal sweep
After symbolization, replace hardcoded `JMP [$NNNN]`, `[$NN],Y` etc. with
symbolic pointer names (`JMP [ZP_PtrWorkLo]`). Keep numeric operands
only when unresolved.

<a id="ram-symbolization"></a>
## RAM and ZP Symbolization (Naming and Structure)

RAM/ZP naming evidence, overlay restraint, and symbol-family conventions
live in [Naming Conventions](#naming-conventions). Prioritization and
queue mechanics live in
[PASS_WORKFLOW.md#raw-ram-prioritization](PASS_WORKFLOW.md#raw-ram-prioritization)
and [PASS_WORKFLOW.md#raw-ram-queue](PASS_WORKFLOW.md#raw-ram-queue).

<a id="tail-call-annotations"></a>
## Tail-Call and Parity-Preserved Redundant-Instruction Annotations

### Tail-call preservation

`JSR Target` immediately followed by `RTS` is a parity-preserved
tail-call pattern. Do not rewrite to `JMP Target` when binary
equivalence is required. Add a concise inline note at the call site:

```
JSR Target          ; tail-call candidate; could use `JMP` when ROM parity is not required
RTS
```

### Compact unconditional branches

When a conditional branch is deliberately used as a compact unconditional
branch because the latest local flag-setting instruction proves the
condition, keep the branch and annotate it `; always`. Do not call it
redundant or kept for ROM parity: an in-range branch is the optimal two-byte
transfer, while `JMP` costs one extra byte.

```
DEX
BNE @@copyPayload
BEQ @@nextPacket ; always
```

Use only when no intervening instruction mutates the relevant flag; branch
instructions themselves do not change flags. Otherwise improve the structure
or write a specific invariant comment.

### Redundant instructions retained for parity

When an instruction is provably redundant — the register or memory
write is overwritten before any consumer reads it (including flag
consumers, since loads and most ALU ops update N/Z); a load duplicates
a previous load whose register *and* N/Z outputs no intervening
consumer relies on; a flag is set or cleared and then overwritten
before any consumer of that flag — keep it exactly as the ROM has it
and add a one-line comment naming the redundancy and that it is
preserved for parity:

```
LDA #$00          ; redundant — preserved for parity (overwritten before the next read)
```
Do not delete or reorder these instructions when refactoring the
surrounding routine; parity preservation overrides cleanup. The
adjacent rules for parity-sensitive `JMP` trampolines and
`$+N`/`$-N` relative branch literals live at
[#naming-conventions](#naming-conventions).

The bug-comment requirement for parity-preserved oddities lives at
[DOCUMENTATION.md#parity-bug-comments](DOCUMENTATION.md#parity-bug-comments);
the symbolic-expression encoding for parity-preserved buggy values lives
at [DATA_RECOVERY.md#hardcoded-length-elimination](DATA_RECOVERY.md#hardcoded-length-elimination).

<a id="nop-and-padding-representation"></a>
### NOP and Padding Representation

Every `NOP` in an executable region must be classified when the surrounding
routine is audited or before any static-exhaustion claim:

- **timing pad** — needed or plausibly needed for scanline, split-scroll,
  controller, audio, or other cycle-sensitive behavior;
- **path pad** — equalizes or preserves a parity-sensitive control-flow path;
- **unreachable padding** — intentionally skipped bytes retained for ROM
  identity;
- **redundant instruction** — removable only in non-parity work.

Render executable `$EA` bytes as `NOP`, not `.DB $EA`, unless the bytes are
truly data, an overlapping encoding, or another format consumer reads them as
bytes. If a `JMP` or branch exists only to skip preserved padding, comment the
transfer instruction so the reader understands why the apparently redundant
control flow remains:

```asm
JMP @@next          ; skips preserved padding bytes.
    NOP            ; unreachable padding bytes preserved for parity.
    NOP
@@next:
```

Terminal or inter-table fill bytes (`$FF`, `$00`, etc.) should be commented as
unused padding only when the adjacent stream/table format proves the bytes sit
outside the consumed extent. Do not label payload bytes as padding merely
because they repeat a fill-like value.
