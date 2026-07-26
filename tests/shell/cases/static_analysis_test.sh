#!/usr/bin/env bash
# Tests scripts/static_analysis.py: the assembled-listing CFG/liveness scanner.
# Focused on the two calibration properties: a caller-initialised index is not a
# confirmed bug (only a wrong-register typo is), and the bit-7 rewrite is only
# suggested when both A and Z are dead after the branch.

STATIC_ANALYSIS="${REPO_ROOT}/scripts/static_analysis.py"

_write_static_analysis_fixture() {
  cat > "$1" <<'ASM'
.ORG $8000
PPUSTATUS  .EQU $2002
SrcTable   .EQU $0300
DstBuffer  .EQU $0200
InputByte  .EQU $0010
Flag       .EQU $0011
Flag2      .EQU $0012
Out1       .EQU $0013
Out2       .EQU $0014
ZP_StateA  .EQU $0015
ZP_StateB  .EQU $0016
ZP_State2  .EQU $0017
ZP_State3  .EQU $0018

; Confirmed overrun: wrong-register init (LDX where LDY was needed).
ConfirmedOverrun:
    LDX #$00
@@loop:
    LDA SrcTable,Y
    STA DstBuffer,Y
    INY
    CPY #$10
    BNE @@loop
    RTS

; Call-contract: X is an input register the caller sets via TAX before the call.
CallerSetsIndex:
    LDA InputByte
    TAX
    JSR ContractLoop
    RTS
ContractLoop:
    LDA SrcTable,X
    STA DstBuffer,X
    INX
    CPX #$08
    BNE ContractLoop
    RTS

; bit-7 where A is dead on every path (each redefines A before RTS) but Z is
; live: the fall-through's BEQ observes the AND's Z. An A-only check would wrongly
; suggest the rewrite; requiring Z dead too must exclude it.
Bit7Zlive:
    LDA Flag
    AND #$80
    BNE b7z_t1
    BEQ b7z_t2
    LDA #$00
    STA Out1
    RTS
b7z_t1:
    LDA #$01
    STA Out2
    RTS
b7z_t2:
    LDA #$02
    STA Out1
    RTS

; bit-7 with A and Z redefined on both paths -> safe rewrite.
Bit7Safe:
    LDA Flag2
    AND #$80
    BNE b7s_hit
    LDA #$03
    STA Out2
    RTS
b7s_hit:
    LDA #$04
    STA Out1
    RTS

; bit-7 on a hardware register: the idiomatic PPUSTATUS vblank wait. Bit 7 is
; fixed by the PPU, so it is a clean win (no layout risk, no comment needed).
VblankWait:
    LDA PPUSTATUS
    AND #$80
    BNE VblankWait
    LDA #$00
    STA Out2
    RTS

; Reload whose LD_ is a branch target: another flow JMPs in with a different A,
; so ZP_StateA is not necessarily in A on entry -- the reload is not redundant
; and must be omitted even though the CFG cannot see the absolute JMP edge.
StoreThenLabeledReload:
    STA ZP_StateA
LabeledReloadTarget:
    LDA ZP_StateA
    JMP UseStateA
JumpsIntoLabeledReload:
    LDA #$07
    JMP LabeledReloadTarget
UseStateA:
    STA Out1
    RTS

; Plain reload: the LD_ is unlabeled (reachable only by fall-through), so A still
; holds the stored value -- a valid (lower-confidence) reload candidate.
PlainReload:
    LDA InputByte
    STA ZP_StateB
    LDA ZP_StateB
    BEQ pr_done
    STA Out2
pr_done:
    RTS

; Reload whose STORE is a branch target: the BNE path arrives with N/Z set by LDX,
; not by A, so the reload's LDA is needed to set Z for the BEQ. Not redundant,
; even though the reload's LD_ is itself unlabeled.
ReloadStoreIsTarget:
    LDX Flag
    BNE rst_store
    LDA InputByte
rst_store:
    STA ZP_State2
    LDA ZP_State2
    BEQ rst_done
    STA Out1
rst_done:
    RTS

; Wrong-register store: a dead LDY #0 before a STA is the fingerprint of an
; LDA #0 typo -- the STA writes the stale A ($07), not 0. Y is redefined below so
; the LDY #0 is genuinely dead.
WrongRegStore:
    LDA #$07
    LDY #0
    STA ZP_StateA
    LDY #1
    STY ZP_StateB
    RTS

; Mirror case: a dead LDA #imm before a STX -- the immediate goes into A but the
; store reads X, so #imm is discarded (either LDX #imm or STA was meant). A is
; redefined below so the LDA #$09 is genuinely dead.
WrongRegStore2:
    LDX InputByte
    LDA #$09
    STX ZP_State3
    LDA #0
    STA Out1
    RTS

; Control: a dead LDY #imm that is NOT immediately before a store stays a plain
; dead instruction, not a wrong-register finding.
DeadLdyControl:
    LDY #$05
    LDY #$06
    STY ZP_StateA
    RTS

; Shift/carry confusion: CLC before an accumulator ASL. ASL shifts 0 into bit 0,
; not the carry, so the CLC is dead and the shift was likely meant to be ROL.
CarryClcShift:
    LDA Flag2
    CLC
    ASL
    STA Out1
    RTS

; A carry-set (CMP) whose carry is discarded by a later accumulator ASL.
CarryCmpShift:
    LDA Flag2
    CMP #6
    LDA InputByte
    ASL
    STA Out2
    RTS

; Control: SEC before SBC -- the SBC genuinely consumes the carry, so this is not
; a shift/carry confusion and must not be flagged.
CarryUsedControl:
    SEC
    LDA Flag2
    SBC InputByte
    STA Out1
    RTS
ASM
}

test_static_analysis_separates_confirmed_bug_from_input_contract() {
  local asm="${NESREV_TEST_TMPDIR}/sa_calib.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_calib.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
bugs = {b["routine"]: b for b in json.load(open(sys.argv[1]))["bugs"]}
co = bugs.get("ConfirmedOverrun")
if not co or co["confidence"] != "high" or not co["typo"]:
    raise SystemExit(f"wrong-register overrun must be confirmed/high with a typo: {co}")
cl = bugs.get("ContractLoop")
if not cl or cl["confidence"] != "review":
    raise SystemExit(f"caller-initialised index must be a review candidate, not a bug: {cl}")
if cl["typo"] is not None:
    raise SystemExit("input-contract loop must not report a typo")
if cl["n_callers"] < 1 or cl["n_callers_set"] != cl["n_callers"]:
    raise SystemExit(f"every caller sets the index (contract satisfied): {cl}")
PY
}

test_static_analysis_bit7_requires_a_and_z_dead() {
  local asm="${NESREV_TEST_TMPDIR}/sa_bit7.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_bit7.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
bit7_preds = [r["pred"] for r in d["bit7"]]
excl_kinds = [r.get("kind") for r in d["excluded"]]
# The Z-live case (Bit7Zlive, `LDA Flag`) must be excluded, never suggested.
if "LDA Flag" in bit7_preds:
    raise SystemExit("bit-7 with Z live after the branch must not be suggested")
if not any(k == "bit-7 mask" for k in excl_kinds):
    raise SystemExit("bit-7 mask with Z live after the branch must be excluded")
# The A/Z-dead case (Bit7Safe, `LDA Flag2`) must be suggested.
if "LDA Flag2" not in bit7_preds:
    raise SystemExit("the A/Z-dead bit-7 case should be suggested")
PY
}

test_static_analysis_bit7_hardware_vs_software() {
  local asm="${NESREV_TEST_TMPDIR}/sa_hw.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_hw.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
b7 = json.load(open(sys.argv[1]))["bit7"]
hw = [r for r in b7 if "PPUSTATUS" in r["pred"]]
sw = [r for r in b7 if "PPUSTATUS" not in r["pred"]]
# A PPUSTATUS bit-7 test is a hardware/idiomatic clean win (bit 7 = vblank).
if not hw or not all(r["hw"] and r["ppustatus"] for r in hw):
    raise SystemExit(f"PPUSTATUS bit-7 must be tagged hardware/idiomatic: {hw}")
# A RAM software-flag bit-7 test must not be tagged hardware.
if not sw or any(r["hw"] for r in sw):
    raise SystemExit(f"a software-flag bit-7 must not be tagged hardware: {sw}")
PY
}

test_static_analysis_reload_skips_labeled_target() {
  local asm="${NESREV_TEST_TMPDIR}/sa_reload.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_reload.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
stores = [r["store"] for r in json.load(open(sys.argv[1]))["reload"]]
# The reload whose LD_ is a labeled branch target (other flows JMP in) must be
# omitted -- it is redundant only if A holds the value on *every* incoming path.
if any("ZP_StateA" in s for s in stores):
    raise SystemExit(f"reload at a labeled branch target must be omitted: {stores}")
# The plain unlabeled reload (sole fall-through) must still be a candidate.
if not any("ZP_StateB" in s for s in stores):
    raise SystemExit(f"a sole-fall-through reload should be a candidate: {stores}")
# A reload whose STORE is a branch target must be omitted -- an incoming flow may
# set N/Z from another instruction, so the reload's LD_ is needed for the flags.
if any("ZP_State2" in s for s in stores):
    raise SystemExit(f"reload whose store is a branch target must be omitted: {stores}")
PY
}

test_static_analysis_flags_wrong_register_store() {
  local asm="${NESREV_TEST_TMPDIR}/sa_wrongreg.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_wrongreg.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
wr = d["wrongreg"]
# Dead LDY #0 before STA: immediate into Y, store reads A -> LDA #0 (or STY) meant.
ldy = [r for r in wr if r["dead"] == "LDY #0"]
if not ldy or ldy[0]["r1"] != "Y" or ldy[0]["r2"] != "A" or ldy[0]["fix_load"] != "LDA #0":
    raise SystemExit(f"dead LDY #0 before a STA must be a wrong-register finding: {wr}")
# Mirror: dead LDA #imm before STX: immediate into A, store reads X.
lda = [r for r in wr if r["dead"] == "LDA #$09"]
if not lda or lda[0]["r1"] != "A" or lda[0]["r2"] != "X" or lda[0]["fix_load"] != "LDX #$09":
    raise SystemExit(f"dead LDA #imm before a STX must be a wrong-register finding: {wr}")
# A dead LDY not before a store stays a plain dead instruction.
if any(r["dead"] == "LDY #$05" for r in wr):
    raise SystemExit("a dead LDY not before a store must not be a wrong-register finding")
if "LDY #$05" not in [r["src"] for r in d["dead"]]:
    raise SystemExit(f"the control dead LDY should remain in dead: {[r['src'] for r in d['dead']]}")
PY
}

test_static_analysis_flags_shift_carry_confusion() {
  local asm="${NESREV_TEST_TMPDIR}/sa_carry.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_carry.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
cs = json.load(open(sys.argv[1]))["carryshift"]
setters = [(r["setter"], r["intended"]) for r in cs]
# CLC before an accumulator ASL is a shift/carry confusion; ROL was likely meant.
if ("CLC", "ROL") not in setters:
    raise SystemExit(f"CLC before an accumulator ASL must be flagged (ROL): {setters}")
# A CMP whose carry a later ASL discards is flagged too.
if not any(s == "CMP #6" for s, _ in setters):
    raise SystemExit(f"a CMP whose carry a later ASL discards must be flagged: {setters}")
# A carry-set genuinely consumed (SEC before SBC) must NOT be flagged.
if any(s == "SEC" for s, _ in setters):
    raise SystemExit("a SEC whose carry SBC consumes must not be flagged")
PY
}
