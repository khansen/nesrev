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
