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
ZP_State4  .EQU $0019
END_SENTINEL .EQU $00

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

; bit-7 on $4016 (controller read): a *side-effect* read, but bit 7 is data / open
; bus, NOT a hardware-fixed status bit -- so it must not be a clean win (hw=False).
; This distinguishes the side-effect-read set from the fixed-bit-7 set. A/Z are
; dead after the branch so it is a genuine bit-7 candidate, not excluded.
Bit7ControllerReg:
    LDA $4016
    AND #$80
    BNE b7c_set
    LDA #$00
    STA Out1
    RTS
b7c_set:
    LDA #$01
    STA Out1
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

; Narrowing check: an unrelated inline comment sits on the STORE, but the flagged
; reload's LD_ has none. Only the flagged instruction (the reload) is inspected,
; so this finding must be annotated=False -- the store comment must not mask it.
ContextCommentedReload:
    LDA InputByte
    STA ZP_State3 ; unrelated prose on the store, not about the reload
    LDA ZP_State3
    BEQ ccr_done
    STA Out1
ccr_done:
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

; A dead instruction that already carries an inline comment -> annotated=True,
; so a source-annotation sweep can skip it (it is already documented).
AnnotatedDead:
    LDY #$07 ; redundant load kept for ROM parity
    LDY #$08
    STY ZP_StateB
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

; LSR variant: CLC before an accumulator LSR. LSR vacates bit 7, so ROR (bit 7)
; was likely meant -- the reported bit must be 7, not 0.
CarryClcLsr:
    LDA Flag2
    CLC
    LSR
    STA Out2
    RTS

; Redundant compare-to-zero with a *literal* #0 -- a clean drop (named=false).
; (The CLC redefines carry before RTS so the compare's carry is dead.)
Cmp0Literal:
    LDA Flag2
    CMP #0
    BNE c0l_join
    LDA #1
    STA Out1
c0l_join:
    CLC
    RTS

; Redundant compare-to-zero with a *named* zero-valued sentinel -- a trade-off
; (named=true): only redundant while END_SENTINEL == 0, and the name documents
; what the branch tests.
Cmp0Named:
    LDA Flag2
    CMP #END_SENTINEL
    BNE c0n_join
    LDA #1
    STA Out2
c0n_join:
    CLC
    RTS

; A reload whose stored value comes from a JSR return -- removability is non-local
; (it depends on the subroutine's flag-return contract), so the finding names the
; subroutine.
ReloadFromJsr:
    JSR SomeBcdSub
    STA ZP_State4
    LDA ZP_State4
    BEQ rfj_done
    STA Out1
rfj_done:
    RTS
SomeBcdSub:
    LDA #0
    RTS

; Plain tail-call candidate with no inline comment.
TailCallPlain:
    JSR SomeBcdSub
    RTS

; Already annotated tail-call candidate.
TailCallAnnotated:
    JSR SomeBcdSub ; tail-call candidate; could use `JMP` when ROM parity is not required
    RTS

; Not a tail call: there is an intervening instruction.
TailCallInterveningControl:
    JSR SomeBcdSub
    LDA #0
    RTS

; A labeled RTS still reports as a tail-call shape, but the finding records that
; the return site has its own label.
TailCallLabeledRts:
    JSR SomeBcdSub
SharedTailReturn:
    RTS
JumpToSharedTailReturn:
    JMP SharedTailReturn
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
# A $4016 read has side effects, but its bit 7 is NOT hardware-fixed (data/open
# bus), so it must be a software-flag trade-off, never a fixed-bit-7 clean win.
ctrl = [r for r in b7 if "$4016" in r["pred"]]
if not ctrl or any(r["hw"] for r in ctrl):
    raise SystemExit(f"a $4016 side-effect read must not be a fixed-bit-7 clean win: {ctrl}")
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
# CLC before an accumulator ASL -> ROL, folding carry into bit 0.
asl = [r for r in cs if r["setter"] == "CLC" and r["shift"] == "ASL"]
if not asl or asl[0]["intended"] != "ROL" or asl[0]["bit"] != "0":
    raise SystemExit(f"CLC before ASL must be flagged as ROL / bit 0: {cs}")
# CLC before an accumulator LSR -> ROR, folding carry into bit 7 (not bit 0).
lsr = [r for r in cs if r["setter"] == "CLC" and r["shift"] == "LSR"]
if not lsr or lsr[0]["intended"] != "ROR" or lsr[0]["bit"] != "7":
    raise SystemExit(f"CLC before LSR must be flagged as ROR / bit 7: {cs}")
# A CMP whose carry a later ASL discards is flagged too.
if not any(r["setter"] == "CMP #6" for r in cs):
    raise SystemExit(f"a CMP whose carry a later ASL discards must be flagged: {cs}")
# A carry-set genuinely consumed (SEC before SBC) must NOT be flagged.
if any(r["setter"] == "SEC" for r in cs):
    raise SystemExit("a SEC whose carry SBC consumes must not be flagged")
PY
}

test_static_analysis_compare_zero_named_vs_literal() {
  local asm="${NESREV_TEST_TMPDIR}/sa_cmp0.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_cmp0.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
cmp0 = json.load(open(sys.argv[1]))["cmp0"]
# A literal #0 compare is a clean drop (named=false).
lit = [r for r in cmp0 if r["cmp"] == "CMP #0"]
if not lit or lit[0]["named"]:
    raise SystemExit(f"a literal #0 compare must be a clean drop (named=false): {cmp0}")
# A named zero-valued sentinel is a trade-off (named=true).
nm = [r for r in cmp0 if "END_SENTINEL" in r["cmp"]]
if not nm or not nm[0]["named"]:
    raise SystemExit(f"a named zero-sentinel compare must be a trade-off (named=true): {cmp0}")
PY
}

test_static_analysis_reload_flags_jsr_contract() {
  local asm="${NESREV_TEST_TMPDIR}/sa_reljsr.asm"
  local out="${NESREV_TEST_TMPDIR}/sa_reljsr.json"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${out}" >/dev/null
  python3 - "${out}" <<'PY'
import json, sys
rl = json.load(open(sys.argv[1]))["reload"]
# A locally-produced reload (value from a nearby LDA) is a local optimization.
plain = [r for r in rl if "ZP_StateB" in r["store"]]
if not plain or plain[0]["jsr"] is not None:
    raise SystemExit(f"a locally-produced reload must have jsr=None: {rl}")
# A reload whose value came from a JSR names the subroutine (non-local contract).
viajsr = [r for r in rl if "ZP_State4" in r["store"]]
if not viajsr or viajsr[0]["jsr"] != "SomeBcdSub":
    raise SystemExit(f"a JSR-produced reload must name the subroutine: {rl}")
PY
}

test_static_analysis_flags_tail_call_candidates() {
  local asm="${NESREV_TEST_TMPDIR}/sa_tail.asm"
  local json="${NESREV_TEST_TMPDIR}/sa_tail.json"
  local doc="${NESREV_TEST_TMPDIR}/sa_tail.md"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${json}" --doc-out "${doc}" \
    --title Fixture --commit test --date 2026-07-26 >/dev/null
  python3 - "${json}" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
tc = d["tailcall"]
by = {r["routine"]: r for r in tc}
expected = {"CallerSetsIndex", "TailCallPlain", "TailCallAnnotated", "TailCallLabeledRts"}
if set(by) != expected:
    raise SystemExit(f"expected tail-call routines {expected}, got {set(by)}: {tc}")
if by["TailCallPlain"]["annotated"]:
    raise SystemExit(f"plain tail call should be unannotated: {tc}")
if not by["TailCallAnnotated"]["annotated"]:
    raise SystemExit(f"commented tail call should be annotated: {tc}")
if not by["TailCallLabeledRts"]["rts_labeled"]:
    raise SystemExit(f"labeled RTS tail call should carry rts_labeled: {tc}")
if "TailCallInterveningControl" in by:
    raise SystemExit("intervening instruction must not be a tail-call candidate")
if by["TailCallPlain"]["target"] != "SomeBcdSub":
    raise SystemExit(f"tail-call target should be parsed from assembled JSR source: {tc}")
PY
  grep -q "Tail-call candidates" "${doc}" \
    || { echo "doc missing tail-call section" >&2; return 1; }
  grep -Fq "**E:**" "${doc}" \
    || { echo "doc missing Category E annotation worklist" >&2; return 1; }
}

test_static_analysis_flags_already_annotated_findings() {
  local asm="${NESREV_TEST_TMPDIR}/sa_annot.asm"
  local json="${NESREV_TEST_TMPDIR}/sa_annot.json"
  local doc="${NESREV_TEST_TMPDIR}/sa_annot.md"
  _write_static_analysis_fixture "${asm}"
  python3 "${STATIC_ANALYSIS}" "${asm}" --json "${json}" --doc-out "${doc}" \
    --title Fixture --commit test --date 2026-07-26 >/dev/null
  python3 - "${json}" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
dead = d["dead"]
if any("annotated" not in r for r in dead):
    raise SystemExit("every dead finding must expose an 'annotated' flag")
# a dead instruction carrying an inline comment is already annotated.
ann = [r for r in dead if "#$07" in r["src"]]
if not ann or not ann[0]["annotated"]:
    raise SystemExit(f"a commented dead instruction must be annotated=True: {dead}")
# a dead instruction with no inline comment is not annotated (the sweep worklist).
un = [r for r in dead if "#$05" in r["src"]]
if not un or un[0]["annotated"]:
    raise SystemExit(f"an un-commented dead instruction must be annotated=False: {dead}")
# Narrowing: only the FLAGGED instruction's line is inspected. A reload whose
# store carries an unrelated comment (but whose reload LD_ does not) must NOT be
# masked -- annotated=False, so it stays in the worklist.
ctx = [r for r in d["reload"] if "unrelated prose" in r["store"]]
if not ctx or ctx[0]["annotated"]:
    raise SystemExit(f"a context comment on the store must not mask the reload: {d['reload']}")
PY
  # the doc must foreground the worklist and describe the observable, not overclaim.
  grep -q "Source-annotation status" "${doc}" \
    || { echo "doc missing annotation-status section" >&2; return 1; }
  grep -q "have no inline comment at the flagged instruction" "${doc}" \
    || { echo "doc missing un-annotated count" >&2; return 1; }
  ! grep -Fq '`LD_`' "${doc}" \
    || { echo "doc contains symbol-looking pseudo mnemonic LD_" >&2; return 1; }
  python3 - "${doc}" <<'PY'
from pathlib import Path
import sys

data = Path(sys.argv[1]).read_bytes()
if not data.endswith(b"\n") or data.endswith(b"\n\n"):
    raise SystemExit("doc-out must end with exactly one newline")
PY
}
