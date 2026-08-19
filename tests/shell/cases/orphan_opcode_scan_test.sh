#!/usr/bin/env bash
# Tests the advisory orphan-opcode scanner used during hidden-code recovery.

ORPHAN_SCAN="${REPO_ROOT}/scripts/orphan_opcode_scan.py"

_write_banked_orphan_scan_asm() {
  cat > "$1" <<'ASM'
.ORG $8000
L08000:
.DB $FF,$FF,$FF,$FF

.ORG $8010
L08010:
.DB $11,$22,$A9,$00,$85,$13,$E6,$11,$60,$FF

.ORG $8040
L08040:
.DB $20,$00,$80,$60
ASM
}

_write_banked_orphan_scan_warnings() {
  cat > "$1" <<'TXT'
SymbolName|rationale
L08010|REVIEW REQUIRED: intake auto-seed; replace with symbol-specific rationale
TXT
}

_write_banked_orphan_scan_codeentries() {
  cat > "$1" <<'TXT'
# bank|addr
0|$8012
TXT
}

_write_banked_orphan_scan_dispositions() {
  cat > "$1" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
L08010,queued_static_pass,,,,,,blocked_unknown_format,review scanner candidate
CSV
}

_write_semantic_orphan_scan_asm() {
  cat > "$1" <<'ASM'
.ORG $C000
EarlyTable:
.DB $FF,$FF,$FF,$FF

LDA #$00
RTS

LateTable:
.DB <EarlyTable,>EarlyTable,$A9,$01,$85,$10,$60
ASM
}

_write_semantic_orphan_scan_warnings() {
  cat > "$1" <<'TXT'
SymbolName|rationale
LateTable|REVIEW REQUIRED: intake auto-seed; replace with symbol-specific rationale
TXT
}

_write_semantic_orphan_scan_codeentries() {
  cat > "$1" <<'TXT'
$C009
TXT
}

_write_semantic_orphan_scan_dispositions() {
  cat > "$1" <<'CSV'
label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes
LateTable,queued_static_pass,,,,,,blocked_unknown_format,review scanner candidate
CSV
}

test_orphan_opcode_scan_finds_table_tail_code_candidate() {
  local asm="${NESREV_TEST_TMPDIR}/fixture.asm"
  local warnings="${NESREV_TEST_TMPDIR}/WARNING_BASELINE.txt"
  local codeentries="${NESREV_TEST_TMPDIR}/codeentries.txt"
  local dispositions="${NESREV_TEST_TMPDIR}/data_blob_dispositions.csv"
  local out="${NESREV_TEST_TMPDIR}/scan.csv"
  _write_banked_orphan_scan_asm "${asm}"
  _write_banked_orphan_scan_warnings "${warnings}"
  _write_banked_orphan_scan_codeentries "${codeentries}"
  _write_banked_orphan_scan_dispositions "${dispositions}"

  python3 "${ORPHAN_SCAN}" \
    --asm "${asm}" \
    --mapper 1 \
    --warnings "${warnings}" \
    --codeentries "${codeentries}" \
    --data-blob-dispositions "${dispositions}" \
    --min-size 1 \
    --threshold 22 > "${out}"

  assert_match "span_label,candidate_label" "$(<"${out}")" "CSV header should identify span and candidate labels"
  assert_match "L08010,L08012,0,\\\$8012,2" "$(<"${out}")" "scanner should report code starts inside the DB span"
  assert_match "yes,,.*,queued_static_pass" "$(<"${out}")" "scanner should join codeentry and disposition context"
}

test_orphan_opcode_scan_uses_listing_addresses_after_code_and_symbolic_db() {
  local asm="${NESREV_TEST_TMPDIR}/semantic_fixture.asm"
  local warnings="${NESREV_TEST_TMPDIR}/semantic_WARNING_BASELINE.txt"
  local codeentries="${NESREV_TEST_TMPDIR}/semantic_codeentries.txt"
  local dispositions="${NESREV_TEST_TMPDIR}/semantic_data_blob_dispositions.csv"
  local out="${NESREV_TEST_TMPDIR}/semantic_scan.csv"
  _write_semantic_orphan_scan_asm "${asm}"
  _write_semantic_orphan_scan_warnings "${warnings}"
  _write_semantic_orphan_scan_codeentries "${codeentries}"
  _write_semantic_orphan_scan_dispositions "${dispositions}"

  python3 "${ORPHAN_SCAN}" \
    --asm "${asm}" \
    --mapper 0 \
    --warnings "${warnings}" \
    --codeentries "${codeentries}" \
    --data-blob-dispositions "${dispositions}" \
    --min-size 1 \
    --threshold 22 > "${out}"

  assert_match "LateTable,LC009,,\\\$C009,2" "$(<"${out}")" "scanner should keep CPU addresses after instruction records"
  assert_match "LateTable,LC009,,\\\$C009,2,.*yes,,.*,queued_static_pass" "$(<"${out}")" "scanner should join codeentry and disposition context for semantic labels"
  if grep -q "L0C009" "${out}"; then
    fail "NROM candidate labels must not gain a fabricated bank prefix"
  fi
}

test_project_hidden_code_scan_wrapper_writes_pass_inventory_csv() {
  local slug
  slug="$(unique_slug orphan_scan)"
  local rom="${NESREV_TEST_TMPDIR}/${slug}.nes"
  make_ines "${rom}" --prg 1 --chr 1
  scaffold_project "${slug}" "${rom}"
  mkdir -p "projects/${slug}/config/nesrev" "projects/${slug}/docs/reverse_engineering/inventory"
  _write_semantic_orphan_scan_asm "projects/${slug}/asm/${slug}.asm"
  _write_semantic_orphan_scan_warnings "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
  _write_semantic_orphan_scan_codeentries "projects/${slug}/config/nesrev/codeentries.txt"
  _write_semantic_orphan_scan_dispositions "projects/${slug}/docs/reverse_engineering/inventory/data_blob_dispositions.csv"
  printf 'NESREV_CODEENTRIES_FILE="projects/%s/config/nesrev/codeentries.txt"\n' "${slug}" >> "projects/${slug}/project.conf"

  MIN_SIZE=1 THRESHOLD=22 bash scripts/project_hidden_code_scan.sh "${slug}" > "${NESREV_TEST_TMPDIR}/wrapper.out"

  local out="projects/${slug}/docs/reverse_engineering/inventory/pass/orphan_opcode_candidates.csv"
  [[ -f "${out}" ]] || fail "wrapper did not write ${out}"
  assert_match "orphan-opcode candidates: [1-9][0-9]*" "$(<"${NESREV_TEST_TMPDIR}/wrapper.out")" "wrapper should print a nonzero candidate count"
  assert_match "LateTable,LC009,,\\\$C009,2" "$(<"${out}")" "wrapper CSV should include semantic-label candidate"
  if grep -q "L0C009" "${out}"; then
    fail "wrapper must pass mapper context so NROM labels stay unbanked"
  fi

  cleanup_project "${slug}"
}

test_project_hidden_code_scan_wrapper_allows_missing_reference_rom() {
  local slug
  slug="$(unique_slug orphan_scan_missing_ref)"
  local rom="${NESREV_TEST_TMPDIR}/${slug}.nes"
  make_ines "${rom}" --prg 1 --chr 1
  scaffold_project "${slug}" "${rom}"
  mkdir -p "projects/${slug}/config/nesrev" "projects/${slug}/docs/reverse_engineering/inventory"
  _write_semantic_orphan_scan_asm "projects/${slug}/asm/${slug}.asm"
  _write_semantic_orphan_scan_warnings "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
  _write_semantic_orphan_scan_codeentries "projects/${slug}/config/nesrev/codeentries.txt"
  _write_semantic_orphan_scan_dispositions "projects/${slug}/docs/reverse_engineering/inventory/data_blob_dispositions.csv"
  printf 'NESREV_CODEENTRIES_FILE="projects/%s/config/nesrev/codeentries.txt"\n' "${slug}" >> "projects/${slug}/project.conf"
  rm -f "projects/${slug}/reference/${slug}.nes"

  MIN_SIZE=1 THRESHOLD=22 bash scripts/project_hidden_code_scan.sh "${slug}" > "${NESREV_TEST_TMPDIR}/missing_ref_wrapper.out"

  local out="projects/${slug}/docs/reverse_engineering/inventory/pass/orphan_opcode_candidates.csv"
  [[ -f "${out}" ]] || fail "wrapper did not write ${out} without reference ROM"
  assert_match "orphan-opcode candidates: [1-9][0-9]*" "$(<"${NESREV_TEST_TMPDIR}/missing_ref_wrapper.out")" "wrapper should still print candidate count"
  assert_match "LateTable,LC009,,\\\$C009,2" "$(<"${out}")" "wrapper should scan without reference-ROM mapper context"

  cleanup_project "${slug}"
}

# Target-validation fixture. Three 16 KiB banks so bank-relative resolution is
# exercised: banks 0 and 1 are switched windows, bank 2 is the fixed bank.
# Bank 0 holds a real veneer at $8000; bank 1 holds data at the same address,
# so identical candidate bytes are executable in one bank and not the other.
_write_target_validation_asm() {
  python3 - "$1" <<'PY'
import sys

BANK = 0x4000
# Fixed-bank layout is deterministic: JMP occupies $C000-$C002 and the pointer
# word occupies $C003-$C004, so these two addresses are always interior bytes.
head = [
    "FIXED_MID_INSTR .EQU $C001",
    "FIXED_PTR_MID .EQU $C004",
]
bank0 = [
    ".ORG $8000",
    "VeneerBank0:",
    "    JMP VeneerBodyBank0",
    "VeneerBodyBank0:",
    "    RTS",
    "CandidateValidTargetBank0:",
    "    .DB $20,<VeneerBank0,>VeneerBank0,$60",
    "CandidateRamTargetBank0:",
    "    .DB $20,$00,$07,$60",
    "CandidateMidInstrTargetBank0:",
    "    .DB $4C,<FIXED_MID_INSTR,>FIXED_MID_INSTR",
    "CandidateMidDataTargetBank0:",
    "    .DB $4C,<FIXED_PTR_MID,>FIXED_PTR_MID",
]
bank0_bytes = 3 + 1 + 4 + 4 + 3 + 3
bank1 = [
    "DataWhereBank0HasVeneer:",
    "    .DB $FF,$FF,$FF,$FF",
    "CandidateCopiedBytesBank1:",
    "    .DB $20,<VeneerBank0,>VeneerBank0,$60",
]
bank1_bytes = 4 + 4
fixed = [
    "FixedEntry:",
    "    JMP FixedEntry",
    "FixedPtrTable:",
    "    .DW FixedEntry",
]
fixed_bytes = 3 + 2


def filler(label, count):
    lines = [f"{label}:"]
    while count > 0:
        chunk = min(count, 16)
        lines.append("    .DB " + ",".join(["$FF"] * chunk))
        count -= chunk
    return lines


lines = head + bank0 + filler("FillerBank0", BANK - bank0_bytes)
lines += [".ORG $8000"] + bank1 + filler("FillerBank1", BANK - bank1_bytes)
lines += [".ORG $C000"] + fixed + filler("FillerFixedBank", BANK - fixed_bytes)
open(sys.argv[1], "w", encoding="utf-8").write("\n".join(lines) + "\n")
PY
}

_write_nrom_mirror_target_validation_asm() {
  cat > "$1" <<'ASM'
.ORG $C000
MirrorTarget:
    RTS
CandidateMirrorTarget:
    .DB $20,$00,$80,$60
ASM
}

# Reads one column of the offset-0 row for a span, so assertions name the
# column instead of counting commas.
_orphan_scan_field() {
  python3 - "$1" "$2" "$3" <<'PY'
import csv
import sys

path, label, column = sys.argv[1], sys.argv[2], sys.argv[3]
with open(path, newline="", encoding="utf-8") as handle:
    for row in csv.DictReader(handle):
        if row["span_label"] == label and row["candidate_offset"] == "0":
            print(row[column])
            break
PY
}

test_orphan_opcode_scan_validates_nrom_16k_mirror_targets() {
  local asm="${NESREV_TEST_TMPDIR}/nrom_mirror_target.asm"
  local out="${NESREV_TEST_TMPDIR}/nrom_mirror_target.csv"
  _write_nrom_mirror_target_validation_asm "${asm}"

  python3 "${ORPHAN_SCAN}" \
    --asm "${asm}" \
    --mapper 0 \
    --min-size 1 \
    --threshold 10 \
    --all > "${out}"

  assert_eq "yes" "$(_orphan_scan_field "${out}" CandidateMirrorTarget target_valid)" \
    "16 KiB NROM should resolve the \$8000 mirror to the single PRG image"
  assert_eq "1/1" "$(_orphan_scan_field "${out}" CandidateMirrorTarget resolved_targets)" \
    "NROM mirror resolution should count as a validated target"
}

test_orphan_opcode_scan_validates_absolute_control_flow_targets() {
  local asm="${NESREV_TEST_TMPDIR}/target_validation.asm"
  local out="${NESREV_TEST_TMPDIR}/target_validation.csv"
  _write_target_validation_asm "${asm}"

  # --all so rejected runs are still emitted; the filtering behaviour has its
  # own test below.
  python3 "${ORPHAN_SCAN}" \
    --asm "${asm}" \
    --mapper 1 \
    --min-size 1 \
    --threshold 10 \
    --all > "${out}"

  # Positive control: the call resolves to an instruction start in the
  # candidate's own bank.
  assert_eq "yes" "$(_orphan_scan_field "${out}" CandidateValidTargetBank0 target_valid)" \
    "targets resolving to instruction starts should validate"
  assert_eq "1/1" "$(_orphan_scan_field "${out}" CandidateValidTargetBank0 resolved_targets)" \
    "resolved_targets should count validated targets"

  # Copied bytes: identical to the bank-0 candidate, but bank 1 holds data at
  # the called address. Byte identity proves provenance, not executability.
  assert_eq "no" "$(_orphan_scan_field "${out}" CandidateCopiedBytesBank1 target_valid)" \
    "a copied run whose target is data in its own bank must not validate"
  assert_match "data@b1" "$(_orphan_scan_field "${out}" CandidateCopiedBytesBank1 invalid_targets)" \
    "invalid_targets should name the resolved bank"

  # Jump into the middle of a fixed-bank instruction.
  assert_eq "no" "$(_orphan_scan_field "${out}" CandidateMidInstrTargetBank0 target_valid)" \
    "a jump into an instruction body must not validate"
  assert_match "mid-instr" "$(_orphan_scan_field "${out}" CandidateMidInstrTargetBank0 invalid_targets)" \
    "invalid_targets should report the mid-instruction landing"

  # Jump into a fixed-bank pointer word, the shape a decoded run takes when it
  # lands in inline-call payload or table bytes.
  assert_eq "no" "$(_orphan_scan_field "${out}" CandidateMidDataTargetBank0 target_valid)" \
    "a jump into pointer-word bytes must not validate"
  assert_match "mid-data" "$(_orphan_scan_field "${out}" CandidateMidDataTargetBank0 invalid_targets)" \
    "invalid_targets should report the mid-data landing"

  # RAM destinations stay unknown: copied ROM-to-RAM images legitimately call
  # their runtime addresses, and rejecting them would hide that pattern.
  assert_eq "unknown" "$(_orphan_scan_field "${out}" CandidateRamTargetBank0 target_valid)" \
    "an unresolvable RAM target must stay unknown rather than valid or invalid"
  assert_match "ram target" "$(_orphan_scan_field "${out}" CandidateRamTargetBank0 target_validation_notes)" \
    "notes should explain why the target was unresolved"
}

test_orphan_opcode_scan_invalid_targets_lose_strong_filtering() {
  local asm="${NESREV_TEST_TMPDIR}/target_validation_filter.asm"
  local out="${NESREV_TEST_TMPDIR}/target_validation_filter.csv"
  _write_target_validation_asm "${asm}"

  # Default filtering: a proven-invalid run must not qualify on score alone.
  python3 "${ORPHAN_SCAN}" \
    --asm "${asm}" \
    --mapper 1 \
    --min-size 1 \
    --threshold 10 > "${out}"

  if grep -q "^[0-9]*,CandidateMidInstrTargetBank0,.*,no," "${out}"; then
    fail "a target_valid=no run must not survive strong filtering"
  fi
  grep -q "CandidateValidTargetBank0" "${out}" \
    || fail "a validated run must still be reported"
  python3 "${ORPHAN_SCAN}" --asm "${asm}" --mapper 1 --min-size 1 --threshold 10 --all \
    | grep -q "CandidateMidInstrTargetBank0" \
    || fail "--all must still expose rejected runs for review"
}
