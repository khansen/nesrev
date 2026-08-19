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
