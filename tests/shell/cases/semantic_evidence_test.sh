#!/usr/bin/env bash
# Tests the reference-order and derived-constant semantic-evidence advisories.

CHECK="${REPO_ROOT}/scripts/semantic_evidence_check.py"

_empty_crosswalk() {
  local path="$1"
  cat > "${path}" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
EOF
}

test_semantic_evidence_reports_reference_order_without_code_citation() {
  local asm="${NESREV_TEST_TMPDIR}/order.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
RenderCivilianSlot:
    RTS
EOF
  cat > "${crosswalk}" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
| first civilian | `RenderCivilianSlot` | high confidence | The panel follows the instruction booklet order. |
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>&1)"
  assert_match "reference_order_without_code_citation=1" "${out}" \
    "a confidence claim based on booklet order must cite code"
  assert_match "first civilian" "${out}" \
    "the diagnostic must identify the crosswalk term"
}

test_semantic_evidence_accepts_reference_order_with_code_citation() {
  local asm="${NESREV_TEST_TMPDIR}/cited.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
RenderCivilianSlot:
    RTS
EOF
  cat > "${crosswalk}" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
| first civilian | `RenderCivilianSlot` | high confidence | `RenderCivilianSlot` selects the entry independently of the booklet order. |
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "reference_order_without_code_citation=0" "${out}" \
    "an evidence cell citing a live asm symbol must pass"
}

test_semantic_evidence_ignores_reference_only_row() {
  local asm="${NESREV_TEST_TMPDIR}/reference_only.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  printf 'Reset:\n    RTS\n' > "${asm}"
  cat > "${crosswalk}" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
| first civilian |  | reference-only | The instruction booklet lists this target first. |
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "reference_order_without_code_citation=0" "${out}" \
    "reference-only vocabulary is not a code-identity claim"
}

test_semantic_evidence_ignores_code_evidence_without_reference_ordering() {
  local asm="${NESREV_TEST_TMPDIR}/code_evidence.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  printf 'AdvanceRound:\n    RTS\n' > "${asm}"
  cat > "${crosswalk}" <<'EOF'
| Reference term / aliases | Asm symbol(s) | Mapping confidence | Evidence |
|---|---|---|---|
| round | `AdvanceRound` | high confidence | The counter transition selects the next round. |
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "reference_order_without_code_citation=0" "${out}" \
    "the narrow check must not demand boilerplate citations on every row"
}

test_semantic_evidence_reports_unanchored_derived_root() {
  local asm="${NESREV_TEST_TMPDIR}/unanchored.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
PANEL_ID_FIRST      .EQU 4
PANEL_ID_SECOND     .EQU PANEL_ID_FIRST+1
PANEL_ID_THIRD      .EQU PANEL_ID_SECOND+1
SelectPanel:
    CPY #PANEL_ID_SECOND
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>&1)"
  assert_match "unanchored_derived_constant_roots=1" "${out}" \
    "a numeric family root used only to derive the applied member must be reported"
  assert_match "PANEL_ID_FIRST" "${out}" \
    "the diagnostic must name the unanchored root"
}

test_semantic_evidence_accepts_derived_root_with_operand_use() {
  local asm="${NESREV_TEST_TMPDIR}/anchored.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
PANEL_ID_FIRST      .EQU 4
PANEL_ID_SECOND     .EQU PANEL_ID_FIRST+1
SelectPanel:
    CPY #PANEL_ID_FIRST
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "unanchored_derived_constant_roots=0" "${out}" \
    "a family root used by an instruction is anchored"
}

test_semantic_evidence_does_not_count_comment_as_operand_use() {
  local asm="${NESREV_TEST_TMPDIR}/comment.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
PANEL_ID_FIRST      .EQU 4
PANEL_ID_SECOND     .EQU PANEL_ID_FIRST+1
; PANEL_ID_FIRST is the presumed first entry.
SelectPanel:
    CPY #PANEL_ID_SECOND
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "unanchored_derived_constant_roots=1" "${out}" \
    "a prose mention must not masquerade as an operand anchor"
}

test_semantic_evidence_skips_unrelated_offset_constants() {
  local asm="${NESREV_TEST_TMPDIR}/unrelated.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
TILE_BASE           .EQU 4
SCREEN_LIMIT        .EQU TILE_BASE+1
Render:
    LDA #SCREEN_LIMIT
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "unanchored_derived_constant_roots=0" "${out}" \
    "unrelated names must not be coerced into one semantic family"
}

test_semantic_evidence_skips_non_offset_derivation() {
  local asm="${NESREV_TEST_TMPDIR}/mask.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
PPUCTRL_FLAG_NMI    .EQU %10000000
PPUCTRL_FLAG_MASK   .EQU ~PPUCTRL_FLAG_NMI
WriteControl:
    LDA #PPUCTRL_FLAG_MASK
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "unanchored_derived_constant_roots=0" "${out}" \
    "mask composition is outside the ordinal-offset signal"
}

test_semantic_evidence_skips_structural_count_index_math() {
  local asm="${NESREV_TEST_TMPDIR}/count.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
SPRITE_PIECE_COUNT       .EQU 4
SPRITE_PIECE_LAST_INDEX  .EQU SPRITE_PIECE_COUNT-1
Render:
    CPX #SPRITE_PIECE_LAST_INDEX
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  local out
  out="$(python3 "${CHECK}" "${asm}" "${crosswalk}" 2>/dev/null)"
  assert_match "unanchored_derived_constant_roots=0" "${out}" \
    "ordinary count-to-last-index math is structural, not an identity claim"
}

test_semantic_evidence_strict_mode_proves_bad_direction() {
  local asm="${NESREV_TEST_TMPDIR}/strict.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
ROUND_STATE_FIRST   .EQU 1
ROUND_STATE_SECOND  .EQU ROUND_STATE_FIRST+1
Run:
    CMP #ROUND_STATE_SECOND
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  assert_exit 68 python3 "${CHECK}" "${asm}" "${crosswalk}" --strict
}

test_semantic_evidence_report_mode_is_advisory() {
  local asm="${NESREV_TEST_TMPDIR}/report.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  cat > "${asm}" <<'EOF'
ROUND_STATE_FIRST   .EQU 1
ROUND_STATE_SECOND  .EQU ROUND_STATE_FIRST+1
Run:
    CMP #ROUND_STATE_SECOND
    RTS
EOF
  _empty_crosswalk "${crosswalk}"
  assert_exit 0 python3 "${CHECK}" "${asm}" "${crosswalk}"
}

test_semantic_evidence_rejects_bad_cli_and_read_errors() {
  local asm="${NESREV_TEST_TMPDIR}/cli.asm"
  local crosswalk="${NESREV_TEST_TMPDIR}/crosswalk.md"
  printf 'Reset:\n    RTS\n' > "${asm}"
  _empty_crosswalk "${crosswalk}"
  assert_exit 64 python3 "${CHECK}" "${asm}" "${crosswalk}" --stict
  assert_exit 64 python3 "${CHECK}" "${asm}" "${crosswalk}" --strict=1
  assert_exit 65 python3 "${CHECK}" "${NESREV_TEST_TMPDIR}/missing.asm" "${crosswalk}"
  printf '\377' > "${crosswalk}"
  assert_exit 65 python3 "${CHECK}" "${asm}" "${crosswalk}"
}

test_semantic_evidence_is_opt_in_process_advisory() {
  local process_check
  process_check="$(cat "${REPO_ROOT}/scripts/project_process_check.sh")"
  assert_match 'PROOF_DEBT_REQUIRED.*==.*1' "${process_check}" \
    "legacy projects must stay outside the new advisory"
  assert_match 'semantic_evidence_check.py' "${process_check}" \
    "opted-in process checks must surface the signal"
  if printf '%s' "${process_check}" | grep -q 'semantic_evidence_check.py.*--strict'; then
    fail "corpus calibration does not support making the shared check strict"
  fi
}
