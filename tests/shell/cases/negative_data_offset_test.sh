#!/usr/bin/env bash
# Tests the small negative indexed data-label boundary signal.

CHECK="${REPO_ROOT}/scripts/negative_data_offset_check.py"

test_negative_data_offset_reports_direct_data_label_offset() {
  local asm="${NESREV_TEST_TMPDIR}/candidate.asm"
  cat > "${asm}" <<'EOF'
PacketTail:
    .DB $10,$20,$30,$40
Reader:
    LDA PacketTail-3,X
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match 'candidates=1' "${out}"
  assert_match 'PacketTail-3,X uses an indexed base 3 byte\(s\) before data label PacketTail' "${out}" \
    "diagnostic must identify the source boundary and offset"
}

test_negative_data_offset_accepts_alias_and_indexed_indirect_forms() {
  local asm="${NESREV_TEST_TMPDIR}/aliases.asm"
  cat > "${asm}" <<'EOF'
PacketAlias:
PacketBytes: .DB $10,$20,$30,$40
Reader:
    LDA [PacketAlias-$03],Y
    LDA (PacketBytes-%10,X)
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match 'candidates=2' "${out}" \
    "consecutive data aliases and both indexed enclosure forms must be covered"
}

test_negative_data_offset_ignores_non_data_and_non_candidate_shapes() {
  local asm="${NESREV_TEST_TMPDIR}/clean.asm"
  cat > "${asm}" <<'EOF'
RAM_Buffer .EQU $0200
CodeTarget:
    RTS
DataTable:
    .DB $10,$20,$30,$40
Reader:
    LDA RAM_Buffer-1,X
    LDA CodeTarget-1,X
    LDA MissingLabel-1,X
    LDA DataTable+1,X
    LDA DataTable-1
    LDA DataTable-17,X
    RTS
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match 'candidates=0' "${out}" \
    "RAM, code, unknown, positive, unindexed, and non-small offsets stay out"
}

test_negative_data_offset_ignores_comments_and_data_expressions() {
  local asm="${NESREV_TEST_TMPDIR}/comments.asm"
  cat > "${asm}" <<'EOF'
DataTable:
    .DB $10,$20,$30
PointerBytes:
    .DB <DataTable-1, >DataTable-1
Reader:
    ; LDA DataTable-1,X
    LDA DataTable,X ; DataTable-1,X is historical prose
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match 'candidates=0' "${out}" \
    "comments and data expressions are not executable indexed operands"
}

test_negative_data_offset_strict_mode_proves_bad_direction() {
  local asm="${NESREV_TEST_TMPDIR}/strict.asm"
  cat > "${asm}" <<'EOF'
DataTable: .BYTE 1,2,3
Reader:
    CMP DataTable-1,Y
EOF
  assert_exit 68 python3 "${CHECK}" "${asm}" --strict
}

test_negative_data_offset_report_mode_is_advisory() {
  local asm="${NESREV_TEST_TMPDIR}/report.asm"
  cat > "${asm}" <<'EOF'
DataTable: .DW $1234
Reader:
    LDA DataTable-1,Y
EOF
  assert_exit 0 python3 "${CHECK}" "${asm}"
}

test_negative_data_offset_rejects_bad_cli_and_read_errors() {
  local bad="${NESREV_TEST_TMPDIR}/bad.asm"
  printf '\377' > "${bad}"
  assert_exit 64 python3 "${CHECK}"
  assert_exit 64 python3 "${CHECK}" "${bad}" --stict
  assert_exit 65 python3 "${CHECK}" "${NESREV_TEST_TMPDIR}/missing.asm"
  assert_exit 65 python3 "${CHECK}" "${bad}"
}

test_negative_data_offset_is_opt_in_process_advisory() {
  local process_check proof_block outside_proof_block
  process_check="$(<"${REPO_ROOT}/scripts/project_process_check.sh")"
  proof_block="$(
    sed -n '/^if \[\[ "${PROOF_DEBT_REQUIRED}" == "1" \]\]; then$/,/^fi$/p' \
      "${REPO_ROOT}/scripts/project_process_check.sh"
  )"
  outside_proof_block="$(
    sed '/^if \[\[ "${PROOF_DEBT_REQUIRED}" == "1" \]\]; then$/,/^fi$/d' \
      "${REPO_ROOT}/scripts/project_process_check.sh"
  )"
  assert_match 'negative_data_offset_check\.py' "${process_check}" \
    "new-project process checks must surface the boundary signal"
  assert_match 'negative_data_offset_check\.py' "${proof_block}" \
    "legacy projects must stay outside the new advisory"
  if printf '%s' "${outside_proof_block}" | grep -q 'negative_data_offset_check.py'; then
    fail "boundary scan must not run outside the proof-debt opt-in block"
  fi
  if printf '%s' "${process_check}" | grep -q 'negative_data_offset_check.py.*--strict'; then
    fail "boundary candidates must remain advisory until individually reviewed"
  fi
}
