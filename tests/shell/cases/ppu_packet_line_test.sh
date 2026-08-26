#!/usr/bin/env bash
# Tests one-packet-per-line validation for explicitly declared PPU streams.

CHECK="${REPO_ROOT}/scripts/ppu_packet_line_check.py"

test_ppu_packet_line_accepts_literal_repeat_and_terminator_lines() {
  local asm="${NESREV_TEST_TMPDIR}/good.asm"
  cat > "${asm}" <<'EOF'
PPU_PACKET_REPEAT .EQU %01000000
; Format: zero-terminated PPU packets [address hi, address lo, control, payload].
GoodPpuPacketStream:
.DB $20,$00,$03,$11,$22,$33
.DB $23,$C0,(PPU_PACKET_REPEAT|$20),$AA
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "declared_streams=1 line_layout_findings=0" "${out}" \
    "canonical literal and repeat packets must pass"
}

test_ppu_packet_line_rejects_two_packets_joined_on_one_line() {
  local asm="${NESREV_TEST_TMPDIR}/joined.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
JoinedPpuPacketStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "line_layout_findings=1" "${out}" \
    "parity-invisible joined packet lines must be reported"
  assert_match "requires 4 byte\(s\).*found 8" "${out}" \
    "the diagnostic must state the decoded boundary"
}

test_ppu_packet_line_rejects_packet_split_across_lines() {
  local asm="${NESREV_TEST_TMPDIR}/split.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU palette packets.
SplitPpuPacketStream:
.DB $3F,$00,$03,$11
.DB $22,$33
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "line_layout_findings=2" "${out}" \
    "both halves of a split packet must be review-visible"
}

test_ppu_packet_line_requires_standalone_terminator() {
  local asm="${NESREV_TEST_TMPDIR}/terminator.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
TerminatorPpuPacketStream:
.DB $00,$FF
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "standalone .DB .00" "${out}" \
    "a terminator sharing its line must be rejected"
}

test_ppu_packet_line_requires_terminator() {
  local asm="${NESREV_TEST_TMPDIR}/unterminated.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
UnterminatedPpuPacketStream:
.DB $20,$00,$01,$11
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "has no standalone terminator" "${out}" \
    "a declared zero-terminated stream must contain its terminator"
}

test_ppu_packet_line_allows_sanctioned_trailing_bytes() {
  local asm="${NESREV_TEST_TMPDIR}/trailing.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
TrailingPpuPacketStream:
.DB $20,$00,$01,$11
.DB $00
.DB $EA,$EA ; trailing bytes after stream terminator (parity-preserved)
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "line_layout_findings=0" "${out}" \
    "the playbook-sanctioned trailing-byte annotation must pass"
}

test_ppu_packet_line_allows_declared_shared_suffix_entry() {
  local asm="${NESREV_TEST_TMPDIR}/suffix.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
PrimaryPpuPacketStream:
.DB $20,$00,$01,$11
; Format: zero-terminated PPU packets; also a suffix entry for the prior stream.
SuffixPpuPacketStream:
.DB $20,$01,$01,$22
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "declared_streams=2 line_layout_findings=0" "${out}" \
    "a stream may fall through a separately declared suffix entry"
}

test_ppu_packet_line_does_not_treat_unrelated_stream_as_suffix() {
  local asm="${NESREV_TEST_TMPDIR}/unrelated_stream.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
FirstPpuPacketStream:
.DB $20,$00,$01,$11
; Format: zero-terminated PPU packets.
SecondPpuPacketStream:
.DB $20,$01,$01,$22
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "declared_streams=2 line_layout_findings=1" "${out}" \
    "an unrelated next stream must not hide a missing terminator"
  assert_match "FirstPpuPacketStream.*has no standalone terminator" "${out}" \
    "the missing terminator must stay attributed to the first stream"
}

test_ppu_packet_line_ignores_unannotated_or_differently_named_data() {
  local asm="${NESREV_TEST_TMPDIR}/scope.asm"
  cat > "${asm}" <<'EOF'
UnannotatedPpuPacketStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
; Format: zero-terminated PPU packets.
NotAStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "declared_streams=0 line_layout_findings=0" "${out}" \
    "both the format declaration and stream-name contract are required"
}

test_ppu_packet_line_excludes_address_high_flag_variant() {
  local asm="${NESREV_TEST_TMPDIR}/variant.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets; flag bits are packed in the address high byte.
VariantPpuPacketStream:
.DB $60,$00,$05,$11,$22,$33,$44,$55
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "declared_streams=0 line_layout_findings=0" "${out}" \
    "the canonical control-byte decoder must exclude the address-high flag variant"
}

test_ppu_packet_line_reports_unresolvable_expression() {
  local asm="${NESREV_TEST_TMPDIR}/unknown.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
UnknownPpuPacketStream:
.DB $20,$00,UNKNOWN_CONTROL,$11
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>&1)"
  assert_match "cannot resolve byte expression" "${out}" \
    "an unsupported expression must not silently make the stream green"
}

test_ppu_packet_line_strict_mode_proves_bad_direction() {
  local asm="${NESREV_TEST_TMPDIR}/strict.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
BadPpuPacketStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
.DB $00
EOF
  assert_exit 68 python3 "${CHECK}" "${asm}" --strict
}

test_ppu_packet_line_report_mode_is_advisory() {
  local asm="${NESREV_TEST_TMPDIR}/report.asm"
  cat > "${asm}" <<'EOF'
; Format: zero-terminated PPU packets.
BadPpuPacketStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
.DB $00
EOF
  assert_exit 0 python3 "${CHECK}" "${asm}"
}

test_ppu_packet_line_rejects_bad_cli_and_read_errors() {
  local asm="${NESREV_TEST_TMPDIR}/cli.asm"
  printf 'Reset:\n    RTS\n' > "${asm}"
  assert_exit 64 python3 "${CHECK}" "${asm}" --stict
  assert_exit 64 python3 "${CHECK}" "${asm}" --strict=1
  assert_exit 65 python3 "${CHECK}" "${NESREV_TEST_TMPDIR}/missing.asm"
  printf '\377' > "${asm}"
  assert_exit 65 python3 "${CHECK}" "${asm}"
}

test_ppu_packet_line_is_opt_in_process_advisory() {
  local process_check
  process_check="$(cat "${REPO_ROOT}/scripts/project_process_check.sh")"
  assert_match 'PROOF_DEBT_REQUIRED.*==.*1' "${process_check}" \
    "legacy projects must stay outside the new advisory"
  assert_match 'ppu_packet_line_check.py' "${process_check}" \
    "opted-in process checks must surface the packet-line signal"
  if printf '%s' "${process_check}" | grep -q 'ppu_packet_line_check.py.*--strict'; then
    fail "corpus calibration does not support making the shared check strict"
  fi
}
