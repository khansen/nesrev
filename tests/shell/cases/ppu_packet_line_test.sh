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
  assert_match "line_layout_findings=1" "${out}" \
    "a split packet must fail without interpreting its payload as another header"
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

test_ppu_packet_line_accepts_payload_field_inside_shared_suffix() {
  local asm="${NESREV_TEST_TMPDIR}/suffix_field.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
Parent:
.DB $20,$00,$01,$11
; Format: zero-terminated PPU packet stream suffix.
Suffix:
.DB $20,$01,$02,$22
; Format: 1-byte payload field inside Suffix.
Payload:
.DB $33
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'declared_streams=2 line_layout_findings=0' "${out}"
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

test_ppu_packet_line_requires_format_not_label_spelling() {
  local asm="${NESREV_TEST_TMPDIR}/scope.asm"
  cat > "${asm}" <<'EOF'
UnannotatedPpuPacketStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
; Format: zero-terminated PPU packets.
NotAStream:
.DB $20,$00,$01,$11,$20,$01,$01,$22
.DB $00
EOF
  local out
  out="$(python3 "${CHECK}" "${asm}" 2>/dev/null)"
  assert_match "declared_streams=1 line_layout_findings=1" "${out}" \
    "a declared stream must be checked regardless of its label spelling"
  assert_match 'format_candidates=1 checked_streams=1 skipped_formats=0' "${out}"
  assert_exit 68 python3 "${CHECK}" "${asm}" --strict
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
  assert_match 'format_candidates=1 checked_streams=0 skipped_formats=1' "${out}"
}

test_ppu_packet_line_accepts_ppu_hi_field_name_without_assuming_flags() {
  local asm="${NESREV_TEST_TMPDIR}/canonical_fields.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream [ppu_hi, ppu_lo, control, payload].
BootPalette:
.DB $3F,$00,$01,$11
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'declared_streams=1 line_layout_findings=0' "${out}"
  assert_match 'format_candidates=1 checked_streams=1 skipped_formats=0' "${out}"
}

test_ppu_packet_line_handles_named_fields_inside_packets() {
  local asm="${NESREV_TEST_TMPDIR}/fields.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
HudTemplate:
.DB $22,$4C,$04,$19,$11
; Format: 2-byte digit field inside HudTemplate.
TopDigits:
.DB $24,$24
.DB $23,$41,$03,$19
; Format: 2-byte digit field inside HudTemplate.
BottomDigits:
.DB $24,$24
.DB $00
HudTemplateEnd:
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'declared_streams=1 line_layout_findings=0' "${out}"
}

test_ppu_packet_line_payload_field_must_complete_its_packet() {
  local asm="${NESREV_TEST_TMPDIR}/short_field.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
HudTemplate:
.DB $22,$4C,$04,$19,$11
; Format: 2-byte digit field inside HudTemplate.
Digits:
.DB $24
.DB $00
ASM
  assert_exit 68 python3 "${CHECK}" "${asm}" --strict
}

test_ppu_packet_line_unrelated_field_cannot_extend_packet() {
  local asm="${NESREV_TEST_TMPDIR}/other_field.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
HudTemplate:
.DB $22,$4C,$04,$19,$11
; Format: 2-byte digit field inside OtherTemplate.
Digits:
.DB $24,$24
.DB $00
ASM
  assert_exit 68 python3 "${CHECK}" "${asm}" --strict
}

test_ppu_packet_line_reports_unsupported_formats_and_zero_coverage() {
  local asm="${NESREV_TEST_TMPDIR}/unsupported.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packets [ppu_hi|flags, ppu_lo, length, payload].
AddressFlagTemplate:
.DB $60,$00,$03,$11
.DB $00
; Format: two zero-terminated PPU packet streams.
PlayerTemplates:
.DB $00
OtherPlayerTemplate:
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'format_candidates=2 checked_streams=0 skipped_formats=2' "${out}"
  assert_match 'NOT CHECKED:.*AddressFlagTemplate' "${out}"
  assert_match 'NOT CHECKED:.*PlayerTemplates' "${out}"
  assert_match 'NOT CHECKED: no canonical PPU packet streams checked' "${out}"
}

test_ppu_packet_line_skips_grouped_declaration_after_canonical_prefix() {
  local asm="${NESREV_TEST_TMPDIR}/grouped_hidden.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet streams (PLAYER 1 + PLAYER 2 attract labels).
PlayerTemplates:
.DB $20,$00,$01,$11
.DB $00
OtherPlayerTemplate:
.DB $20,$01,$02,$22
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'format_candidates=1 checked_streams=0 skipped_formats=1' "${out}"
  assert_match 'NOT CHECKED:.*PlayerTemplates' "${out}"
}

test_ppu_packet_line_format_is_not_limited_to_seven_comment_lines() {
  local asm="${NESREV_TEST_TMPDIR}/long_header.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
; Header line 2.
; Header line 3.
; Header line 4.
; Header line 5.
; Header line 6.
; Header line 7.
; Header line 8.
; Consumer: Reader.
Palette:
.DB $3F,$00,$01,$11
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'declared_streams=1 line_layout_findings=0' "${out}"
}

test_ppu_packet_line_accepts_consumer_before_format() {
  local asm="${NESREV_TEST_TMPDIR}/reordered_header.asm"
  cat > "${asm}" <<'ASM'
; Consumer: Reader.
; Format: zero-terminated PPU packet stream.
Palette:
.DB $3F,$00,$01,$11
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'format_candidates=1 checked_streams=1 skipped_formats=0' "${out}"
}

test_ppu_packet_line_supports_inline_body_and_same_address_alias() {
  local asm="${NESREV_TEST_TMPDIR}/aliases.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
Palette:
  PaletteAlias: .DB $3F,$00,$01,$11
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'declared_streams=1 line_layout_findings=0' "${out}"
}

test_ppu_packet_line_accepts_annotated_same_address_alias() {
  local asm="${NESREV_TEST_TMPDIR}/annotated_alias.asm"
  cat > "${asm}" <<'ASM'
; Format: zero-terminated PPU packet stream.
Parent:
; Format: zero-terminated PPU packet stream.
Alias:
.DB $20,$00,$02,$11
; Format: 1-byte field inside Alias.
Field:
.DB $22
.DB $00
ASM
  local out
  out="$(python3 "${CHECK}" "${asm}" --strict 2>&1)"
  assert_match 'declared_streams=2 line_layout_findings=0' "${out}"
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

test_ppu_packet_line_is_universal_process_advisory() {
  local process_check
  process_check="$(cat "${REPO_ROOT}/scripts/project_process_check.sh")"
  assert_match 'ppu_packet_line_check.py' "${process_check}" \
    "every project's process check must surface the packet-line signal"
  assert_not_match 'PROOF_DEBT_REQUIRED' "${process_check}"
  if printf '%s' "${process_check}" | grep -q 'ppu_packet_line_check.py.*--strict'; then
    fail "corpus calibration does not support making the shared check strict"
  fi
}
