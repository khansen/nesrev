#!/usr/bin/env bash
# Tests for mechanically checkable `; Used by:` xref validation.

USED_BY_CHECK="${REPO_ROOT}/scripts/used_by_xref_check.py"

_make_used_by_docs_project() {
  local slug="$1"
  local root="projects/${slug}"

  cleanup_project "${slug}"
  mkdir -p \
    "${root}/asm" \
    "${root}/build" \
    "${root}/reference" \
    "${root}/docs/reverse_engineering/inventory"

  cat > "${root}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="${root}/asm/${slug}.asm"
REF_NES="${root}/reference/${slug}.nes"
DOC_ROOT="${root}/docs/reverse_engineering"
SYSTEMS_DOC="${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
NESREV_RECOVERY_STATUS="legacy"
OUT_BIN="${root}/build/${slug}.o"
EOF

  cat > "${root}/asm/${slug}.asm" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: FakeMissingConsumer.
DataTable:
.DB $01
ASM

  : > "${root}/reference/${slug}.nes"
  : > "${root}/docs/reverse_engineering/${slug}_DX_Systems.md"
  : > "${root}/docs/reverse_engineering/WARNING_BASELINE.txt"
  : > "${root}/docs/reverse_engineering/ONBOARDING.md"
  : > "${root}/docs/reverse_engineering/QUICK_REFERENCE.md"
  printf 'old_name,new_name,reason,confidence,pass_id\n' \
    > "${root}/docs/reverse_engineering/inventory/renames.csv"
}

test_used_by_xref_check_accepts_direct_data_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_direct.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader.
DataTable:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" "${asm}" >/dev/null
}

test_used_by_xref_check_rejects_stale_direct_consumer() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_stale.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS
OtherReader:
  RTS

; Format: one byte.
; Used by: OtherReader.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" --strict "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "stale Used by comment must fail"
  assert_match "OtherReader" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_reports_owner_mismatch_advisory_without_strict() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_advisory.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS
OtherReader:
  RTS

; Format: one byte.
; Used by: OtherReader.
DataTable:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"

  assert_match "Used by hard-error scan passed" "$(cat "${NESREV_TEST_TMPDIR}/used_by.out")"
  assert_match "ADVISORY: Used by xref" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
  assert_match "OtherReader" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_reports_missing_xasm_cleanly() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_missing_xasm.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader.
DataTable:
.DB $01
ASM

  set +e
  PATH=/usr/bin:/bin python3 "${USED_BY_CHECK}" "${asm}" \
    >"${NESREV_TEST_TMPDIR}/used_by.out" \
    2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "66" "missing xasm must return a stable error code"
  assert_match "xasm not found" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_splits_and_case_insensitively() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_upper_and.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: Reader AND FakeMissingConsumer.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "uppercase AND must still split Used by consumer symbols"
  assert_match "FakeMissingConsumer" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_accepts_consumer_through_pointer_table() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_indirect.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA PtrTable
  RTS

; Format: pointer table.
; Used by: Reader.
PtrTable:
.DW Payload

; Format: payload bytes.
; Used by: Reader through PtrTable.
Payload:
.DB $01
ASM

  python3 "${USED_BY_CHECK}" "${asm}" >/dev/null
}

test_used_by_xref_check_through_producer_advisory_unless_strict() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_indirect_stale.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  LDA PtrTable
  RTS

; Format: pointer table.
; Used by: Reader.
PtrTable:
.DW OtherPayload

; Format: payload bytes.
; Used by: Reader through PtrTable.
Payload:
.DB $01

OtherPayload:
.DB $02
ASM

  # Non-strict: an unverifiable through/via dispatcher (indirect reach) is
  # advisory, not a hard failure -- the xref cannot follow the indirection.
  set +e
  python3 "${USED_BY_CHECK}" "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "through-producer must be advisory (not hard) without --strict"
  assert_match "ADVISORY" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
  assert_match "PtrTable does not reference Payload" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"

  # --strict opt-in still enforces it as a hard failure.
  set +e
  python3 "${USED_BY_CHECK}" --strict "${asm}" >"${NESREV_TEST_TMPDIR}/used_by_s.out" 2>"${NESREV_TEST_TMPDIR}/used_by_s.err"
  local rc_strict=$?
  set -e
  assert_eq "${rc_strict}" "2" "through-producer must hard-fail under --strict"
  assert_match "PtrTable does not reference Payload" "$(cat "${NESREV_TEST_TMPDIR}/used_by_s.err")"
}

test_used_by_xref_check_rejects_unresolved_consumer_label() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_unresolved_label.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
L1234:
  LDA DataTable
  RTS

; Format: one byte.
; Used by: L1234.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "Used by comments must not cite unresolved LXXXX labels"
  assert_match "unresolved consumer label L1234" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_used_by_xref_check_rejects_prg_banking_without_consumer_symbol() {
  local asm="${NESREV_TEST_TMPDIR}/used_by_banking.asm"
  cat > "${asm}" <<'ASM'
.ORG $C000
Reader:
  RTS

; Format: one byte.
; Used by: selected through MMC1 PRG banking.
DataTable:
.DB $01
ASM

  set +e
  python3 "${USED_BY_CHECK}" "${asm}" >"${NESREV_TEST_TMPDIR}/used_by.out" 2>"${NESREV_TEST_TMPDIR}/used_by.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "generic MMC1 banking Used by comment must fail"
  assert_match "PRG banking" "$(cat "${NESREV_TEST_TMPDIR}/used_by.err")"
}

test_project_docs_check_hard_fails_unknown_used_by_consumer() {
  local slug; slug="$(unique_slug used_by_docs_fail)"
  trap "cleanup_project ${slug}" EXIT
  _make_used_by_docs_project "${slug}"

  set +e
  make project-docs-check "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/docs.out" 2>"${NESREV_TEST_TMPDIR}/docs.err"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "project-docs-check must hard-fail stale Used by comments"
  assert_match "FakeMissingConsumer" "$(cat "${NESREV_TEST_TMPDIR}/docs.err")"
}
