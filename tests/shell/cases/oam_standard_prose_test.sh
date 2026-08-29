#!/usr/bin/env bash
# Tests the project-facing canonical OAM prose advisory.

CHECK="${REPO_ROOT}/scripts/oam_standard_prose_check.py"

_write_oam_fixture() {
  local root="$1"
  mkdir -p "${root}/asm" \
    "${root}/docs/reverse_engineering/reviews" \
    "${root}/docs/reverse_engineering/inventory"
  cat > "${root}/asm/game.asm" <<'EOF'
; Format: one standard record [Y, tile, attributes, X].
DirectOamTemplate:
    .DB $10,$20,$00,$30
; Format: one extended record [shadow offset, Y, tile, attributes, X].
ExtendedOamTemplate:
    .DB $08,$10,$20,$00,$30
; Format: one suffixed record [Y, tile, attributes, X, flags].
SuffixedOamTemplate:
    .DB $10,$20,$00,$30,$40
TupleText:
    .DB "[Y, tile, attributes, X]"
EOF
  cat > "${root}/docs/reverse_engineering/MEMORY_MAP.md" <<'EOF'
Each direct OAM tuple is `(y, tile, attr, x)`.
EOF
  cat > "${root}/docs/reverse_engineering/reviews/pass-2.md" <<'EOF'
Historical review preserved the old `[Y, tile, attributes, X]` wording.
EOF
  cat > "${root}/docs/reverse_engineering/inventory/current_pass_plan.md" <<'EOF'
Generated evidence quotes `[Y, tile, attributes, X]`.
EOF
}

test_oam_standard_prose_reports_live_asm_and_markdown() {
  local root="${NESREV_TEST_TMPDIR}/project"
  _write_oam_fixture "${root}"
  local out
  out="$(python3 "${CHECK}" "${root}/asm/game.asm" "${root}" 2>&1)"
  assert_match 'candidates=2' "${out}" \
    "live ASM comments and Markdown must both be checked"
  assert_match 'game\.asm:1' "${out}"
  assert_match 'MEMORY_MAP\.md:1' "${out}"
}

test_oam_standard_prose_excludes_provenance_and_extended_shapes() {
  local root="${NESREV_TEST_TMPDIR}/project"
  _write_oam_fixture "${root}"
  local out
  out="$(python3 "${CHECK}" "${root}/asm/game.asm" "${root}" 2>&1)"
  if printf '%s' "${out}" | grep -qE \
    'pass-2\.md|current_pass_plan\.md|shadow offset|X, flags|TupleText|\.DB "\[Y, tile'; then
    fail "review archives, inventory snapshots, extended shapes, and non-comment ASM text must stay outside the advisory"
  fi
}

test_oam_standard_prose_accepts_canonical_reference() {
  local root="${NESREV_TEST_TMPDIR}/clean"
  mkdir -p "${root}/asm" "${root}/docs/reverse_engineering"
  cat > "${root}/asm/game.asm" <<'EOF'
; Format: two standard OAM sprite records (OAM_FIELD_*).
Template:
    .DB $10,$20,$00,$30,$10,$21,$00,$38
EOF
  cat > "${root}/docs/reverse_engineering/MEMORY_MAP.md" <<'EOF'
Uses the canonical OAM record layout from ASM_STYLE.md#hardware-constants.
EOF
  local out
  out="$(python3 "${CHECK}" "${root}/asm/game.asm" "${root}" 2>/dev/null)"
  assert_match 'candidates=0' "${out}"
}

test_oam_standard_prose_strict_mode_proves_bad_direction() {
  local root="${NESREV_TEST_TMPDIR}/project"
  _write_oam_fixture "${root}"
  assert_exit 69 python3 "${CHECK}" "${root}/asm/game.asm" "${root}" --strict
  assert_exit 0 python3 "${CHECK}" "${root}/asm/game.asm" "${root}"
}

test_oam_standard_prose_rejects_bad_cli_and_missing_inputs() {
  local root="${NESREV_TEST_TMPDIR}/project"
  mkdir -p "${root}"
  assert_exit 64 python3 "${CHECK}"
  assert_exit 64 python3 "${CHECK}" missing.asm "${root}" --stict
  assert_exit 65 python3 "${CHECK}" missing.asm "${root}"
}

test_oam_standard_prose_is_universal_process_advisory() {
  local process_check
  process_check="$(<"${REPO_ROOT}/scripts/project_process_check.sh")"
  assert_match 'oam_standard_prose_check\.py' "${process_check}" \
    "every project's process checks must surface repeated canonical OAM prose"
  assert_not_match 'PROOF_DEBT_REQUIRED' "${process_check}"
  if printf '%s' "${process_check}" | grep -q 'oam_standard_prose_check.py.*--strict'; then
    fail "OAM prose candidates must remain advisory until the project is migrated"
  fi
}
