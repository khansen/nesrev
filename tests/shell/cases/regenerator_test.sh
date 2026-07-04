#!/usr/bin/env bash
# Tests scripts/project_regenerate_asm.sh header and container validation.
# Each test scaffolds a throwaway project under projects/<slug>/, invokes the
# regenerator, and cleans up. Tests do not run the full assembler path; they
# stop at the header/container gate by asserting on the script's exit code
# and stderr message.

REGEN="${REPO_ROOT}/scripts/project_regenerate_asm.sh"

_run_regen() {
  # Echo the exit code on stdout so tests can assert on it independently of
  # the script's own output. Optional first args are env-var assignments
  # of the form KEY=value (handled by `env`).
  local slug="$1"; shift
  set +e
  if (( $# > 0 )); then
    env "$@" bash "${REGEN}" "${slug}" \
      >"${NESREV_TEST_TMPDIR}/regen.stdout" 2>"${NESREV_TEST_TMPDIR}/regen.stderr"
  else
    bash "${REGEN}" "${slug}" \
      >"${NESREV_TEST_TMPDIR}/regen.stdout" 2>"${NESREV_TEST_TMPDIR}/regen.stderr"
  fi
  local rc=$?
  set -e
  echo "${rc}"
}

_run_regen_from_dir() {
  local cwd="$1" slug="$2"; shift 2
  set +e
  if (( $# > 0 )); then
    (cd "${cwd}" && env "$@" bash "${REGEN}" "${slug}") \
      >"${NESREV_TEST_TMPDIR}/regen.stdout" 2>"${NESREV_TEST_TMPDIR}/regen.stderr"
  else
    (cd "${cwd}" && bash "${REGEN}" "${slug}") \
      >"${NESREV_TEST_TMPDIR}/regen.stdout" 2>"${NESREV_TEST_TMPDIR}/regen.stderr"
  fi
  local rc=$?
  set -e
  echo "${rc}"
}

test_accepts_compatible_nes2_header() {
  local slug; slug="$(unique_slug nes2)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --header-fmt 2
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "0" "compatible NES 2.0 NROM ROM must be accepted"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "compatible NES 2.0 ROM must produce a non-empty asm file"
}

test_rejects_nes2_extended_mapper() {
  local slug; slug="$(unique_slug nes2_mapper)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --header-fmt 2
  python3 -c '
import sys
p = sys.argv[1]
data = bytearray(open(p, "rb").read())
data[8] = 1
open(p, "wb").write(data)
' "${NESREV_TEST_TMPDIR}/rom.nes"
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject NES 2.0 mapper high bits"
  assert_match "mapper 256" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_rejects_nes2_extended_prg_size() {
  local slug; slug="$(unique_slug nes2_prg)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --header-fmt 2
  python3 -c '
import sys
p = sys.argv[1]
data = bytearray(open(p, "rb").read())
data[9] = 1
open(p, "wb").write(data)
' "${NESREV_TEST_TMPDIR}/rom.nes"
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject NES 2.0 PRG upper size bits"
  assert_match "PRG units=257" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_rejects_reserved_header_bits() {
  local slug; slug="$(unique_slug reserved)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --header-fmt 3
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject reserved header bits"
  assert_match "FLAGS7 bits\[2:3\]=3" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_rejects_wrong_mapper() {
  local slug; slug="$(unique_slug mapper)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --mapper 1
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject non-NROM mapper"
  assert_match "mapper 1" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_accepts_32kb_prg_rom() {
  local slug; slug="$(unique_slug prg32)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --prg 2
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "0" "regenerator should accept NROM-256 PRG=32 KB"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "NROM-256 ROM must produce a non-empty asm file"
  assert_match ".ORG \\\$8000" "$(head -5 "projects/${slug}/asm/${slug}.asm")"
}

test_project_common_derives_32kb_cpu_base() {
  local slug; slug="$(unique_slug prg32_base)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --prg 2
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local settings
  settings="$(bash -c '
set -euo pipefail
source scripts/project_common.sh
load_project_conf "$1"
printf "%s\n%s\n" "${XASM_AUDIT_ROM_RANGE}" "${XASM_COMPARE_CPU_BASE}"
' _ "${slug}")"

  assert_match '\$8000-\$FFFF' "${settings}"
  assert_match '\$8000' "${settings}"
}

test_rejects_unsupported_prg_size() {
  local slug; slug="$(unique_slug prg_bad)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --prg 3
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject PRG sizes outside 16/32 KB"
  assert_match "PRG units=3" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_rejects_wrong_chr_size() {
  local slug; slug="$(unique_slug chr)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --chr 2
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject CHR > 8 KB"
  assert_match "CHR units=2" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_rejects_truncated_container() {
  local slug; slug="$(unique_slug trunc)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes"
  # Truncate the ROM 100 bytes short
  python3 -c '
import sys
p = sys.argv[1]
data = open(p,"rb").read()
open(p,"wb").write(data[:-100])
' "${NESREV_TEST_TMPDIR}/rom.nes"
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject truncated container"
  assert_match "truncated" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}

test_rejects_trailing_bytes_by_default() {
  local slug; slug="$(unique_slug trail)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --trailing 13
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject trailing bytes by default"
  local stderr; stderr="$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
  assert_match "trailing 13 byte" "${stderr}"
  assert_match "ALLOW_TRAILING_BYTES=1" "${stderr}"
}

test_trailing_byte_override_proceeds_with_warning() {
  local slug; slug="$(unique_slug trail_ovr)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --trailing 7
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}" "ALLOW_TRAILING_BYTES=1")
  local stderr; stderr="$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
  assert_match "ALLOW_TRAILING_BYTES=1 set" "${stderr}" \
    "override path must emit the trailing-byte warning"
  assert_match "7 trailing byte" "${stderr}"
  assert_eq "${rc}" "0" "override path must complete successfully"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "override path must emit a non-empty asm file at projects/${slug}/asm/${slug}.asm"
}

test_accepts_ordinary_ines1_rom() {
  local slug; slug="$(unique_slug ok_ordinary)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes"
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "0" "ordinary strict-iNES 1.0 ROM must be accepted"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "ordinary ROM must produce a non-empty asm file"
}

test_direct_regenerator_invocation_is_not_cwd_sensitive() {
  local slug; slug="$(unique_slug cwd_regen)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes"
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen_from_dir "${NESREV_TEST_TMPDIR}" "${slug}")
  assert_eq "${rc}" "0" "direct regenerator invocation must work outside the repo root"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "direct regenerator invocation from another cwd must produce asm"
}

test_accepts_chr_ram_rom() {
  local slug; slug="$(unique_slug ok_chrram)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --chr 0
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "0" "CHR-RAM ROM (CHR=0) must be accepted"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "CHR-RAM ROM must produce a non-empty asm file"
}

test_accepts_trainer_bearing_rom() {
  local slug; slug="$(unique_slug ok_trainer)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --trainer 1
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "0" "trainer-bearing ROM must be accepted"
  [[ -s "projects/${slug}/asm/${slug}.asm" ]] \
    || fail "trainer-bearing ROM must produce a non-empty asm file"
}

test_tracked_control_config_reproduces_with_base_command() {
  local slug; slug="$(unique_slug tracked_control)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes"
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local control_dir="projects/${slug}/config/nesrev"
  local control_file="${control_dir}/codeentries.txt"
  mkdir -p "${control_dir}"
  printf '$C000\n' > "${control_file}"
  cat >> "projects/${slug}/project.conf" <<EOF
NESREV_RECOVERY_STATUS="configured"
NESREV_CODEENTRIES_FILE="${control_file}"
EOF

  if git check-ignore -q "${control_file}"; then
    fail "tracked NESrev control path is unexpectedly ignored: ${control_file}"
  fi

  set +e
  make project-regenerate-asm "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/regen.stdout" 2>"${NESREV_TEST_TMPDIR}/regen.stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "base regeneration must load tracked project.conf controls"
  assert_match "code entries config: ${control_file}" \
    "$(cat "${NESREV_TEST_TMPDIR}/regen.stdout")"

  cp "projects/${slug}/asm/${slug}.asm" "${NESREV_TEST_TMPDIR}/first.asm"
  make project-regenerate-asm "PROJECT=${slug}" >/dev/null
  cmp "${NESREV_TEST_TMPDIR}/first.asm" "projects/${slug}/asm/${slug}.asm" \
    || fail "base regeneration with tracked controls is not reproducible"
}

test_rejects_bad_magic() {
  local slug; slug="$(unique_slug magic)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes" --magic deadbeef
  scaffold_project "${slug}" "${NESREV_TEST_TMPDIR}/rom.nes"

  local rc; rc=$(_run_regen "${slug}")
  assert_eq "${rc}" "1" "regenerator should reject bad iNES magic"
  assert_match "not a valid iNES file" "$(cat "${NESREV_TEST_TMPDIR}/regen.stderr")"
}
