#!/usr/bin/env bash
# Shared helpers for tests/shell/cases/*_test.sh.
#
# Exposes:
#   fail "message"                  - print and exit non-zero
#   assert_eq actual expected msg   - string equality
#   assert_match regex string msg   - posix regex match
#   assert_exit expected_rc cmd...  - run cmd, assert exit code
#   make_ines out [opts...]         - synthesize an iNES ROM (see below)
#   scaffold_project slug rom_path  - create a minimal project.conf rig
#
# make_ines option flags:
#   --prg N        PRG units (default 1)
#   --chr N        CHR units (default 1)
#   --mapper N     mapper number (default 0)
#   --header-fmt N FLAGS7 bits[2:3]: 0=iNES1.0, 2=compatible NES2.0, 1/3=reserved (default 0)
#   --trainer 0|1  set bit 2 of FLAGS6 and prepend 512 trainer bytes (default 0)
#   --trailing N   append N synthetic trailing bytes (default 0)
#   --magic HEX    override iNES magic (4 hex bytes, default 4e45531a)

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

assert_eq() {
  local actual="$1" expected="$2" msg="${3:-}"
  if [[ "${actual}" != "${expected}" ]]; then
    fail "${msg:-assert_eq}: expected '${expected}', got '${actual}'"
  fi
}

assert_match() {
  local regex="$1" string="$2" msg="${3:-}"
  if ! [[ "${string}" =~ ${regex} ]]; then
    fail "${msg:-assert_match}: pattern '${regex}' not found in: ${string}"
  fi
}

assert_exit() {
  local expected_rc="$1"; shift
  local had_errexit=0
  [[ $- == *e* ]] && had_errexit=1
  set +e
  "$@"
  local rc=$?
  if (( had_errexit )); then
    set -e
  else
    set +e
  fi
  if (( rc != expected_rc )); then
    fail "assert_exit: expected rc=${expected_rc}, got rc=${rc} from: $*"
  fi
}

make_ines() {
  local out="$1"; shift
  local prg=1 chr=1 mapper=0 header_fmt=0 trainer=0 trailing=0
  local magic="4e45531a"
  while (( $# > 0 )); do
    case "$1" in
      --prg)        prg="$2"; shift 2 ;;
      --chr)        chr="$2"; shift 2 ;;
      --mapper)     mapper="$2"; shift 2 ;;
      --header-fmt) header_fmt="$2"; shift 2 ;;
      --trainer)    trainer="$2"; shift 2 ;;
      --trailing)   trailing="$2"; shift 2 ;;
      --magic)      magic="$2"; shift 2 ;;
      *) fail "make_ines: unknown option $1" ;;
    esac
  done

  local flags6 flags7
  flags6=$(( ((mapper & 0x0F) << 4) | ((trainer & 1) << 2) ))
  flags7=$(( (mapper & 0xF0) | ((header_fmt & 0x03) << 2) ))

  # Write 16-byte header
  python3 - "${out}" "${magic}" "${prg}" "${chr}" "${flags6}" "${flags7}" <<'PY'
import sys
out, magic, prg, chr_, f6, f7 = sys.argv[1:]
header = bytes.fromhex(magic) + bytes([int(prg), int(chr_), int(f6), int(f7)]) + b'\x00' * 8
with open(out, "wb") as fh:
    fh.write(header)
PY

  # Trainer
  if (( trainer == 1 )); then
    python3 -c 'import sys; open(sys.argv[1],"ab").write(b"\xee"*512)' "${out}"
  fi
  # PRG (16 KB units)
  python3 -c 'import sys; open(sys.argv[1],"ab").write(b"\xa9\x00\x60"+b"\x00"*(int(sys.argv[2])*16384-3))' "${out}" "${prg}"
  # CHR (8 KB units)
  if (( chr > 0 )); then
    python3 -c 'import sys; open(sys.argv[1],"ab").write(b"\x00"*(int(sys.argv[2])*8192))' "${out}" "${chr}"
  fi
  # Trailing
  if (( trailing > 0 )); then
    python3 -c 'import sys; open(sys.argv[1],"ab").write(b"\xff"*int(sys.argv[2]))' "${out}" "${trailing}"
  fi
}

scaffold_project() {
  local slug="$1" rom_path="$2"
  local proj_root="projects/${slug}"
  mkdir -p "${proj_root}"/{reference,asm,build,docs/reverse_engineering}
  cp "${rom_path}" "${proj_root}/reference/${slug}.nes"
  cat > "${proj_root}/project.conf" <<EOF
PROJECT_NAME="${slug}"
ASM_FILE="${proj_root}/asm/${slug}.asm"
REF_NES="${proj_root}/reference/${slug}.nes"
DOC_ROOT="${proj_root}/docs/reverse_engineering"
SYSTEMS_DOC="${proj_root}/docs/reverse_engineering/${slug}_DX_Systems.md"
WARN_BASELINE_FILE="${proj_root}/docs/reverse_engineering/WARNING_BASELINE.txt"
OUT_BIN="${proj_root}/build/${slug}.o"
EOF
}

cleanup_project() {
  local slug="$1"
  rm -rf "projects/${slug}"
}

unique_slug() {
  # Returns a slug of the form shtest_<base>_<uniq>, where <uniq> is the
  # per-test tmpdir suffix mktemp generated for this invocation. Two
  # concurrent runs of the same test get different tmpdirs and therefore
  # different slugs, keeping projects/shtest_* fixtures non-colliding.
  # The suffix is forced lowercase so the result matches the scaffold
  # generator's lowercase-only slug contract.
  local base="$1"
  local uniq="${NESREV_TEST_TMPDIR##*.}"
  if [[ -z "${uniq}" || "${uniq}" == "${NESREV_TEST_TMPDIR}" ]]; then
    # Fallback when the tmpdir name has no suffix (shouldn't happen with
    # mktemp -t but be defensive).
    uniq="$$"
  fi
  uniq="$(printf '%s' "${uniq}" | tr '[:upper:]' '[:lower:]')"
  echo "shtest_${base}_${uniq}"
}
