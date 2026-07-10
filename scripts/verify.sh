#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 4 || $# -gt 5 ]]; then
  echo "usage: $0 <asm_file> <ref_nes> <out_bin> <warn_baseline_file> [compare_cpu_base]" >&2
  echo "(invoke via 'make project-verify PROJECT=<slug>' rather than directly)" >&2
  exit 64
fi

ASM_FILE="$1"
REF_NES="$2"
OUT_BIN="$3"
WARN_BASELINE_FILE="$4"
COMPARE_CPU_BASE="${5:-}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"
TMPDIR_VERIFY="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_VERIFY}"' EXIT

if ! command -v xasm >/dev/null 2>&1; then
  echo "error: xasm not found in PATH" >&2
  exit 1
fi

if ! command -v rg >/dev/null 2>&1; then
  echo "error: rg not found in PATH" >&2
  exit 1
fi

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 1
fi

if [[ ! -f "${REF_NES}" ]]; then
  echo "error: reference iNES file not found: ${REF_NES}" >&2
  exit 1
fi

echo "[1/4] Assembling ${ASM_FILE} (unused .EQU = error)"
XASM_LOG="${TMPDIR_VERIFY}/xasm.log"
mkdir -p "$(dirname "${OUT_BIN}")"
xasm --pure-binary --Werror=unused-equ -o "${OUT_BIN}" "${ASM_FILE}" 2>&1 | tee "${XASM_LOG}"

echo "[1b/4] Validating expected warning baseline"
rg "warning: .*defined but not used" "${XASM_LOG}" \
  | sed -E "s/.*warning: \`([A-Za-z_][A-Za-z0-9_]*)' defined but not used.*/\\1/" \
  | sort -u > "${TMPDIR_VERIFY}/warnings_actual_symbols.txt" || true

if [[ ! -f "${WARN_BASELINE_FILE}" ]]; then
  echo "error: warning baseline file not found: ${WARN_BASELINE_FILE}" >&2
  exit 1
fi

awk -F'|' '
  /^[[:space:]]*#/ { next }
  /^[[:space:]]*$/ { next }
  {
    sym=$1
    gsub(/[[:space:]]+$/, "", sym)
    print sym
  }
' "${WARN_BASELINE_FILE}" | sort -u > "${TMPDIR_VERIFY}/warnings_expected_symbols.txt"

if ! cmp -s "${TMPDIR_VERIFY}/warnings_expected_symbols.txt" "${TMPDIR_VERIFY}/warnings_actual_symbols.txt"; then
  echo "FAIL: assembler warning baseline changed" >&2
  echo "--- expected warning symbols ---" >&2
  cat "${TMPDIR_VERIFY}/warnings_expected_symbols.txt" >&2
  echo "--- actual warning symbols ---" >&2
  cat "${TMPDIR_VERIFY}/warnings_actual_symbols.txt" >&2
  exit 5
fi
echo "OK: warning baseline unchanged"

echo "[2/4] Comparing ${OUT_BIN} to PRG ROM in ${REF_NES}"

REF_PRG="${TMPDIR_VERIFY}/reference_prg.bin"
extract_reference_prg_from_ines "${REF_NES}" "${REF_PRG}"

if cmp -s "${REF_PRG}" "${OUT_BIN}"; then
  echo "OK: binary identity preserved"
else
  echo "FAIL: output PRG differs from iNES PRG reference" >&2
  echo "running xasm --compare for first mismatch source mapping..." >&2
  compare_cmd=(
    xasm
    --pure-binary
    -o "${TMPDIR_VERIFY}/scratch.o"
    "--compare=${REF_PRG}"
    "${ASM_FILE}"
  )
  if [[ -n "${COMPARE_CPU_BASE}" ]]; then
    compare_cmd=(
      xasm
      --pure-binary
      -o "${TMPDIR_VERIFY}/scratch.o"
      "--compare=${REF_PRG}"
      "--compare-cpu-base=${COMPARE_CPU_BASE}"
      "${ASM_FILE}"
    )
  fi
  set +e
  "${compare_cmd[@]}" >"${TMPDIR_VERIFY}/compare.log" 2>&1
  compare_rc=$?
  set -e
  cat "${TMPDIR_VERIFY}/compare.log" >&2
  if [[ "${compare_rc}" -ne 5 ]]; then
    echo "warning: xasm --compare exited with ${compare_rc} (expected 5 on mismatch)" >&2
  fi
  exit 2
fi

echo "[3/4] Checking unresolved generic labels"
if rg -n "\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:" "${ASM_FILE}" >"${TMPDIR_VERIFY}/labels.out"; then
  label_count="$(rg -o "\bL[0-9A-F]{4,5}\b" "${ASM_FILE}" | sort -u | wc -l | tr -d ' ')"
  ref_count="$(wc -l <"${TMPDIR_VERIFY}/labels.out" | tr -d ' ')"
  if [[ "${ALLOW_UNRESOLVED_LXXXX:-0}" == "1" ]]; then
    echo "WARN: ${label_count} distinct LXXXX/LXXXXX labels (${ref_count} refs); allowed by ALLOW_UNRESOLVED_LXXXX=1" >&2
  else
    echo "FAIL: ${label_count} distinct LXXXX/LXXXXX labels (${ref_count} refs)" >&2
    sample_lines=20
    head -n "${sample_lines}" "${TMPDIR_VERIFY}/labels.out" >&2
    if (( ref_count > sample_lines )); then
      echo "... +$((ref_count - sample_lines)) more sites; to list all: rg -n '\\bL[0-9A-F]{4,5}\\b' ${ASM_FILE}" >&2
    fi
    exit 3
  fi
else
  echo "OK: no unresolved LXXXX/LXXXXX labels"
fi

echo "[4/4] Checking unknown UNK_* symbols"
if rg -n "\bUNK_" "${ASM_FILE}" >"${TMPDIR_VERIFY}/unk.out"; then
  echo "WARN: UNK_* symbols still present:" >&2
  cat "${TMPDIR_VERIFY}/unk.out" >&2
  echo "(non-fatal)"
else
  echo "OK: no UNK_* symbols"
fi

echo "Verification complete"
