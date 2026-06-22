#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <project_slug> <mod_slug>" >&2
  exit 2
fi

PROJECT_SLUG="$1"
MOD_SLUG="$2"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/mod_common.sh
source "${SCRIPT_DIR}/mod_common.sh"

load_mod_conf "${PROJECT_SLUG}" "${MOD_SLUG}"

if ! command -v xasm >/dev/null 2>&1; then
  echo "error: xasm not found in PATH" >&2
  exit 3
fi

if [[ ! -d "${MOD_ROOT}" ]]; then
  echo "error: mod directory not found: ${MOD_ROOT}" >&2
  exit 3
fi
if [[ ! -f "${MOD_ASM_FILE}" ]]; then
  echo "error: mod asm file not found: ${MOD_ASM_FILE}" >&2
  exit 3
fi
if [[ ! -f "${REF_NES_FILE}" ]]; then
  echo "error: reference ROM not found: ${REF_NES_FILE}" >&2
  exit 3
fi

mkdir -p "$(dirname "${OUT_PRG_FILE}")"
TMP_BUILD_DIR="$(mktemp -d)"
trap 'rm -rf "${TMP_BUILD_DIR}"' EXIT

echo "[1/4] Assembling mod PRG from ${MOD_ASM_FILE}"
TEMP_ASM_FILE="${TMP_BUILD_DIR}/$(basename "${MOD_ASM_FILE}")"
cp "${MOD_ASM_FILE}" "${TEMP_ASM_FILE}"
xasm --pure-binary "${TEMP_ASM_FILE}"
XASM_OUT_FILE="${TEMP_ASM_FILE%.asm}.o"
if [[ ! -f "${XASM_OUT_FILE}" ]]; then
  echo "error: expected xasm output not found: ${XASM_OUT_FILE}" >&2
  exit 4
fi
cp "${XASM_OUT_FILE}" "${OUT_PRG_FILE}"

PRG_SIZE_OUT="$(wc -c < "${OUT_PRG_FILE}" | tr -d ' ')"
if [[ "${PRG_SIZE_OUT}" != "16384" ]]; then
  echo "error: assembled PRG size is ${PRG_SIZE_OUT}, expected 16384" >&2
  exit 4
fi

echo "[2/4] Validating reference ROM layout"
INES_MAGIC="$(od -An -tx1 -N4 "${REF_NES_FILE}" | tr -d ' \n')"
if [[ "${INES_MAGIC}" != "4e45531a" ]]; then
  echo "error: ${REF_NES_FILE} is not a valid iNES file (bad magic)" >&2
  exit 4
fi
PRG_UNITS="$(od -An -tu1 -j4 -N1 "${REF_NES_FILE}" | tr -d ' ')"
CHR_UNITS="$(od -An -tu1 -j5 -N1 "${REF_NES_FILE}" | tr -d ' ')"
FLAGS6="$(od -An -tu1 -j6 -N1 "${REF_NES_FILE}" | tr -d ' ')"
if [[ -z "${PRG_UNITS}" || -z "${CHR_UNITS}" || -z "${FLAGS6}" ]]; then
  echo "error: failed to parse iNES header fields from ${REF_NES_FILE}" >&2
  exit 4
fi
if (( (FLAGS6 & 0x04) != 0 )); then
  echo "error: trainer-backed ROMs are not supported in mod workflow v1" >&2
  exit 4
fi
if [[ "${PRG_UNITS}" != "1" || "${CHR_UNITS}" != "1" ]]; then
  echo "error: mod workflow v1 only supports 16KB PRG + 8KB CHR (found PRG=${PRG_UNITS}, CHR=${CHR_UNITS})" >&2
  exit 4
fi

HEADER_BIN="${TMP_BUILD_DIR}/header.bin"
CHR_BIN="${TMP_BUILD_DIR}/chr.bin"

echo "[3/4] Extracting header and CHR from reference ROM"
dd if="${REF_NES_FILE}" of="${HEADER_BIN}" bs=1 count=16 status=none
dd if="${REF_NES_FILE}" of="${CHR_BIN}" bs=1 skip=$((16 + 16384)) count=8192 status=none

echo "[4/4] Building mod ROM ${OUT_NES_FILE}"
cat "${HEADER_BIN}" "${OUT_PRG_FILE}" "${CHR_BIN}" > "${OUT_NES_FILE}"

OUT_NES_SIZE="$(wc -c < "${OUT_NES_FILE}" | tr -d ' ')"
if [[ "${OUT_NES_SIZE}" != "24592" ]]; then
  echo "error: built mod ROM size is ${OUT_NES_SIZE}, expected 24592" >&2
  exit 4
fi

echo "Built mod outputs:"
echo "  PRG: ${OUT_PRG_FILE}"
echo "  ROM: ${OUT_NES_FILE}"
