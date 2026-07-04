#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 6 ]]; then
  echo "usage: $0 <project_slug> [codepointers_csv] [codeentries_txt] [datapointers_csv] [inlinecalls_csv] [dataranges_csv]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"
# Command-line paths are explicit one-run overrides. The normal reproducible
# path comes from tracked project.conf settings.
CODEPOINTERS_CSV="${2:-${NESREV_CODEPOINTERS_FILE}}"
CODEENTRIES_TXT="${3:-${NESREV_CODEENTRIES_FILE}}"
DATAPOINTERS_CSV="${4:-${NESREV_DATAPOINTERS_FILE}}"
INLINECALLS_CSV="${5:-${NESREV_INLINECALLS_FILE}}"
DATARANGES_CSV="${6:-${NESREV_DATARANGES_FILE}}"

if [[ ! -f "${REF_NES}" ]]; then
  echo "error: reference iNES file not found: ${REF_NES}" >&2
  exit 1
fi

if [[ -n "${CODEPOINTERS_CSV}" && ! -f "${CODEPOINTERS_CSV}" ]]; then
  echo "error: codepointers csv not found: ${CODEPOINTERS_CSV}" >&2
  exit 1
fi

if [[ -n "${CODEENTRIES_TXT}" && ! -f "${CODEENTRIES_TXT}" ]]; then
  echo "error: codeentries file not found: ${CODEENTRIES_TXT}" >&2
  exit 1
fi

if [[ -n "${DATAPOINTERS_CSV}" && ! -f "${DATAPOINTERS_CSV}" ]]; then
  echo "error: datapointers csv not found: ${DATAPOINTERS_CSV}" >&2
  exit 1
fi

if [[ -n "${INLINECALLS_CSV}" && ! -f "${INLINECALLS_CSV}" ]]; then
  echo "error: inlinecalls csv not found: ${INLINECALLS_CSV}" >&2
  exit 1
fi

if [[ -n "${DATARANGES_CSV}" && ! -f "${DATARANGES_CSV}" ]]; then
  echo "error: dataranges csv not found: ${DATARANGES_CSV}" >&2
  exit 1
fi

if ! command -v javac >/dev/null 2>&1; then
  echo "error: javac not found in PATH" >&2
  exit 1
fi

if ! command -v java >/dev/null 2>&1; then
  echo "error: java not found in PATH" >&2
  exit 1
fi

INES_MAGIC="$(od -An -tx1 -N4 "${REF_NES}" | tr -d ' \n')"
if [[ "${INES_MAGIC}" != "4e45531a" ]]; then
  echo "error: ${REF_NES} is not a valid iNES file (bad magic)" >&2
  exit 1
fi

PRG_UNITS="$(od -An -tu1 -j4 -N1 "${REF_NES}" | tr -d ' ')"
CHR_UNITS="$(od -An -tu1 -j5 -N1 "${REF_NES}" | tr -d ' ')"
FLAGS6="$(od -An -tu1 -j6 -N1 "${REF_NES}" | tr -d ' ')"
FLAGS7="$(od -An -tu1 -j7 -N1 "${REF_NES}" | tr -d ' ')"

HEADER_BITS=$(( (FLAGS7 & 0x0C) >> 2 ))
MAPPER_NUMBER=$(( (FLAGS6 >> 4) | (FLAGS7 & 0xF0) ))

if (( HEADER_BITS == 2 )); then
  NES2_BYTE8="$(od -An -tu1 -j8 -N1 "${REF_NES}" | tr -d ' ')"
  NES2_BYTE9="$(od -An -tu1 -j9 -N1 "${REF_NES}" | tr -d ' ')"
  NES2_MAPPER_HIGH=$(( NES2_BYTE8 & 0x0F ))
  NES2_PRG_UNITS_HIGH=$(( NES2_BYTE9 & 0x0F ))
  NES2_CHR_UNITS_HIGH=$(( (NES2_BYTE9 >> 4) & 0x0F ))
  MAPPER_NUMBER=$(( MAPPER_NUMBER | (NES2_MAPPER_HIGH << 8) ))
  PRG_UNITS=$(( PRG_UNITS | (NES2_PRG_UNITS_HIGH << 8) ))
  CHR_UNITS=$(( CHR_UNITS | (NES2_CHR_UNITS_HIGH << 8) ))
elif (( HEADER_BITS != 0 )); then
  echo "error: ${REF_NES} has FLAGS7 bits[2:3]=${HEADER_BITS}; nesrev supports iNES 1.0 (bits[2:3]=0) and compatible NES 2.0 (bits[2:3]=2) headers only." >&2
  echo "       See agent_playbook/NEW_PROJECT.md#rom-support-matrix for the full support matrix." >&2
  exit 1
fi

# Supported ROM matrix (must match agent_playbook/NEW_PROJECT.md#rom-support-matrix):
#   iNES 1.0 or NES 2.0 headers whose decoded fields stay in this matrix
#   mapper 0 (NROM)
#   PRG = 16 KB (1 unit) or 32 KB (2 units)
#   CHR = 0 or 8 KB (0 or 1 unit)
if [[ "${MAPPER_NUMBER}" != "0" ]]; then
  echo "error: ${REF_NES} uses mapper ${MAPPER_NUMBER}; nesrev currently supports mapper 0 (NROM) only." >&2
  echo "       See agent_playbook/NEW_PROJECT.md#rom-support-matrix for the full support matrix." >&2
  exit 1
fi
if [[ "${PRG_UNITS}" != "1" && "${PRG_UNITS}" != "2" ]]; then
  echo "error: ${REF_NES} has PRG units=${PRG_UNITS}; nesrev currently supports PRG=16 KB or 32 KB (1 or 2 units) only." >&2
  echo "       See agent_playbook/NEW_PROJECT.md#rom-support-matrix for the full support matrix." >&2
  exit 1
fi
if [[ "${CHR_UNITS}" != "0" && "${CHR_UNITS}" != "1" ]]; then
  echo "error: ${REF_NES} has CHR units=${CHR_UNITS}; nesrev currently supports CHR=0 or 8 KB (0 or 1 unit)." >&2
  echo "       See agent_playbook/NEW_PROJECT.md#rom-support-matrix for the full support matrix." >&2
  exit 1
fi

TRAINER_SIZE=0
if (( (FLAGS6 & 0x04) != 0 )); then
  TRAINER_SIZE=512
fi

PRG_OFFSET=$((16 + TRAINER_SIZE))
PRG_SIZE=$((PRG_UNITS * 16384))
CHR_SIZE=$((CHR_UNITS * 8192))
EXPECTED_SIZE=$((PRG_OFFSET + PRG_SIZE + CHR_SIZE))
REF_SIZE="$(wc -c < "${REF_NES}" | tr -d ' ')"

if (( REF_SIZE < EXPECTED_SIZE )); then
  echo "error: ${REF_NES} is truncated (size ${REF_SIZE}, expected ${EXPECTED_SIZE})." >&2
  echo "       Header declares PRG=${PRG_UNITS}x16 KB, CHR=${CHR_UNITS}x8 KB, trainer=${TRAINER_SIZE} bytes." >&2
  exit 1
fi
if (( REF_SIZE > EXPECTED_SIZE )); then
  if [[ "${ALLOW_TRAILING_BYTES:-0}" != "1" ]]; then
    echo "error: ${REF_NES} has ${REF_SIZE} bytes but the iNES header declares ${EXPECTED_SIZE}." >&2
    echo "       The trailing $(( REF_SIZE - EXPECTED_SIZE )) byte(s) may be dumper metadata or hidden data; review before intake." >&2
    echo "       Re-run with ALLOW_TRAILING_BYTES=1 to proceed once the trailer has been audited." >&2
    echo "       See agent_playbook/NEW_PROJECT.md#trailing-byte-override for the audit and override procedure." >&2
    exit 1
  fi
  echo "warn: ${REF_NES} has ${REF_SIZE} bytes; ALLOW_TRAILING_BYTES=1 set, proceeding with $(( REF_SIZE - EXPECTED_SIZE )) trailing byte(s) ignored." >&2
fi

TMPDIR_REGEN="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_REGEN}"' EXIT
RAW_PRG="${TMPDIR_REGEN}/rom.prg"
OUT_ASM="${TMPDIR_REGEN}/regen.asm"

dd if="${REF_NES}" of="${RAW_PRG}" bs=1 skip="${PRG_OFFSET}" count="${PRG_SIZE}" status=none

javac NESrev.java -Xlint:unchecked >/dev/null

cmd=(java NESrev "${RAW_PRG}")
if [[ -n "${CODEPOINTERS_CSV}" ]]; then
  cmd+=(-codepointers "${CODEPOINTERS_CSV}")
fi
if [[ -n "${DATAPOINTERS_CSV}" ]]; then
  cmd+=(-datapointers "${DATAPOINTERS_CSV}")
fi
if [[ -n "${CODEENTRIES_TXT}" ]]; then
  cmd+=(-codeentries "${CODEENTRIES_TXT}")
fi
if [[ -n "${INLINECALLS_CSV}" ]]; then
  cmd+=(-inlinecalls "${INLINECALLS_CSV}")
fi
if [[ -n "${DATARANGES_CSV}" ]]; then
  cmd+=(-dataranges "${DATARANGES_CSV}")
fi

"${cmd[@]}" > "${OUT_ASM}"
mv "${OUT_ASM}" "${ASM_FILE}"

echo "asm regenerated: ${ASM_FILE}"
if [[ -n "${CODEPOINTERS_CSV}" ]]; then
  echo "code pointer config: ${CODEPOINTERS_CSV} (raw PRG offsets)"
fi
if [[ -n "${DATAPOINTERS_CSV}" ]]; then
  echo "data pointer config: ${DATAPOINTERS_CSV} (raw PRG offsets)"
fi
if [[ -n "${CODEENTRIES_TXT}" ]]; then
  echo "code entries config: ${CODEENTRIES_TXT} (CPU addresses)"
fi
if [[ -n "${INLINECALLS_CSV}" ]]; then
  echo "inline-call config: ${INLINECALLS_CSV} (CPU addresses)"
fi
if [[ -n "${DATARANGES_CSV}" ]]; then
  echo "data-range config: ${DATARANGES_CSV} (CPU addresses)"
fi
