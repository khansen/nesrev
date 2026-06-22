#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "usage: $0 <project_slug> <mod_slug> [ips|bps]" >&2
  exit 2
fi

PROJECT_SLUG="$1"
MOD_SLUG="$2"
REQUESTED_FORMAT="${3:-}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/mod_common.sh
source "${SCRIPT_DIR}/mod_common.sh"

load_mod_conf "${PROJECT_SLUG}" "${MOD_SLUG}"

FORMAT="${REQUESTED_FORMAT:-${PATCH_FORMAT_DEFAULT:-ips}}"
if [[ "${FORMAT}" != "ips" && "${FORMAT}" != "bps" ]]; then
  echo "error: unsupported patch format '${FORMAT}' (expected ips or bps)" >&2
  exit 2
fi

if [[ ! -f "${OUT_NES_FILE}" ]]; then
  bash "${SCRIPT_DIR}/build_mod.sh" "${PROJECT_SLUG}" "${MOD_SLUG}"
fi

if [[ ! -f "${REF_NES_FILE}" ]]; then
  echo "error: reference ROM not found: ${REF_NES_FILE}" >&2
  exit 3
fi
if [[ ! -f "${OUT_NES_FILE}" ]]; then
  echo "error: mod ROM not found: ${OUT_NES_FILE}" >&2
  exit 3
fi

mkdir -p "$(dirname "${OUT_PATCH_FILE}")"
TMPDIR_PATCH="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_PATCH}"' EXIT
ROUNDTRIP_ROM="${TMPDIR_PATCH}/roundtrip.nes"
PATCH_BASE="${OUT_PATCH_FILE%.*}"
if [[ "${PATCH_BASE}" == "${OUT_PATCH_FILE}" ]]; then
  PATCH_BASE="${OUT_PATCH_FILE}"
fi

if [[ "${FORMAT}" == "ips" ]]; then
  OUT_PATCH_FILE="${PATCH_BASE}.ips"
  echo "[1/2] Creating IPS patch ${OUT_PATCH_FILE}"
  python3 "${SCRIPT_DIR}/ips_patch.py" create "${REF_NES_FILE}" "${OUT_NES_FILE}" "${OUT_PATCH_FILE}" || exit 5
  echo "[2/2] Verifying IPS patch roundtrip"
  python3 "${SCRIPT_DIR}/ips_patch.py" apply "${REF_NES_FILE}" "${OUT_PATCH_FILE}" "${ROUNDTRIP_ROM}" || exit 5
else
  OUT_PATCH_FILE="${PATCH_BASE}.bps"
  if ! command -v flips >/dev/null 2>&1; then
    echo "error: bps requested but 'flips' is not installed" >&2
    exit 5
  fi
  echo "[1/2] Creating BPS patch ${OUT_PATCH_FILE}"
  flips --create --bps "${REF_NES_FILE}" "${OUT_NES_FILE}" "${OUT_PATCH_FILE}" || exit 5
  echo "[2/2] Verifying BPS patch roundtrip"
  flips --apply --bps "${OUT_PATCH_FILE}" "${REF_NES_FILE}" "${ROUNDTRIP_ROM}" || exit 5
fi

if ! cmp -s "${ROUNDTRIP_ROM}" "${OUT_NES_FILE}"; then
  echo "error: roundtrip patch check failed: reconstructed ROM differs from mod ROM" >&2
  exit 5
fi

echo "Patch created and verified:"
echo "  ${OUT_PATCH_FILE}"
