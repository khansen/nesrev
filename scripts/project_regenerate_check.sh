#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

PROJECT_SLUG="$1"
load_project_conf "${PROJECT_SLUG}"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: committed asm file not found: ${ASM_FILE}" >&2
  exit 65
fi

STRICT_MODE="${STRICT:-0}"
case "${STRICT_MODE}" in
  0|1) ;;
  *) echo "error: STRICT must be 0 or 1" >&2; exit 64 ;;
esac

MAX_DIFF_LINES="${REGENERATE_DIFF_MAX_LINES:-200}"
if [[ ! "${MAX_DIFF_LINES}" =~ ^[0-9]+$ ]] || (( MAX_DIFF_LINES < 1 )); then
  echo "error: REGENERATE_DIFF_MAX_LINES must be a positive integer" >&2
  exit 64
fi

TMPDIR_REGENERATE_CHECK="$(mktemp -d)"
trap 'rm -rf "${TMPDIR_REGENERATE_CHECK}"' EXIT
REGENERATED_ASM="${TMPDIR_REGENERATE_CHECK}/regenerated.asm"
DIFF_FILE="${TMPDIR_REGENERATE_CHECK}/regeneration.diff"

PROJECT_REGENERATE_OUTPUT_ASM="${REGENERATED_ASM}" \
  bash "${SCRIPT_DIR}/project_regenerate_asm.sh" "${PROJECT_SLUG}" >/dev/null

set +e
diff -u \
  --label "${ASM_FILE} (committed)" \
  --label "${ASM_FILE} (regenerated)" \
  "${ASM_FILE}" "${REGENERATED_ASM}" >"${DIFF_FILE}"
DIFF_RC=$?
set -e

if (( DIFF_RC == 0 )); then
  echo "[regenerate-check] status=clean diff_lines=0"
  exit 0
fi
if (( DIFF_RC != 1 )); then
  echo "error: diff failed while comparing ${ASM_FILE}" >&2
  exit "${DIFF_RC}"
fi

DIFF_LINES="$(wc -l <"${DIFF_FILE}" | tr -d ' ')"
echo "[regenerate-check] status=drift diff_lines=${DIFF_LINES}"
sed -n "1,${MAX_DIFF_LINES}p" "${DIFF_FILE}"
if (( DIFF_LINES > MAX_DIFF_LINES )); then
  echo "... $((DIFF_LINES - MAX_DIFF_LINES)) diff line(s) omitted; set REGENERATE_DIFF_MAX_LINES to adjust the preview" >&2
fi

if (( STRICT_MODE == 1 )); then
  echo "FAIL: committed asm differs from base-command regeneration" >&2
  exit 69
fi

echo "advisory: committed asm differs from base-command regeneration; review and record intentional normalization or semantic edits" >&2
exit 0
