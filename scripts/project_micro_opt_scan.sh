#!/usr/bin/env bash
set -euo pipefail

# Regenerate a project's MICRO_OPTIMIZATION_CANDIDATES.md from the structured
# analysis in scripts/micro_optimization_scan.py (dead instructions +
# micro-optimizable idioms, verified against xasm's assembled listing).

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

DOC_OUT="${DOC_ROOT}/MICRO_OPTIMIZATION_CANDIDATES.md"
# Title-case the slug: donkey_kong_jr -> "Donkey Kong Jr"
TITLE="$(echo "$1" | tr '_' ' ' | awk '{for(i=1;i<=NF;i++)$i=toupper(substr($i,1,1)) substr($i,2)}1')"
COMMIT="$(git -C "${SCRIPT_DIR}/.." rev-parse --short HEAD 2>/dev/null || echo '(working tree)')"
DATE="$(date +%Y-%m-%d)"

python3 "${SCRIPT_DIR}/micro_optimization_scan.py" "${ASM_FILE}" \
  --doc-out "${DOC_OUT}" --title "${TITLE}" --commit "${COMMIT}" --date "${DATE}"

echo "wrote ${DOC_OUT}"
python3 "${SCRIPT_DIR}/micro_optimization_scan.py" "${ASM_FILE}" --print
