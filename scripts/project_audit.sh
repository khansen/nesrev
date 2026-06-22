#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 <project_slug> [text|json]" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"
OUTPUT_FORMAT="${2:-text}"

mkdir -p "$(dirname "${OUT_BIN}")"
cmd=(
  xasm
  --pure-binary
  -o "${OUT_BIN}"
  --audit-raw-addresses
  "--audit-output-format=${OUTPUT_FORMAT}"
)

if [[ -n "${XASM_AUDIT_ROM_RANGE:-}" ]]; then
  cmd+=("--audit-rom-range=${XASM_AUDIT_ROM_RANGE}")
fi

cmd+=("${ASM_FILE}")
"${cmd[@]}"
