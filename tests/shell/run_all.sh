#!/usr/bin/env bash
# Keep the established shell entry point; Python measures elapsed monotonic time
# without launching a separate clock process around every Bash test.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
exec python3 "${SCRIPT_DIR}/run_all.py" "$@"
