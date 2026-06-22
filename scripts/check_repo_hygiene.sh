#!/usr/bin/env bash
set -euo pipefail

tracked_ignored="$(
  git ls-files -ci --exclude-standard |
    grep -v '/\.gitkeep$' || true
)"

tracked_build_placeholders="$(
  git ls-files |
    grep -E '^projects/.*/build/\.gitkeep$' || true
)"

if [[ -n "${tracked_ignored}" ]]; then
  echo "FAIL: ignored generated/private files are tracked:" >&2
  printf '%s\n' "${tracked_ignored}" | sed 's/^/  /' >&2
  exit 1
fi

if [[ -n "${tracked_build_placeholders}" ]]; then
  echo "FAIL: build directories must not contain tracked .gitkeep placeholders:" >&2
  printf '%s\n' "${tracked_build_placeholders}" | sed 's/^/  /' >&2
  exit 1
fi

python3 scripts/check_symbol_naming.py --tracked-primary

echo "OK: no ignored generated/private files are tracked"
