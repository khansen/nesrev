#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <working_notes_path> <max_lines>" >&2
  exit 64
fi

notes_file="$1"
max_lines="$2"

if ! [[ "${max_lines}" =~ ^[0-9]+$ ]]; then
  echo "error: max_lines must be a non-negative integer: ${max_lines}" >&2
  exit 64
fi
max_lines=$((10#${max_lines}))

if [[ ! -f "${notes_file}" ]]; then
  echo "OK: ${notes_file} not present; no working-notes maturity debt"
  exit 0
fi

line_count="$(awk 'END { print NR + 0 }' "${notes_file}")"
line_count="${line_count:-0}"
line_count=$((10#${line_count}))

if (( line_count > max_lines )); then
  cat >&2 <<EOF
FAIL: ${notes_file} has ${line_count} lines, exceeding the maturity budget (${max_lines}).
Promote stable facts to canonical docs/source, act on queued findings, and prune
${notes_file} to forward-pass hazards and unresolved evidence gaps. If a
project truly needs a larger live-notes budget, raise MAX_MATURITY_WORKING_NOTES_LINES
in project.conf with an explicit rationale in the scorecard.
EOF
  exit 1
fi

echo "OK: ${notes_file} maturity budget (${line_count}/${max_lines})"
