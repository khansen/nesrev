#!/usr/bin/env bash
set -euo pipefail

# Working-notes maturity check: the notes file, if present, must stay within
# its maturity line budget.
#
# This deliberately does not report on deferrals. Systematic deferral with no
# structured record is one condition and needs one owner, which is
# `deferrals_uncaptured` in proof_debt.py — a rate rather than an absolute
# count. Reporting it here too meant the same condition surfacing twice with
# two different thresholds.

if [[ $# -lt 2 || $# -gt 3 ]]; then
  echo "usage: $0 <working_notes_path> <max_lines> [scorecard_path]" >&2
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
  echo "OK: ${notes_file} not present; no line budget to enforce"
  exit 0
fi

line_count="$(awk 'END { print NR + 0 }' "${notes_file}")"
line_count="${line_count:-0}"
line_count=$((10#${line_count}))

if (( line_count > max_lines )); then
  echo "working-notes maturity budget exceeded: ${notes_file} has ${line_count} lines (max ${max_lines})" >&2
  echo "promote stable facts to source/docs, act on queued findings, then prune" >&2
  exit 1
fi

echo "OK: ${notes_file} within maturity budget (${line_count}/${max_lines} lines)"
