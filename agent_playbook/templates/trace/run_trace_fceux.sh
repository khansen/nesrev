#!/usr/bin/env bash
# Template: operator-run FCEUX frame-poll trace backend.
# Copy into projects/<slug>/scripts/ and replace PROJECT plus defaults.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
PROJECT="${PROJECT_SLUG:-example_project}"
PROJECT_ROOT="${ROOT}/projects/${PROJECT}"
ROM="${TRACE_ROM:-${PROJECT_ROOT}/reference/${PROJECT}.nes}"
LUA_SCRIPT="${TRACE_LUA:-${PROJECT_ROOT}/tools/trace/fceux_frame_poll_trace.lua}"
OUT="${1:-${PROJECT_ROOT}/tmp/traces/trace.log}"
MAX_FRAMES="${TRACE_MAX_FRAMES:-36000}"
MOVIE="${MOVIE:-}"
INPUT2="${TRACE_INPUT2:-}"
FCEUX_BIN="${FCEUX_BIN:-fceux}"

if ! command -v "${FCEUX_BIN}" >/dev/null 2>&1; then
  echo "ERROR: ${FCEUX_BIN} not found in PATH" >&2
  exit 1
fi
if [[ ! -f "${ROM}" ]]; then
  echo "ERROR: missing ROM: ${ROM}" >&2
  exit 1
fi
if [[ ! -f "${LUA_SCRIPT}" ]]; then
  echo "ERROR: missing Lua trace script: ${LUA_SCRIPT}" >&2
  exit 1
fi

mkdir -p "$(dirname "${OUT}")"

args=(--no-config 1 --sound 0)
if [[ -n "${INPUT2}" ]]; then args+=(--input2 "${INPUT2}"); fi
if [[ -n "${MOVIE}" ]]; then args+=(--playmovie "${MOVIE}"); fi

echo "FCEUX trace -> ${OUT} (frames: ${MAX_FRAMES}${MOVIE:+, movie: ${MOVIE}})"
TRACE_OUT="${OUT}" TRACE_MAX_FRAMES="${MAX_FRAMES}" \
  "${FCEUX_BIN}" "${args[@]}" --loadlua "${LUA_SCRIPT}" "${ROM}"
echo "Trace complete: ${OUT}"
