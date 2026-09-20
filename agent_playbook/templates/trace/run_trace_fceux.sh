#!/usr/bin/env bash
# Template: supervised FCEUX frame-poll trace backend.
# Copy into projects/<slug>/scripts/ and replace PROJECT plus defaults.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
PROJECT="${PROJECT_SLUG:-example_project}"
PROJECT_ROOT="${ROOT}/projects/${PROJECT}"
ROM="${TRACE_ROM:-${PROJECT_ROOT}/reference/${PROJECT}.nes}"
LUA_SCRIPT="${TRACE_LUA:-${PROJECT_ROOT}/tools/trace/fceux_frame_poll_trace.lua}"
OUT_DIR="${1:-${PROJECT_ROOT}/tmp/traces}"
MAX_FRAMES="${TRACE_MAX_FRAMES:-36000}"
TIMEOUT="${TRACE_TIMEOUT:-180}"
MOVIE="${MOVIE:-}"
INPUT2="${TRACE_INPUT2:-}"
FCEUX_BIN="${FCEUX_BIN:-fceux}"

args=(--rom "${ROM}" --lua "${LUA_SCRIPT}" --fceux "${FCEUX_BIN}"
      --output-dir "${OUT_DIR}" --max-frames "${MAX_FRAMES}" --timeout "${TIMEOUT}")
if [[ -n "${INPUT2}" ]]; then args+=(--input2 "${INPUT2}"); fi
if [[ -n "${MOVIE}" ]]; then args+=(--movie "${MOVIE}"); fi

# Replace these required milestones together with the Lua scenario predicates.
args+=(--require-milestone scenario_started --require-milestone result_resolved)
exec python3 "${ROOT}/scripts/run_fceux_trace.py" "${args[@]}"
