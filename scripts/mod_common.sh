#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_mod_conf() {
  if [[ $# -ne 2 ]]; then
    echo "usage: load_mod_conf <project_slug> <mod_slug>" >&2
    exit 2
  fi

  local project_slug="$1"
  local mod_slug="$2"

  if [[ ! "${project_slug}" =~ ^[a-z0-9_-]+$ ]]; then
    echo "error: project_slug must match [a-z0-9_-]+" >&2
    exit 2
  fi
  if [[ ! "${mod_slug}" =~ ^[a-z0-9_-]+$ ]]; then
    echo "error: mod_slug must match [a-z0-9_-]+" >&2
    exit 2
  fi

  load_project_conf "${project_slug}"

  MOD_ROOT="projects/${project_slug}/mods/${mod_slug}"
  MOD_CONF="${MOD_ROOT}/mod.conf"
  MOD_ASM_BASENAME="$(basename "${ASM_FILE}")"
  MOD_ASM_FILE="${MOD_ROOT}/asm/${MOD_ASM_BASENAME}"
  REF_NES_FILE="${REF_NES}"
  OUT_PRG_FILE="${MOD_ROOT}/build/${mod_slug}.o"
  OUT_NES_FILE="${MOD_ROOT}/build/${mod_slug}.nes"
  OUT_PATCH_FILE="${MOD_ROOT}/build/${mod_slug}.ips"
  PATCH_FORMAT_DEFAULT="ips"
  PROJECT_SLUG="${project_slug}"
  MOD_SLUG="${mod_slug}"

  if [[ -f "${MOD_CONF}" ]]; then
    # shellcheck disable=SC1090
    source "${MOD_CONF}"
  fi

  if [[ -z "${MOD_ASM_FILE:-}" || -z "${REF_NES_FILE:-}" || -z "${OUT_PRG_FILE:-}" || -z "${OUT_NES_FILE:-}" ]]; then
    echo "error: missing required mod.conf fields in ${MOD_CONF}" >&2
    exit 3
  fi
}
