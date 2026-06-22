#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <project_slug> <mod_slug>" >&2
  exit 2
fi

PROJECT_SLUG="$1"
MOD_SLUG="$2"

if [[ ! "${PROJECT_SLUG}" =~ ^[a-z0-9_-]+$ ]]; then
  echo "error: project_slug must match [a-z0-9_-]+" >&2
  exit 2
fi
if [[ ! "${MOD_SLUG}" =~ ^[a-z0-9_-]+$ ]]; then
  echo "error: mod_slug must match [a-z0-9_-]+" >&2
  exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "${PROJECT_SLUG}"

if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: source asm file from project.conf not found: ${ASM_FILE}" >&2
  exit 3
fi

MOD_ROOT="projects/${PROJECT_SLUG}/mods/${MOD_SLUG}"
MOD_ASM_BASENAME="$(basename "${ASM_FILE}")"
MOD_ASM_FILE="${MOD_ROOT}/asm/${MOD_ASM_BASENAME}"
REF_NES_FILE="${REF_NES}"
OUT_PRG_FILE="${MOD_ROOT}/build/${MOD_SLUG}.o"
OUT_NES_FILE="${MOD_ROOT}/build/${MOD_SLUG}.nes"
OUT_PATCH_FILE="${MOD_ROOT}/build/${MOD_SLUG}.ips"
MOD_CONF="${MOD_ROOT}/mod.conf"

if [[ -e "${MOD_ROOT}" ]]; then
  echo "error: mod directory already exists: ${MOD_ROOT}" >&2
  exit 3
fi

mkdir -p "${MOD_ROOT}/asm" "${MOD_ROOT}/build" "${MOD_ROOT}/docs"
cp "${ASM_FILE}" "${MOD_ASM_FILE}"

cat > "${MOD_ROOT}/README.md" <<EOF
# ${MOD_SLUG} (${PROJECT_SLUG})

## Build

\`\`\`sh
make mod-build PROJECT=${PROJECT_SLUG} MOD=${MOD_SLUG}
\`\`\`

## Create Patch

\`\`\`sh
make mod-patch PROJECT=${PROJECT_SLUG} MOD=${MOD_SLUG}
\`\`\`
EOF

cat > "${MOD_CONF}" <<EOF
# Mod configuration for scripts/build_mod.sh and scripts/create_mod_patch.sh

PROJECT_SLUG="${PROJECT_SLUG}"
MOD_SLUG="${MOD_SLUG}"

MOD_ASM_FILE="${MOD_ASM_FILE}"
REF_NES_FILE="${REF_NES_FILE}"

OUT_PRG_FILE="${OUT_PRG_FILE}"
OUT_NES_FILE="${OUT_NES_FILE}"
PATCH_FORMAT_DEFAULT="ips"
OUT_PATCH_FILE="${OUT_PATCH_FILE}"
EOF

echo "Created mod scaffold:"
echo "  ${MOD_ROOT}"
echo "Forked asm:"
echo "  ${MOD_ASM_FILE}"
