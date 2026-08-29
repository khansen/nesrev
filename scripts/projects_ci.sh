#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

configs=()
while IFS= read -r conf; do
  [[ -n "${conf}" ]] && configs+=("${conf}")
done < <(git ls-files 'projects/*/project.conf' | sort)
if (( ${#configs[@]} == 0 )); then
  echo "projects-ci: no tracked projects/*/project.conf files found" >&2
  exit 1
fi

failed=0
for conf in "${configs[@]}"; do
  slug="${conf#projects/}"
  slug="${slug%/project.conf}"
  echo "=== projects-ci: ${slug} ==="
  if ! bash "${SCRIPT_DIR}/project_ci.sh" "${slug}"; then
    echo "FAIL: ${slug}: project-ci" >&2
    failed=$((failed + 1))
  fi
done

if (( failed != 0 )); then
  echo "projects-ci: ${failed}/${#configs[@]} projects failed" >&2
  exit 1
fi
echo "projects-ci: ${#configs[@]}/${#configs[@]} projects passed"
