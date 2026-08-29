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
  echo "projects-policy-check: no tracked projects/*/project.conf files found" >&2
  exit 1
fi

python3 "${SCRIPT_DIR}/project_policy_config_check.py" corpus "${REPO_ROOT}"

failed=0
for conf in "${configs[@]}"; do
  slug="${conf#projects/}"
  slug="${slug%/project.conf}"
  echo "=== projects-policy-check: ${slug} ==="
  if ! bash "${SCRIPT_DIR}/project_process_check.sh" "${slug}"; then
    echo "FAIL: ${slug}: project-process-check" >&2
    failed=$((failed + 1))
  fi
  if ! bash "${SCRIPT_DIR}/project_docs_check.sh" "${slug}"; then
    echo "FAIL: ${slug}: project-docs-check" >&2
    failed=$((failed + 1))
  fi
done

if (( failed != 0 )); then
  echo "projects-policy-check: ${failed} gate failure(s) across ${#configs[@]} tracked projects" >&2
  exit 1
fi
echo "projects-policy-check: ${#configs[@]} tracked projects passed"
