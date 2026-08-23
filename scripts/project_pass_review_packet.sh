#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <project_slug> <base-ref> <head-ref>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

cd "${REPO_ROOT}"

SLUG="$1"
BASE_REF="$2"
HEAD_REF="$3"
PROJECT_PATH="projects/${SLUG}"
MAKE_BIN="${MAKE_BIN:-make}"

case "${SLUG}" in
  *[!a-z0-9_-]*|"")
    echo "error: invalid project slug: ${SLUG}" >&2
    exit 2
    ;;
esac

load_project_conf "${SLUG}"

BASE_SHA="$(git rev-parse --verify "${BASE_REF}^{commit}")" || {
  echo "error: base ref is not a commit: ${BASE_REF}" >&2
  exit 2
}
HEAD_SHA="$(git rev-parse --verify "${HEAD_REF}^{commit}")" || {
  echo "error: head ref is not a commit: ${HEAD_REF}" >&2
  exit 2
}
CURRENT_SHA="$(git rev-parse HEAD)"
BASE_SHORT="$(git rev-parse --short "${BASE_SHA}")"
HEAD_SHORT="$(git rev-parse --short "${HEAD_SHA}")"

if [[ "${CURRENT_SHA}" != "${HEAD_SHA}" ]]; then
  echo "error: review head must be checked out before generating a packet" >&2
  echo "current HEAD: ${CURRENT_SHA}" >&2
  echo "review HEAD:  ${HEAD_SHA}" >&2
  exit 2
fi

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "error: tracked working tree changes would make gate evidence stale" >&2
  echo "commit, stash, or discard tracked changes before generating a packet" >&2
  exit 2
fi

if ! git diff --quiet "${BASE_SHA}..${HEAD_SHA}" -- "${PROJECT_PATH}"; then
  RANGE_HAS_PROJECT_DIFF=1
else
  RANGE_HAS_PROJECT_DIFF=0
fi
PROJECT_COMMIT_COUNT="$(git rev-list --count "${BASE_SHA}..${HEAD_SHA}" -- "${PROJECT_PATH}")"

shell_quote() {
  printf "%q" "$1"
}

join_quoted() {
  local item first=1
  for item in "$@"; do
    if (( first )); then
      first=0
    else
      printf ' '
    fi
    shell_quote "${item}"
  done
}

emit_command_block() {
  local title="$1"
  local sha_label="$2"
  local command="$3"
  local output rc

  printf '### %s\n\n' "${title}"
  printf 'State: `%s`\n\n' "${sha_label}"
  printf 'Command:\n\n```sh\n%s\n```\n\n' "${command}"
  set +e
  output="$(cd "${REPO_ROOT}" && bash -o pipefail -c "${command}" 2>&1)"
  rc=$?
  set -e
  printf 'Exit status: `%s`\n\n' "${rc}"
  printf 'Output:\n\n```text\n'
  if [[ -n "${output}" ]]; then
    printf '%s\n' "${output}"
  else
    printf '(no output)\n'
  fi
  printf '```\n\n'
}

path_exists_in_range() {
  local path="$1"
  git cat-file -e "${BASE_SHA}:${path}" 2>/dev/null ||
    git cat-file -e "${HEAD_SHA}:${path}" 2>/dev/null
}

append_path_if_present() {
  local path="$1"
  if path_exists_in_range "${path}"; then
    LEDGER_PATHS+=("${path}")
  fi
}

csv_data_rows_for_ref() {
  local sha="$1"
  local path="$2"
  python3 - "${sha}" "${path}" <<'PY'
import csv
import subprocess
import sys

sha, path = sys.argv[1:]
try:
    text = subprocess.check_output(
        ["git", "show", f"{sha}:{path}"],
        stderr=subprocess.DEVNULL,
        text=True,
    )
except subprocess.CalledProcessError:
    print("0")
    raise SystemExit(0)

reader = csv.reader(text.splitlines())
rows = list(reader)
if not rows:
    print("0")
else:
    print(sum(1 for row in rows[1:] if any(cell.strip() for cell in row)))
PY
}

lxxxx_counts_for_ref() {
  local sha="$1"
  local path="$2"
  python3 - "${sha}" "${path}" <<'PY'
import re
import subprocess
import sys

sha, path = sys.argv[1:]
try:
    text = subprocess.check_output(
        ["git", "show", f"{sha}:{path}"],
        stderr=subprocess.DEVNULL,
        text=True,
    )
except subprocess.CalledProcessError:
    print("NA NA")
    raise SystemExit(0)

defs = len(re.findall(r"^L[0-9A-F]{4,5}:", text, re.M))
occ = len(re.findall(r"\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:", text, re.M))
print(f"{defs} {occ}")
PY
}

signed_delta() {
  local value="$1"
  if (( value >= 0 )); then
    printf '+%d' "${value}"
  else
    printf '%d' "${value}"
  fi
}

format_lxxxx_count() {
  local defs="$1"
  local occ="$2"
  if [[ "${defs}" == "NA" || "${occ}" == "NA" ]]; then
    printf 'not present'
  else
    printf '%s / %s' "${defs}" "${occ}"
  fi
}

LEDGER_PATHS=()
append_path_if_present "${WARN_BASELINE_FILE}"
append_path_if_present "${DOC_ROOT}/inventory/deferrals.csv"
append_path_if_present "${PROGRESS_SCORECARD_FILE}"
append_path_if_present "${RENAMES_FILE}"
append_path_if_present "${SEMANTIC_CLAIMS_FILE}"
append_path_if_present "${CROSSWALK_FILE}"
append_path_if_present "${DOC_ROOT}/inventory/proof_debt_acknowledged.csv"

BASE_RENAME_ROWS="$(csv_data_rows_for_ref "${BASE_SHA}" "${RENAMES_FILE}")"
HEAD_RENAME_ROWS="$(csv_data_rows_for_ref "${HEAD_SHA}" "${RENAMES_FILE}")"
RENAME_ROW_DELTA="$(( HEAD_RENAME_ROWS - BASE_RENAME_ROWS ))"

BASE_LXXXX_COUNTS="$(lxxxx_counts_for_ref "${BASE_SHA}" "${ASM_FILE}")"
HEAD_LXXXX_COUNTS="$(lxxxx_counts_for_ref "${HEAD_SHA}" "${ASM_FILE}")"
BASE_LXXXX_DEFS="${BASE_LXXXX_COUNTS%% *}"
BASE_LXXXX_OCC="${BASE_LXXXX_COUNTS#* }"
HEAD_LXXXX_DEFS="${HEAD_LXXXX_COUNTS%% *}"
HEAD_LXXXX_OCC="${HEAD_LXXXX_COUNTS#* }"
LXXXX_DELTA_TEXT=""
if [[ "${BASE_LXXXX_DEFS}" != "NA" && "${BASE_LXXXX_OCC}" != "NA" &&
      "${HEAD_LXXXX_DEFS}" != "NA" && "${HEAD_LXXXX_OCC}" != "NA" ]]; then
  LXXXX_DEF_DELTA="$(signed_delta "$(( HEAD_LXXXX_DEFS - BASE_LXXXX_DEFS ))")"
  LXXXX_OCC_DELTA="$(signed_delta "$(( HEAD_LXXXX_OCC - BASE_LXXXX_OCC ))")"
  LXXXX_DELTA_TEXT=" (delta ${LXXXX_DEF_DELTA} / ${LXXXX_OCC_DELTA})"
fi
RENAME_ROW_SUMMARY="$(signed_delta "${RENAME_ROW_DELTA}") this range (${BASE_RENAME_ROWS} -> ${HEAD_RENAME_ROWS} total)"
BASE_LXXXX_TEXT="$(format_lxxxx_count "${BASE_LXXXX_DEFS}" "${BASE_LXXXX_OCC}")"
HEAD_LXXXX_TEXT="$(format_lxxxx_count "${HEAD_LXXXX_DEFS}" "${HEAD_LXXXX_OCC}")"
LXXXX_SUMMARY="${BASE_LXXXX_TEXT} -> ${HEAD_LXXXX_TEXT}${LXXXX_DELTA_TEXT}"

VERIFY_CMD="$(
  if [[ -n "${ALLOW_UNRESOLVED_LXXXX:-}" ]]; then
    printf 'ALLOW_UNRESOLVED_LXXXX=%s ' "$(shell_quote "${ALLOW_UNRESOLVED_LXXXX}")"
  fi
  printf '%s project-verify PROJECT=%s' \
    "$(shell_quote "${MAKE_BIN}")" \
    "$(shell_quote "${SLUG}")"
)"
PROCESS_CMD="$(printf '%s project-process-check PROJECT=%s' "$(shell_quote "${MAKE_BIN}")" "$(shell_quote "${SLUG}")")"
DOCS_CMD="$(printf '%s project-docs-check PROJECT=%s' "$(shell_quote "${MAKE_BIN}")" "$(shell_quote "${SLUG}")")"
NEXT_PASS_CMD="$(printf '%s project-next-pass PROJECT=%s' "$(shell_quote "${MAKE_BIN}")" "$(shell_quote "${SLUG}")")"

cat <<EOF
# Project Pass Review Packet

This packet describes a local project-pass review range. Git history and the
project artifacts are authoritative; this file is only a review aid.

## Reviewed State

- Project: \`${SLUG}\`
- Project path: \`${PROJECT_PATH}\`
- Base ref: \`${BASE_REF}\`
- Base SHA: \`${BASE_SHA}\`
- Review head ref: \`${HEAD_REF}\`
- Review head SHA: \`${HEAD_SHA}\`
- Current checkout SHA: \`${CURRENT_SHA}\`
- Review range: \`${BASE_SHORT}..${HEAD_SHORT}\`
- Project diff present: \`${RANGE_HAS_PROJECT_DIFF}\`

Gate evidence below is captured at review head \`${HEAD_SHA}\` unless a
section says otherwise.

## Range Summary

- Project commits in range: \`${PROJECT_COMMIT_COUNT}\`
- Rename ledger rows: \`${RENAME_ROW_SUMMARY}\`
- Unresolved LXXXX labels: \`${LXXXX_SUMMARY}\`

EOF

emit_command_block \
  "Complete Commit List And Diffstat" \
  "range ${BASE_SHORT}..${HEAD_SHORT}" \
  "git log --oneline --stat $(shell_quote "${BASE_SHA}..${HEAD_SHA}") -- $(shell_quote "${PROJECT_PATH}")"

emit_command_block \
  "Project Diff" \
  "range ${BASE_SHORT}..${HEAD_SHORT}" \
  "git diff --stat --patch $(shell_quote "${BASE_SHA}..${HEAD_SHA}") -- $(shell_quote "${PROJECT_PATH}")"

if (( ${#LEDGER_PATHS[@]} > 0 )); then
  emit_command_block \
    "Review Ledger Deltas" \
    "range ${BASE_SHORT}..${HEAD_SHORT}" \
    "git diff --stat --patch $(shell_quote "${BASE_SHA}..${HEAD_SHA}") -- $(join_quoted "${LEDGER_PATHS[@]}")"
else
  cat <<EOF
### Review Ledger Deltas

State: \`range ${BASE_SHORT}..${HEAD_SHORT}\`

No configured review ledgers were present in either endpoint of the range.

EOF
fi

emit_command_block \
  "Proof Debt Signals" \
  "review_head ${HEAD_SHA}" \
  "python3 scripts/proof_debt.py $(shell_quote "${DOC_ROOT}") $(shell_quote "${CROSSWALK_FILE}")"

emit_command_block \
  "Crosswalk Currency" \
  "review_head ${HEAD_SHA}" \
  "python3 scripts/proof_debt.py --crosswalk-only $(shell_quote "${DOC_ROOT}") $(shell_quote "${CROSSWALK_FILE}")"

emit_command_block \
  "Generated Next-Pass Evidence" \
  "review_head ${HEAD_SHA}" \
  "${NEXT_PASS_CMD}"

emit_command_block \
  "Project Verify Gate" \
  "review_head ${HEAD_SHA}" \
  "${VERIFY_CMD}"

emit_command_block \
  "Project Process Gate" \
  "review_head ${HEAD_SHA}" \
  "${PROCESS_CMD}"

emit_command_block \
  "Project Docs Gate" \
  "review_head ${HEAD_SHA}" \
  "${DOCS_CMD}"

cat <<EOF
## Reviewer Instructions

Review \`${BASE_SHORT}..${HEAD_SHORT}\` as a project-pass review. Inspect the
full range, the aggregate signals, the ledger deltas, and the SHA-labelled
gate evidence above. Return \`APPROVED\` only when no blocking issue remains;
otherwise return \`CHANGES_REQUESTED\` with findings ordered by severity.
EOF
