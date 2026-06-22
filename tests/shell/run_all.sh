#!/usr/bin/env bash
# Shell-test runner. Discovers tests/shell/cases/*_test.sh, sources each in a
# subshell with a clean tmpdir, and reports pass/fail.
#
# Each test file is expected to define one or more `test_*` bash functions.
# The runner iterates them in lexical order. Tests indicate failure by:
#   - returning non-zero from the function (set -e is enabled), or
#   - calling `fail "<message>"`.
# Helpers (assert_eq, assert_match, assert_exit, etc.) live in lib.sh.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
export REPO_ROOT SCRIPT_DIR

# shellcheck source=lib.sh
source "${SCRIPT_DIR}/lib.sh"

shopt -s nullglob
test_files=("${SCRIPT_DIR}/cases/"*_test.sh)
if (( ${#test_files[@]} == 0 )); then
  echo "no test files in tests/shell/cases/" >&2
  exit 2
fi

total=0
failed=0
declare -a failures

for file in "${test_files[@]}"; do
  test_name_base="$(basename "${file%_test.sh}")"
  # Require successful sourcing: any syntax or runtime error at source time
  # is a hard failure for the file, not a silent skip.
  source_stderr_file="$(mktemp -t "nesrev_source_stderr.XXXXXX")"
  if bash -c 'set -euo pipefail; source "$1"' _ "${file}" >/dev/null 2>"${source_stderr_file}"; then
    source_rc=0
  else
    source_rc=$?
  fi
  source_stderr="$(<"${source_stderr_file}")"
  rm -f "${source_stderr_file}"
  if (( source_rc != 0 )); then
    total=$((total + 1))
    failed=$((failed + 1))
    failures+=("${test_name_base}::<source>")
    echo "FAIL  ${test_name_base}::<source> (exit ${source_rc}; file did not source cleanly)"
    if [[ -n "${source_stderr}" ]]; then
      echo "${source_stderr}" | sed 's/^/      | /' >&2
    fi
    continue
  fi
  # Discover test_* functions in a clean subshell that sources the file.
  funcs=$(bash -c 'set -u; source "$1"; compgen -A function test_ | sort' _ "${file}" 2>/dev/null)
  if [[ -z "${funcs}" ]]; then
    total=$((total + 1))
    failed=$((failed + 1))
    failures+=("${test_name_base}::<no-tests>")
    echo "FAIL  ${test_name_base}::<no-tests> (file sources cleanly but defines no test_* functions)"
    continue
  fi
  for fn in $funcs; do
    total=$((total + 1))
    case_label="${test_name_base}::${fn}"
    tmpdir="$(mktemp -d -t "nesrev_shtest.XXXXXX")"
    if (
      set -euo pipefail
      cd "${REPO_ROOT}"
      export NESREV_TEST_TMPDIR="${tmpdir}"
      # shellcheck source=lib.sh
      source "${SCRIPT_DIR}/lib.sh"
      # shellcheck disable=SC1090
      source "${file}"
      "${fn}"
    ) >"${tmpdir}/stdout" 2>"${tmpdir}/stderr"; then
      echo "PASS  ${case_label}"
    else
      rc=$?
      failed=$((failed + 1))
      failures+=("${case_label}")
      echo "FAIL  ${case_label} (exit ${rc})"
      sed 's/^/      | /' "${tmpdir}/stderr" >&2 || true
      sed 's/^/      | /' "${tmpdir}/stdout" || true
    fi
    rm -rf "${tmpdir}"
  done
done

echo
if (( failed == 0 )); then
  echo "shell tests: ${total} passed"
  exit 0
fi
echo "shell tests: ${failed} failed of ${total}" >&2
for f in "${failures[@]}"; do
  echo "  - ${f}" >&2
done
exit 1
