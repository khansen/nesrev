#!/usr/bin/env bash

test_assert_exit_preserves_disabled_errexit() {
  set +e
  assert_exit 0 true
  if [[ $- == *e* ]]; then
    fail "assert_exit must not enable errexit when the caller had it disabled"
  fi
  set -e
}

test_assert_exit_preserves_enabled_errexit() {
  assert_exit 0 true
  if [[ $- != *e* ]]; then
    fail "assert_exit must preserve enabled errexit"
  fi
}

test_shell_runner_propagates_nonfinal_command_failures() {
  local fixture_root="${NESREV_TEST_TMPDIR}/runner-fixture"
  mkdir -p "${fixture_root}/tests/shell/cases"
  cp "${REPO_ROOT}/tests/shell/run_all.sh" "${fixture_root}/tests/shell/run_all.sh"
  cp "${REPO_ROOT}/tests/shell/lib.sh" "${fixture_root}/tests/shell/lib.sh"
  cat > "${fixture_root}/tests/shell/cases/nonfinal_test.sh" <<'EOF'
#!/usr/bin/env bash

test_nonfinal_failure() {
  false
  printf 'the command after a failed assertion must not run\n'
}
EOF

  local output rc
  set +e
  output="$(bash "${fixture_root}/tests/shell/run_all.sh" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "the shell runner must propagate a non-final command failure"
  assert_match 'FAIL[[:space:]]+nonfinal::test_nonfinal_failure' "${output}" \
    "the shell runner must identify the failed fixture"
  assert_match 'shell tests: 1 failed of 1' "${output}" \
    "the shell runner must count the failed fixture"
}
