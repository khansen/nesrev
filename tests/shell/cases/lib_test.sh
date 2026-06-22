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
