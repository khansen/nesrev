#!/usr/bin/env bash

test_raw_ram_review_validates_inputs_without_losing_authored_rows() {
  python3 -B "${REPO_ROOT}/tests/raw_ram_review_test.py"
}
