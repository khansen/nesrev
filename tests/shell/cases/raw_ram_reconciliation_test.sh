#!/usr/bin/env bash

test_raw_ram_reconciliation_compares_facts_and_preserves_authored_fields() {
  python3 -B "${REPO_ROOT}/tests/raw_ram_reconciliation_test.py"
}
