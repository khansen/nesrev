#!/usr/bin/env bash

test_process_friction_receipt_migration_and_ingestion() {
  python3 -B "${REPO_ROOT}/tests/process_friction_test.py"
}
