#!/usr/bin/env bash

test_fceux_local_profile() {
  python3 -B "${REPO_ROOT}/scripts/patches/fceux/test_profile.py"
}
