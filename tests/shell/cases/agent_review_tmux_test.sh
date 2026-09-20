#!/usr/bin/env bash

test_agent_review_tmux_launcher() {
  python3 "${REPO_ROOT}/tests/agent_review_tmux_test.py"
}

test_agent_review_gold_completion() {
  python3 "${REPO_ROOT}/tests/agent_review_gold_test.py"
}

test_agent_review_scoped_permissions() {
  python3 "${REPO_ROOT}/tests/agent_review_permissions_test.py"
}

test_agent_review_artifact_import() {
  python3 "${REPO_ROOT}/tests/agent_review_artifact_test.py"
}

test_agent_review_project_git() {
  python3 "${REPO_ROOT}/tests/agent_review_git_test.py"
}
