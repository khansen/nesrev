#!/usr/bin/env bash

test_agent_review_tmux_launcher() {
  python3 "${REPO_ROOT}/tests/agent_review_tmux_test.py"
}

test_agent_review_gold_completion() {
  python3 "${REPO_ROOT}/tests/agent_review_gold_test.py"
}
