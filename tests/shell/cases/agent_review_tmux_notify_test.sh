#!/usr/bin/env bash
# Tests for the tmux notifier used by the local agent-review handoff loop.

AGENT_REVIEW_TMUX_NOTIFY_SCRIPT="${REPO_ROOT}/scripts/agent_review_tmux_notify.sh"

_write_tmux_stub() {
  local path="$1" log="$2"
  cat > "${path}" <<EOF
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "\$*" >> "${log}"
if [[ "\${1:-}" == "display-message" ]]; then
  if [[ "\${TMUX_STUB_FAIL_TARGET:-}" == "1" ]]; then
    echo "can't find pane: \${4:-}" >&2
    exit 1
  fi
  if [[ "\${TMUX_STUB_EMPTY_TARGET:-}" == "1" ]]; then
    exit 0
  fi
  printf '%s\n' "\${4:-%1}"
  exit 0
fi
if [[ "\${1:-}" == "load-buffer" ]]; then
  last=""
  for arg in "\$@"; do
    last="\${arg}"
  done
  cat "\${last}" > "${log}.buffer"
fi
if [[ "\${1:-}" == "paste-buffer" && "\${TMUX_STUB_FAIL_PASTE:-}" == "1" ]]; then
  echo "can't find pane: \${7:-}" >&2
  exit 1
fi
EOF
  chmod +x "${path}"
}

test_agent_review_tmux_notify_sends_prompt_to_role_target() {
  local stub="${NESREV_TEST_TMPDIR}/tmux-stub.sh"
  local log="${NESREV_TEST_TMPDIR}/tmux.log"
  local prompt="${NESREV_TEST_TMPDIR}/prompt.md"
  local output log_text buffer_text
  _write_tmux_stub "${stub}" "${log}"
  printf 'review this packet\nsecond line\n' > "${prompt}"

  output="$(
    AGENT_REVIEW_TMUX_BIN="${stub}" \
    AGENT_REVIEW_TMUX_REVIEWER="%42" \
      "${AGENT_REVIEW_TMUX_NOTIFY_SCRIPT}" reviewer READY_FOR_REVIEW "${prompt}"
  )"

  log_text="$(<"${log}")"
  buffer_text="$(<"${log}.buffer")"
  assert_match "display-message -p -t %42" "${log_text}"
  assert_match "load-buffer -b agent-review-reviewer-[0-9]+ ${prompt}" "${log_text}"
  assert_match "paste-buffer -p -d -b agent-review-reviewer-[0-9]+ -t %42" "${log_text}"
  assert_match "send-keys -t %42 Enter" "${log_text}"
  assert_eq "${buffer_text}" $'review this packet\nsecond line' \
    "tmux notifier must load the prompt file into the tmux buffer"
  assert_match "sent READY_FOR_REVIEW prompt to reviewer pane %42" "${output}"
}

test_agent_review_tmux_notify_can_paste_without_submitting() {
  local stub="${NESREV_TEST_TMPDIR}/tmux-stub-nosubmit.sh"
  local log="${NESREV_TEST_TMPDIR}/tmux-nosubmit.log"
  local prompt="${NESREV_TEST_TMPDIR}/prompt-nosubmit.md"
  local log_text
  _write_tmux_stub "${stub}" "${log}"
  printf 'changes requested\n' > "${prompt}"

  AGENT_REVIEW_TMUX_BIN="${stub}" \
  AGENT_REVIEW_TMUX_IMPLEMENTER="%7" \
  AGENT_REVIEW_TMUX_SUBMIT=0 \
    "${AGENT_REVIEW_TMUX_NOTIFY_SCRIPT}" implementer CHANGES_REQUESTED "${prompt}"

  log_text="$(<"${log}")"
  assert_match "paste-buffer -p -d -b agent-review-implementer-[0-9]+ -t %7" "${log_text}"
  if [[ "${log_text}" =~ send-keys ]]; then
    fail "AGENT_REVIEW_TMUX_SUBMIT=0 must not send Enter"
  fi
}

test_agent_review_tmux_notify_rejects_invalid_target_before_paste() {
  local stub="${NESREV_TEST_TMPDIR}/tmux-stub-invalid-target.sh"
  local log="${NESREV_TEST_TMPDIR}/tmux-invalid-target.log"
  local prompt="${NESREV_TEST_TMPDIR}/prompt-invalid-target.md"
  local output rc log_text
  _write_tmux_stub "${stub}" "${log}"
  printf 'review\n' > "${prompt}"

  set +e
  output="$(
    AGENT_REVIEW_TMUX_BIN="${stub}" \
    AGENT_REVIEW_TMUX_REVIEWER="%404" \
    TMUX_STUB_EMPTY_TARGET=1 \
      "${AGENT_REVIEW_TMUX_NOTIFY_SCRIPT}" reviewer READY_FOR_REVIEW "${prompt}" 2>&1
  )"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "empty tmux pane lookup should reject before loading a prompt"
  assert_match "tmux target not found: %404" "${output}"
  log_text="$(<"${log}")"
  assert_match "display-message -p -t %404" "${log_text}"
  if [[ "${log_text}" =~ load-buffer|paste-buffer ]]; then
    fail "invalid pane target must fail before loading or pasting the prompt"
  fi
}

test_agent_review_tmux_notify_cleans_buffer_after_paste_failure() {
  local stub="${NESREV_TEST_TMPDIR}/tmux-stub-paste-failure.sh"
  local log="${NESREV_TEST_TMPDIR}/tmux-paste-failure.log"
  local prompt="${NESREV_TEST_TMPDIR}/prompt-paste-failure.md"
  local output rc log_text
  _write_tmux_stub "${stub}" "${log}"
  printf 'review\n' > "${prompt}"

  set +e
  output="$(
    AGENT_REVIEW_TMUX_BIN="${stub}" \
    AGENT_REVIEW_TMUX_REVIEWER="%500" \
    TMUX_STUB_FAIL_PASTE=1 \
      "${AGENT_REVIEW_TMUX_NOTIFY_SCRIPT}" reviewer READY_FOR_REVIEW "${prompt}" 2>&1
  )"
  rc=$?
  set -e

  assert_eq "${rc}" "1" "tmux paste failure should propagate to the watcher"
  assert_match "can't find pane" "${output}"
  log_text="$(<"${log}")"
  assert_match "load-buffer -b agent-review-reviewer-[0-9]+ ${prompt}" "${log_text}"
  assert_match "paste-buffer -p -d -b agent-review-reviewer-[0-9]+ -t %500" "${log_text}"
  assert_match "delete-buffer -b agent-review-reviewer-[0-9]+" "${log_text}"
}

test_agent_review_tmux_notify_requires_role_target() {
  local stub="${NESREV_TEST_TMPDIR}/tmux-stub-missing-target.sh"
  local log="${NESREV_TEST_TMPDIR}/tmux-missing-target.log"
  local prompt="${NESREV_TEST_TMPDIR}/prompt-missing-target.md"
  local output rc
  _write_tmux_stub "${stub}" "${log}"
  printf 'review\n' > "${prompt}"

  set +e
  output="$(
    AGENT_REVIEW_TMUX_BIN="${stub}" \
      "${AGENT_REVIEW_TMUX_NOTIFY_SCRIPT}" reviewer READY_FOR_REVIEW "${prompt}" 2>&1
  )"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "notifier must reject missing reviewer target"
  assert_match "set AGENT_REVIEW_TMUX_REVIEWER" "${output}"
}
