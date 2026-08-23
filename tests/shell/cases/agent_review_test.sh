#!/usr/bin/env bash
# Tests for the local agent-review handoff state machine.

AGENT_REVIEW_SCRIPT="${REPO_ROOT}/scripts/agent_review.py"

_init_agent_review_repo() {
  local repo="$1"
  mkdir -p "${repo}/scripts" "${repo}/projects/demo/asm"
  cp "${AGENT_REVIEW_SCRIPT}" "${repo}/scripts/agent_review.py"
  chmod +x "${repo}/scripts/agent_review.py"

  git -C "${repo}" init -q
  git -C "${repo}" config user.email "tests@example.invalid"
  git -C "${repo}" config user.name "Tests"
  git -C "${repo}" config commit.gpgsign false

  cat > "${repo}/projects/demo/asm/demo.asm" <<'EOF'
L1000:
  RTS
EOF
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Base pass"

  cat > "${repo}/projects/demo/asm/demo.asm" <<'EOF'
RunDemo:
  RTS
EOF
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Demo pass"
}

_write_agent_notify_stub() {
  local path="$1" log="$2"
  cat > "${path}" <<EOF
#!/usr/bin/env bash
set -euo pipefail
printf '%s|%s|%s\n' "\$1" "\$2" "\$3" >> "${log}"
printf 'env:%s|%s|%s\n' "\${AGENT_REVIEW_ROLE}" "\${AGENT_REVIEW_STATUS}" "\${AGENT_REVIEW_RUN_ID}" >> "${log}"
cat "\$3" >> "${log}"
EOF
  chmod +x "${path}"
}

_write_agent_packet() {
  local path="$1" head="$2" title="${3:-Packet}" verify_status="${4:-0}"
  cat > "${path}" <<EOF
# ${title}

## Reviewed State

- Review head SHA: \`${head}\`

### Project Verify Gate

State: \`review_head ${head}\`

Exit status: \`${verify_status}\`
EOF
}

_json_field() {
  local repo="$1" field="$2"
  python3 - "${repo}" "${field}" <<'PY'
import json
import sys
from pathlib import Path

repo, field = sys.argv[1:]
data = json.loads((Path(repo) / ".agents/current.json").read_text())
value = data
for part in field.split("."):
    value = value[part]
print(value)
PY
}

_wait_for_log() {
  local log="$1" pattern="$2" label="$3"
  local i text
  for i in {1..50}; do
    text="$(cat "${log}" 2>/dev/null || true)"
    if [[ "${text}" =~ ${pattern} ]]; then
      return 0
    fi
    sleep 0.1
  done
  fail "timed out waiting for ${label}"
}

test_agent_review_relay_round_trip_between_roles() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id log notify
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-1"
  log="${NESREV_TEST_TMPDIR}/notify.log"
  notify="${NESREV_TEST_TMPDIR}/notify.sh"
  _write_agent_notify_stub "${notify}" "${log}"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 3
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    python3 scripts/agent_review.py watch --role reviewer --notify "${notify}" --once

    printf 'Verdict: CHANGES_REQUESTED\n\nFinding 1.\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py watch --role implementer --notify "${notify}" --once

    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    local fix_head
    fix_head="$(git rev-parse HEAD)"
    printf 'Disposition: fixed finding 1.\n' > ".agents/runs/${run_id}/response-01.md"
    _write_agent_packet ".agents/runs/${run_id}/packet-r2.md" "${fix_head}" "Packet r2"
    python3 scripts/agent_review.py reready \
      --response ".agents/runs/${run_id}/response-01.md" \
      --head HEAD \
      --packet ".agents/runs/${run_id}/packet-r2.md"
    python3 scripts/agent_review.py watch --role reviewer --notify "${notify}" --once

    printf 'Verdict: APPROVED\n' > ".agents/runs/${run_id}/review-02.md"
    python3 scripts/agent_review.py approve --review ".agents/runs/${run_id}/review-02.md"
    python3 scripts/agent_review.py watch --role implementer --notify "${notify}" --once
  )

  local log_text
  log_text="$(<"${log}")"
  assert_match "reviewer\\|READY_FOR_REVIEW\\|" "${log_text}" \
    "watcher must notify reviewer for initial review"
  assert_match "implementer\\|CHANGES_REQUESTED\\|" "${log_text}" \
    "watcher must return findings to implementer"
  assert_match "reviewer\\|READY_FOR_REREVIEW\\|" "${log_text}" \
    "watcher must notify reviewer for rereview"
  assert_match "implementer\\|APPROVED\\|" "${log_text}" \
    "watcher must return approval to implementer"
  assert_match "Packet: .agents/runs/${run_id}/packet-r2.md" "${log_text}" \
    "rereview prompt must point at the refreshed packet"
  assert_eq "$(_json_field "${repo}" "status")" "APPROVED" \
    "state should terminate at APPROVED"
  assert_eq "$(_json_field "${repo}" "round")" "2" \
    "rereview should increment the round"
}

test_agent_review_prompt_uses_external_script_path_when_repo_lacks_tool() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_external_tool_repo"
  local external_script="${NESREV_TEST_TMPDIR}/agent_review_external.py"
  mkdir -p "${repo}/projects/demo/asm"
  cp "${AGENT_REVIEW_SCRIPT}" "${external_script}"
  chmod +x "${external_script}"

  git -C "${repo}" init -q
  git -C "${repo}" config user.email "tests@example.invalid"
  git -C "${repo}" config user.name "Tests"
  git -C "${repo}" config commit.gpgsign false

  cat > "${repo}/projects/demo/asm/demo.asm" <<'EOF'
L1000:
  RTS
EOF
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Base pass"

  cat > "${repo}/projects/demo/asm/demo.asm" <<'EOF'
RunDemo:
  RTS
EOF
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Demo pass"

  local base head run_id prompt_text
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-external-tool"

  (
    cd "${repo}"
    python3 "${external_script}" init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 "${external_script}" ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
  )

  prompt_text="$(<"${repo}/.agents/runs/${run_id}/prompts/01-ready-for-review-reviewer.md")"
  assert_match "python3 ${external_script} approve --review" "${prompt_text}" \
    "review prompt must use the external tool path when the repo lacks scripts/agent_review.py"
  assert_match "python3 ${external_script} request-changes --review" "${prompt_text}" \
    "request-changes hint must use the external tool path too"
}

test_agent_review_watch_loop_handles_multiple_turns() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_loop_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id log notify watcher_pid
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-loop"
  log="${NESREV_TEST_TMPDIR}/loop-notify.log"
  notify="${NESREV_TEST_TMPDIR}/loop-notify.sh"
  _write_agent_notify_stub "${notify}" "${log}"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 3
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    python3 scripts/agent_review.py watch --role reviewer \
      --notify "${notify}" --timeout 10 --interval 0.1 \
      >"${NESREV_TEST_TMPDIR}/watcher.stdout" \
      2>"${NESREV_TEST_TMPDIR}/watcher.stderr" &
    echo "$!" > "${NESREV_TEST_TMPDIR}/watcher.pid"
  )
  watcher_pid="$(<"${NESREV_TEST_TMPDIR}/watcher.pid")"

  _wait_for_log "${log}" "reviewer\\|READY_FOR_REVIEW\\|" "initial reviewer turn"

  (
    cd "${repo}"
    printf 'Verdict: CHANGES_REQUESTED\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    local fix_head
    fix_head="$(git rev-parse HEAD)"
    printf 'Disposition: fixed.\n' > ".agents/runs/${run_id}/response-01.md"
    _write_agent_packet ".agents/runs/${run_id}/packet-r2.md" "${fix_head}" "Packet r2"
    python3 scripts/agent_review.py reready \
      --response ".agents/runs/${run_id}/response-01.md" \
      --head HEAD \
      --packet ".agents/runs/${run_id}/packet-r2.md"
  )

  _wait_for_log "${log}" "reviewer\\|READY_FOR_REREVIEW\\|" "rereview turn"
  kill "${watcher_pid}" 2>/dev/null || true
  wait "${watcher_pid}" 2>/dev/null || true
}

test_agent_review_watch_waits_for_state_when_started_before_init() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_preinit_watch_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id log notify watcher_pid
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-preinit-watch"
  log="${NESREV_TEST_TMPDIR}/preinit-watch-notify.log"
  notify="${NESREV_TEST_TMPDIR}/preinit-watch-notify.sh"
  _write_agent_notify_stub "${notify}" "${log}"

  (
    cd "${repo}"
    python3 scripts/agent_review.py watch --role reviewer \
      --notify "${notify}" --timeout 5 --interval 0.1 \
      >"${NESREV_TEST_TMPDIR}/preinit-watcher.stdout" \
      2>"${NESREV_TEST_TMPDIR}/preinit-watcher.stderr" &
    echo "$!" > "${NESREV_TEST_TMPDIR}/preinit-watcher.pid"
  )
  watcher_pid="$(<"${NESREV_TEST_TMPDIR}/preinit-watcher.pid")"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
  )

  _wait_for_log "${log}" "reviewer\\|READY_FOR_REVIEW\\|" "pre-init watcher turn"
  kill "${watcher_pid}" 2>/dev/null || true
  wait "${watcher_pid}" 2>/dev/null || true
}

test_agent_review_watch_does_not_repeat_same_turn() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_repeat_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id log notify output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-repeat"
  log="${NESREV_TEST_TMPDIR}/repeat-notify.log"
  notify="${NESREV_TEST_TMPDIR}/repeat-notify.sh"
  _write_agent_notify_stub "${notify}" "${log}"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    python3 scripts/agent_review.py watch --role reviewer --notify "${notify}" --once
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py watch --role reviewer --notify "${notify}" --once 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "3" "watch should not notify twice for the same turn"
  assert_match "no new reviewer turn" "${output}"
}

test_agent_review_round_cap_exhausts_before_rereview() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_round_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-round"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 1
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    printf 'Verdict: CHANGES_REQUESTED\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    printf 'Disposition: fixed.\n' > ".agents/runs/${run_id}/response-01.md"
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py reready \
    --response ".agents/runs/${run_id}/response-01.md" --head HEAD \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "1" "reready past max_rounds must stop the loop"
  assert_match "review rounds exhausted" "${output}"
  assert_eq "$(_json_field "${repo}" "status")" "REVIEW_ROUNDS_EXHAUSTED" \
    "state must record exhausted review rounds"
}

test_agent_review_reready_requires_fresh_packet_for_new_head() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_stale_packet_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-stale-packet"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 3
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    printf 'Verdict: CHANGES_REQUESTED\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    printf 'Disposition: fixed.\n' > ".agents/runs/${run_id}/response-01.md"
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py reready \
    --response ".agents/runs/${run_id}/response-01.md" --head HEAD 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "reready must not reuse a stale packet"
  assert_match "reready requires --packet or --generate-packet" "${output}"
}

test_agent_review_reready_rejects_packet_for_previous_head() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_stale_packet_explicit_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-stale-packet-explicit"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 3
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    printf 'Verdict: CHANGES_REQUESTED\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    printf 'Disposition: fixed.\n' > ".agents/runs/${run_id}/response-01.md"
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py reready \
    --response ".agents/runs/${run_id}/response-01.md" \
    --head HEAD \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "reready must reject a packet for the previous head"
  assert_match "packet review head does not match state" "${output}"
}

test_agent_review_ready_rejects_packet_with_failed_verify_gate() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_failed_verify_packet_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-failed-verify"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet" 2
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py ready \
    --note ".agents/runs/${run_id}/implementation.md" \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "ready must reject packets with failed verify evidence"
  assert_match "packet Project Verify Gate exit status is nonzero: 2" "${output}"
}

test_agent_review_ready_rejects_packet_without_verify_gate() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_missing_verify_packet_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-missing-verify"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    cat > ".agents/runs/${run_id}/packet.md" <<EOF
# Packet

## Reviewed State

- Review head SHA: \`${head}\`
EOF
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py ready \
    --note ".agents/runs/${run_id}/implementation.md" \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "ready must reject packets without verify evidence"
  assert_match "packet does not contain Project Verify Gate" "${output}"
}

test_agent_review_reready_rejects_process_paths_added_by_fix() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_reready_process_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-process-fix"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 3
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    printf 'Verdict: CHANGES_REQUESTED\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    mkdir -p agent_playbook
    printf '# process rule\n' > agent_playbook/RULES.md
    printf '#!/usr/bin/env bash\n' > scripts/some_gate.sh
    git add agent_playbook/RULES.md scripts/some_gate.sh
    git commit -q -m "Process fix in pass response"
    printf 'Disposition: fixed.\n' > ".agents/runs/${run_id}/response-01.md"
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py reready \
    --response ".agents/runs/${run_id}/response-01.md" --head HEAD \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "reready must reject process paths added by a fix commit"
  assert_match "range touches process/tooling paths" "${output}"
  assert_match "agent_playbook/RULES.md" "${output}"
  assert_match "scripts/some_gate.sh" "${output}"
}

test_agent_review_rejects_review_without_required_verdict() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_verdict_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-verdict"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    printf 'Looks fine, but no machine verdict.\n' > ".agents/runs/${run_id}/review-01.md"
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py approve \
    --review ".agents/runs/${run_id}/review-01.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "approve must require an explicit APPROVED verdict"
  assert_match "review file must contain 'Verdict: APPROVED'" "${output}"
}

test_agent_review_rejects_tampered_run_id_on_read() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_bad_runid_repo"
  _init_agent_review_repo "${repo}"

  local base head output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id good-run
    python3 - <<'PY'
import json
from pathlib import Path

path = Path(".agents/current.json")
data = json.loads(path.read_text())
data["run_id"] = "../escape"
path.write_text(json.dumps(data) + "\n")
PY
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py status 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "state reads must reject unsafe run_id values"
  assert_match "invalid run_id in current.json" "${output}"
}

test_agent_review_init_writes_runtime_excludes() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_exclude_repo"
  _init_agent_review_repo "${repo}"

  local base head output
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"

  (cd "${repo}" && python3 scripts/agent_review.py init \
    --project demo --base "${base}" --head "${head}" --run-id exclude-run)

  output="$(git -C "${repo}" status --short -- .agents)"
  assert_eq "${output}" "" "agent runtime state must be ignored even without tracked .gitignore"

  output="$(git -C "${repo}" check-ignore .agents/current.json .agents/runs/exclude-run/prompts)"
  assert_match ".agents/current.json" "${output}"
  assert_match ".agents/runs/exclude-run/prompts" "${output}"
}

test_agent_review_init_rejects_process_ranges() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_process_repo"
  mkdir -p "${repo}/scripts"
  cp "${AGENT_REVIEW_SCRIPT}" "${repo}/scripts/agent_review.py"

  git -C "${repo}" init -q
  git -C "${repo}" config user.email "tests@example.invalid"
  git -C "${repo}" config user.name "Tests"
  git -C "${repo}" config commit.gpgsign false
  printf 'base\n' > "${repo}/README.md"
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Base"
  printf '#!/usr/bin/env bash\n' > "${repo}/scripts/process_tool.sh"
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Process change"

  local base head output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py init \
    --project demo --base "${base}" --head "${head}" --run-id process-range 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "project-pass handoff must reject process ranges"
  assert_match "range touches process/tooling paths" "${output}"
  assert_match "scripts/process_tool.sh" "${output}"

  (cd "${repo}" && python3 scripts/agent_review.py init \
    --project demo --base "${base}" --head "${head}" --run-id process-range \
    --allow-process-range)
}
