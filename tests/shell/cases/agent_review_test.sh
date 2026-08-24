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

_write_agent_review_make_stub() {
  local path="$1" mode="$2" counter="$3"
  cat > "${path}" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

mode="__MODE__"
counter="__COUNTER__"
printf 'x\n' >> "${counter}"

head=""
out=""
allow=0
for arg in "$@"; do
  case "${arg}" in
    HEAD=*) head="${arg#HEAD=}" ;;
    OUT=*) out="${arg#OUT=}" ;;
    ALLOW_UNRESOLVED_LXXXX=1) allow=1 ;;
  esac
done

mkdir -p "$(dirname "${out}")"
if [[ "${mode}" == "lxxxx" && "${allow}" == "0" ]]; then
  cat > "${out}" <<PACKET
# Packet

## Reviewed State

- Review head SHA: \`${head}\`

### Project Verify Gate

State: \`review_head ${head}\`

Command:

\`\`\`sh
make project-verify PROJECT=demo
\`\`\`

Exit status: \`2\`

Output:

\`\`\`text
FAIL: 491 distinct LXXXX/LXXXXX labels (1000 refs)
\`\`\`
PACKET
else
  command="make project-verify PROJECT=demo"
  output="FAIL: reference iNES file not found"
  status=2
  if [[ "${mode}" == "lxxxx" ]]; then
    command="ALLOW_UNRESOLVED_LXXXX=1 make project-verify PROJECT=demo"
    output="WARN: 491 distinct LXXXX/LXXXXX labels (1000 refs); allowed by ALLOW_UNRESOLVED_LXXXX=1"
    status=0
  fi
  cat > "${out}" <<PACKET
# Packet

## Reviewed State

- Review head SHA: \`${head}\`

### Project Verify Gate

State: \`review_head ${head}\`

Command:

\`\`\`sh
${command}
\`\`\`

Exit status: \`${status}\`

Output:

\`\`\`text
${output}
\`\`\`
PACKET
fi
EOF
  sed -i.bak \
    -e "s|__MODE__|${mode}|g" \
    -e "s|__COUNTER__|${counter}|g" \
    "${path}"
  rm -f "${path}.bak"
  chmod +x "${path}"
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

_approve_agent_review_run() {
  local repo="$1" run_id="$2"
  local base head
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"

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
    printf 'Verdict: APPROVED\n' > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py approve --review ".agents/runs/${run_id}/review-01.md"
  )
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

test_agent_review_reviewer_prompt_names_required_playbooks() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_reviewer_prompt_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id prompt_text
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-reviewer-prompt"

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

  prompt_text="$(<"${repo}/.agents/runs/${run_id}/prompts/01-ready-for-review-reviewer.md")"
  assert_match 'read `AGENTS.md` and follow the' "${prompt_text}" \
    "review prompt must route reviewers through AGENTS.md"
  assert_match 'Review a committed project pass' "${prompt_text}" \
    "review prompt must name the authoritative AGENTS.md route"
  assert_match 'Mandatory Routing Table' "${prompt_text}" \
    "review prompt must point at the routing table"
  assert_match 'additional routed playbooks' "${prompt_text}" \
    "review prompt must preserve subsystem-specific routing"
}

test_agent_review_archive_writes_project_review_artifact() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_archive_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id archive_path output approved_head
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-archive"
  archive_path="${repo}/projects/demo/docs/reverse_engineering/reviews/pass-7.md"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}" --max-rounds 3
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    printf 'packet-only evidence must not be archived\n' >> ".agents/runs/${run_id}/packet.md"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    printf 'Verdict: CHANGES_REQUESTED\n\nFinding: tighten one name.\n' \
      > ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    local fix_head
    fix_head="$(git rev-parse HEAD)"
    printf 'Disposition: fixed the name.\n' > ".agents/runs/${run_id}/response-01.md"
    _write_agent_packet ".agents/runs/${run_id}/packet-r2.md" "${fix_head}" "Packet r2"
    printf 'second packet body must not be archived\n' >> ".agents/runs/${run_id}/packet-r2.md"
    python3 scripts/agent_review.py reready \
      --response ".agents/runs/${run_id}/response-01.md" \
      --head HEAD \
      --packet ".agents/runs/${run_id}/packet-r2.md"
    printf 'Verdict: APPROVED\n\nNo findings.\n' > ".agents/runs/${run_id}/review-02.md"
    python3 scripts/agent_review.py approve --review ".agents/runs/${run_id}/review-02.md"
    python3 scripts/agent_review.py archive --pass-id 7
  )

  approved_head="$(git -C "${repo}" rev-parse HEAD)"
  output="$(<"${archive_path}")"
  assert_match "# Pass 7 External Review" "${output}"
  assert_match "Pass: \`7\`" "${output}"
  assert_match "Project: \`demo\`" "${output}"
  assert_match "Reviewed scorecard row: pass \`7\`" "${output}"
  assert_match "Archive path: \`projects/demo/docs/reverse_engineering/reviews/pass-7.md\`" "${output}"
  assert_match "Final status: \`APPROVED\`" "${output}"
  assert_match "Review-time range: \`${base}..${approved_head}\`" "${output}"
  assert_match "Review-time head: \`${approved_head}\`" "${output}"
  assert_match "Review-time SHAs are provenance, not the durable key" "${output}"
  assert_match "rebases may orphan them" "${output}"
  assert_match "regenerate packets from the review-time range only while" "${output}"
  assert_match "those SHAs remain reachable" "${output}"
  assert_match "review-01.md" "${output}"
  assert_match "Verdict: CHANGES_REQUESTED" "${output}"
  assert_match "response-01.md" "${output}"
  assert_match "Disposition: fixed the name." "${output}"
  assert_match "review-02.md" "${output}"
  assert_match "Verdict: APPROVED" "${output}"
  if [[ "${output}" =~ packet-only\ evidence\ must\ not\ be\ archived ]]; then
    fail "archive must omit regenerable packet bodies"
  fi
  if [[ "${output}" =~ second\ packet\ body\ must\ not\ be\ archived ]]; then
    fail "archive must omit rereview packet bodies"
  fi

  output="$(git -C "${repo}" status --short --untracked-files=all)"
  assert_match "\\?\\? projects/demo/docs/reverse_engineering/reviews/pass-7.md" "${output}" \
    "archive should be the tracked durable project artifact"
  output="$(git -C "${repo}" status --short -- .agents)"
  if [[ "${output}" =~ \.agents/ ]]; then
    fail "transient agent state must remain ignored"
  fi
}

test_agent_review_archive_requires_approved_state() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_archive_unapproved_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-archive-unapproved"

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

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py archive --pass-id 7 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "archive must not run before approval"
  assert_match "archive requires APPROVED" "${output}"
}

test_agent_review_init_rejects_unsafe_project() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_unsafe_project_repo"
  _init_agent_review_repo "${repo}"

  local base head output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py init \
    --project ../../escape --base "${base}" --head "${head}" --run-id unsafe-project 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "init must reject unsafe project path components"
  assert_match "project may contain only" "${output}"
}

test_agent_review_archive_rejects_tampered_project() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_archive_tampered_project_repo"
  _init_agent_review_repo "${repo}"

  local run_id output rc escape_path
  run_id="demo-pass-archive-tampered-project"
  escape_path="$(cd "${repo}/.." && pwd)/escape/docs/reverse_engineering/reviews/pass-7.md"
  rm -f "${escape_path}"

  _approve_agent_review_run "${repo}" "${run_id}"
  (
    cd "${repo}"
    python3 - <<'PY'
import json
from pathlib import Path

path = Path(".agents/current.json")
data = json.loads(path.read_text())
data["project"] = "../../escape"
path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
PY
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py archive --pass-id 7 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "state reads must reject unsafe project values"
  assert_match "invalid project in current.json" "${output}"
  if [[ -e "${escape_path}" ]]; then
    fail "tampered project must not write archive outside the repo"
  fi
}

test_agent_review_archive_rejects_outside_output_path() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_archive_outside_out_repo"
  _init_agent_review_repo "${repo}"

  local run_id output rc escape_path
  run_id="demo-pass-archive-outside-out"
  escape_path="$(cd "${repo}/../.." && pwd)/agent-review-out-escape.md"
  rm -f "${escape_path}"

  _approve_agent_review_run "${repo}" "${run_id}"

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py archive \
    --pass-id 7 --out ../../agent-review-out-escape.md 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "archive must reject output paths outside the repo"
  assert_match "archive output must stay inside repository" "${output}"
  if [[ -e "${escape_path}" ]]; then
    fail "archive --out must not write outside the repo"
  fi
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

test_agent_review_ready_does_not_auto_relax_explicit_lxxxx_packet() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_explicit_lxxxx_packet_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-explicit-lxxxx"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass with an explicit packet.\n' > ".agents/runs/${run_id}/implementation.md"
    cat > ".agents/runs/${run_id}/packet.md" <<EOF
# Packet

## Reviewed State

- Review head SHA: \`${head}\`

### Project Verify Gate

State: \`review_head ${head}\`

Exit status: \`2\`

Output:

\`\`\`text
FAIL: 491 distinct LXXXX/LXXXXX labels (1000 refs)
\`\`\`
EOF
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py ready \
    --note ".agents/runs/${run_id}/implementation.md" \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "explicit LXXXX-failed packets must not auto-relax"
  assert_match "packet Project Verify Gate exit status is nonzero: 2" "${output}"
  assert_eq "$(_json_field "${repo}" "status")" "IMPLEMENTING" \
    "explicit failed packet must not advance state"
  assert_eq "$(_json_field "${repo}" "allow_unresolved_lxxxx")" "False" \
    "explicit failed packet must not enable relaxed verify state"
  if [[ "${output}" =~ strict\ packet\ verify\ failed\ on\ unresolved\ LXXXX\ labels ]]; then
    fail "explicit packet path must not emit generated-packet retry diagnostics"
  fi
}

test_agent_review_ready_auto_relaxes_generated_lxxxx_packet() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_auto_lxxxx_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output counter packet
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-auto-lxxxx"
  counter="${NESREV_TEST_TMPDIR}/auto-lxxxx-make-count"
  mkdir -p "${NESREV_TEST_TMPDIR}/auto-lxxxx-bin"
  _write_agent_review_make_stub \
    "${NESREV_TEST_TMPDIR}/auto-lxxxx-bin/make" \
    lxxxx \
    "${counter}"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass with relaxed verify.\n' > ".agents/runs/${run_id}/implementation.md"
  )

  output="$(
    cd "${repo}" && PATH="${NESREV_TEST_TMPDIR}/auto-lxxxx-bin:${PATH}" \
      python3 scripts/agent_review.py ready \
        --note ".agents/runs/${run_id}/implementation.md" \
        --generate-packet 2>&1
  )"

  assert_match "strict packet verify failed on unresolved LXXXX labels" "${output}" \
    "generated strict LXXXX failure should trigger a relaxed retry"
  assert_eq "$(_json_field "${repo}" "status")" "READY_FOR_REVIEW" \
    "auto-relaxed packet should still hand off for review"
  assert_eq "$(_json_field "${repo}" "allow_unresolved_lxxxx")" "True" \
    "auto-relaxed packet mode must persist in state for reready"
  assert_eq "$(wc -l <"${counter}" | tr -d ' ')" "2" \
    "ready should generate once strict, then once relaxed"

  packet="${repo}/.agents/runs/${run_id}/packet-round-01.md"
  output="$(<"${packet}")"
  assert_match "ALLOW_UNRESOLVED_LXXXX=1 make project-verify PROJECT=demo" "${output}" \
    "final packet must show the relaxed verify command"
  assert_match "Exit status: \`0\`" "${output}" \
    "final packet must pass verify preflight"
}

test_agent_review_ready_does_not_auto_relax_other_generated_verify_failures() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_no_auto_relax_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output rc counter
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-no-auto-relax"
  counter="${NESREV_TEST_TMPDIR}/no-auto-relax-make-count"
  mkdir -p "${NESREV_TEST_TMPDIR}/no-auto-relax-bin"
  _write_agent_review_make_stub \
    "${NESREV_TEST_TMPDIR}/no-auto-relax-bin/make" \
    missing_ref \
    "${counter}"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    printf 'Implemented demo pass.\n' > ".agents/runs/${run_id}/implementation.md"
  )

  set +e
  output="$(
    cd "${repo}" && PATH="${NESREV_TEST_TMPDIR}/no-auto-relax-bin:${PATH}" \
      python3 scripts/agent_review.py ready \
        --note ".agents/runs/${run_id}/implementation.md" \
        --generate-packet 2>&1
  )"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "non-LXXXX verify failures must still block handoff"
  assert_match "packet Project Verify Gate exit status is nonzero: 2" "${output}"
  assert_eq "$(_json_field "${repo}" "status")" "IMPLEMENTING" \
    "failed generated packet must not advance state"
  assert_eq "$(_json_field "${repo}" "allow_unresolved_lxxxx")" "False" \
    "non-LXXXX failures must not enable relaxed verify state"
  assert_eq "$(wc -l <"${counter}" | tr -d ' ')" "1" \
    "ready should not retry unrelated verify failures"
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
