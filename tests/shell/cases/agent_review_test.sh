#!/usr/bin/env bash
# Tests for the local agent-review handoff state machine.

AGENT_REVIEW_SCRIPT="${REPO_ROOT}/scripts/agent_review.py"

_init_agent_review_repo() {
  local repo="$1"
  mkdir -p "${repo}/scripts" "${repo}/tests" "${repo}/projects/demo/asm"
  cp "${AGENT_REVIEW_SCRIPT}" "${repo}/scripts/agent_review.py"
  cp "${REPO_ROOT}/scripts/process_friction.py" "${repo}/scripts/process_friction.py"
  cp "${REPO_ROOT}/scripts/review_packet_evidence.py" "${repo}/scripts/review_packet_evidence.py"
  cp "${REPO_ROOT}/tests/review_packet_fixture.py" "${repo}/tests/review_packet_fixture.py"
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
  python3 "${REPO_ROOT}/tests/review_packet_fixture.py" --output "${path}" \
    --head "${head}" --title "${title}" --verify-exit "${verify_status}" \
    --process-exit "${5:-0}" --docs-exit "${6:-0}"
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
command="make project-verify PROJECT=demo"
output="FAIL: reference iNES file not found"
status=2
if [[ "${mode}" == "ok" ]]; then
  output="OK: binary identity preserved"
  status=0
elif [[ "${mode}" == "lxxxx" && "${allow}" == 0 ]]; then
  output="FAIL: 491 distinct LXXXX/LXXXXX labels (1000 refs)"
elif [[ "${mode}" == "lxxxx" ]]; then
  command="ALLOW_UNRESOLVED_LXXXX=1 make project-verify PROJECT=demo"
  output="WARN: 491 distinct LXXXX/LXXXXX labels (1000 refs); allowed by ALLOW_UNRESOLVED_LXXXX=1"
  status=0
fi
python3 tests/review_packet_fixture.py --output "${out}" --head "${head}" \
  --verify-exit "${status}" --verify-output "${output}" --verify-command "${command}"
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

test_agent_review_start_pass_creates_note_packet_and_prompt() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_start_pass_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output counter note packet prompt
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-1"
  counter="${NESREV_TEST_TMPDIR}/start-pass-make-count"
  mkdir -p "${NESREV_TEST_TMPDIR}/start-pass-bin"
  _write_agent_review_make_stub \
    "${NESREV_TEST_TMPDIR}/start-pass-bin/make" \
    ok \
    "${counter}"

  output="$(
    cd "${repo}" && PATH="${NESREV_TEST_TMPDIR}/start-pass-bin:${PATH}" \
      python3 scripts/agent_review.py start-pass \
        --project demo \
        --pass-id 1 \
        --learning "Process friction: generated note capture exercised." 2>&1
  )"

  assert_match "implementation note: .agents/runs/${run_id}/implementation.md" "${output}" \
    "start-pass must create the implementation note instead of expecting it to preexist"
  assert_match "READY_FOR_REVIEW ${run_id} round 1" "${output}" \
    "start-pass must complete the ready transition"
  assert_match "status: READY_FOR_REVIEW" "${output}" \
    "start-pass must print the final state"
  assert_match "prompt: .agents/runs/${run_id}/prompts/01-ready-for-review-reviewer.md" "${output}" \
    "start-pass must point at the reviewer prompt"

  assert_eq "$(_json_field "${repo}" "status")" "READY_FOR_REVIEW" \
    "start-pass must leave the run ready for review"
  assert_eq "$(_json_field "${repo}" "run_id")" "${run_id}" \
    "default run id must be project-pass-id"
  assert_eq "$(_json_field "${repo}" "review_base")" "${base}" \
    "start-pass must default BASE to HEAD~1"
  assert_eq "$(_json_field "${repo}" "review_head")" "${head}" \
    "start-pass must default HEAD to HEAD"

  note="${repo}/.agents/runs/${run_id}/implementation.md"
  packet="${repo}/.agents/runs/${run_id}/packet-round-01.md"
  prompt="${repo}/.agents/runs/${run_id}/prompts/01-ready-for-review-reviewer.md"
  assert_match "Implemented demo pass 1" "$(<"${note}")" \
    "generated implementation note must name the reviewed pass"
  assert_match "Demo pass" "$(<"${note}")" \
    "generated implementation note must include the commit summary"
  assert_match "## Learning Candidates" "$(<"${note}")" \
    "generated implementation note must carry the learning-candidate section"
  assert_match "generated note capture exercised" "$(<"${note}")" \
    "start-pass must record explicit implementation learning candidates"
  assert_match "Exit status: \`0\`" "$(<"${packet}")" \
    "start-pass must generate a packet that passed verify preflight"
  assert_match "Implementation note: .agents/runs/${run_id}/implementation.md" "$(<"${prompt}")" \
    "reviewer prompt must point at the generated note"
  assert_match "## Learning Candidates" "$(<"${prompt}")" \
    "reviewer prompt must ask reviewers to record process learning candidates"
  assert_eq "$(wc -l <"${counter}" | tr -d ' ')" "1" \
    "start-pass should generate exactly one packet when strict verify passes"
  if [[ -e "${repo}/.agents/runs/${run_id}/state.json" ]]; then
    fail "start-pass must not create an invented per-run state.json"
  fi
}

test_agent_review_start_pass_zero_defaults_to_two_intake_commits() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_pass_zero_repo"
  _init_agent_review_repo "${repo}"

  printf '\n; Reference preparation\n' >> "${repo}/projects/demo/asm/demo.asm"
  git -C "${repo}" add .
  git -C "${repo}" commit -q -m "Reference preparation"

  local base head run_id output counter note
  base="$(git -C "${repo}" rev-parse HEAD~2)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-0"
  counter="${NESREV_TEST_TMPDIR}/pass-zero-make-count"
  mkdir -p "${NESREV_TEST_TMPDIR}/pass-zero-bin"
  _write_agent_review_make_stub \
    "${NESREV_TEST_TMPDIR}/pass-zero-bin/make" \
    ok \
    "${counter}"

  output="$(
    cd "${repo}" && PATH="${NESREV_TEST_TMPDIR}/pass-zero-bin:${PATH}" \
      python3 scripts/agent_review.py start-pass \
        --project demo --pass-id 0 2>&1
  )"

  assert_match "READY_FOR_REVIEW ${run_id} round 1" "${output}" \
    "pass 0 start must complete the review handoff"
  assert_eq "$(_json_field "${repo}" "review_base")" "${base}" \
    "pass 0 must default BASE to HEAD~2"
  assert_eq "$(_json_field "${repo}" "review_head")" "${head}" \
    "pass 0 must retain HEAD as the default review head"
  note="${repo}/.agents/runs/${run_id}/implementation.md"
  assert_match "Demo pass" "$(<"${note}")" \
    "pass 0 review range must include the intake baseline commit"
  assert_match "Reference preparation" "$(<"${note}")" \
    "pass 0 review range must include the reference-preparation commit"
}

test_agent_review_start_pass_zero_honors_explicit_base() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_pass_zero_override_repo"
  _init_agent_review_repo "${repo}"

  local base output counter
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  counter="${NESREV_TEST_TMPDIR}/pass-zero-override-make-count"
  mkdir -p "${NESREV_TEST_TMPDIR}/pass-zero-override-bin"
  _write_agent_review_make_stub \
    "${NESREV_TEST_TMPDIR}/pass-zero-override-bin/make" \
    ok \
    "${counter}"

  output="$(
    cd "${repo}" && PATH="${NESREV_TEST_TMPDIR}/pass-zero-override-bin:${PATH}" \
      python3 scripts/agent_review.py start-pass \
        --project demo --pass-id 0 --base HEAD~1 2>&1
  )"

  assert_match "READY_FOR_REVIEW demo-pass-0 round 1" "${output}" \
    "an explicit pass 0 base must complete the review handoff"
  assert_eq "$(_json_field "${repo}" "review_base")" "${base}" \
    "an explicit pass 0 BASE must override the HEAD~2 default"
}

test_agent_review_start_pass_rejects_process_ranges_before_note() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_start_process_repo"
  mkdir -p "${repo}/scripts"
  cp "${AGENT_REVIEW_SCRIPT}" "${repo}/scripts/agent_review.py"
  cp "${REPO_ROOT}/scripts/process_friction.py" "${repo}/scripts/process_friction.py"
  cp "${REPO_ROOT}/scripts/review_packet_evidence.py" "${repo}/scripts/review_packet_evidence.py"

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

  local output rc
  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py start-pass \
    --project demo --pass-id 2 2>&1)"
  rc=$?
  set -e

  assert_eq "${rc}" "2" "start-pass must reject process ranges like init"
  assert_match "range touches process/tooling paths" "${output}"
  assert_match "scripts/process_tool.sh" "${output}"
  if [[ -e "${repo}/.agents/runs/demo-pass-2/implementation.md" ]]; then
    fail "start-pass must not create a handoff note for a rejected process range"
  fi
}

test_agent_review_prompt_uses_external_script_path_when_repo_lacks_tool() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_external_tool_repo"
  local external_script="${NESREV_TEST_TMPDIR}/agent_review_external.py"
  mkdir -p "${repo}/projects/demo/asm"
  cp "${AGENT_REVIEW_SCRIPT}" "${external_script}"
  cp "${REPO_ROOT}/scripts/process_friction.py" "${NESREV_TEST_TMPDIR}/process_friction.py"
  cp "${REPO_ROOT}/scripts/review_packet_evidence.py" "${NESREV_TEST_TMPDIR}/review_packet_evidence.py"
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

test_agent_review_archive_records_learning_candidates() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_learning_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output friction_path
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-learning"
  friction_path="${repo}/projects/demo/PROCESS_FRICTION.md"

  output="$(
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    cat > ".agents/runs/${run_id}/implementation.md" <<'EOF'
Implemented demo pass.

## Learning Candidates

- Closeout friction should become a wrapper preflight.
EOF
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    cat > ".agents/runs/${run_id}/review-01.md" <<'EOF'
Verdict: CHANGES_REQUESTED

Finding: tighten one name.

## Learning Candidates

- Reviewer had to reconstruct aggregate state manually.
EOF
    python3 scripts/agent_review.py request-changes --review ".agents/runs/${run_id}/review-01.md"
    printf '\n; fix\n' >> "projects/demo/asm/demo.asm"
    git add projects/demo/asm/demo.asm
    git commit -q -m "Fix demo pass"
    local fix_head
    fix_head="$(git rev-parse HEAD)"
    cat > ".agents/runs/${run_id}/response-01.md" <<'EOF'
Disposition: fixed the name.

## Learning Candidates

- Response handoff needed one command instead of manual init plus ready.
EOF
    _write_agent_packet ".agents/runs/${run_id}/packet-r2.md" "${fix_head}" "Packet r2"
    python3 scripts/agent_review.py reready \
      --response ".agents/runs/${run_id}/response-01.md" \
      --head HEAD \
      --packet ".agents/runs/${run_id}/packet-r2.md"
    cat > ".agents/runs/${run_id}/review-02.md" <<'EOF'
Verdict: APPROVED

No findings.

## Learning Candidates

_None._
EOF
    python3 scripts/agent_review.py approve --review ".agents/runs/${run_id}/review-02.md"
    python3 scripts/agent_review.py archive --pass-id 8
  )"

  assert_match "recorded learning candidates in projects/demo/PROCESS_FRICTION.md" "${output}" \
    "archive must report the durable learning-candidate queue when it writes one"

  output="$(<"${friction_path}")"
  assert_match "# Process Friction" "${output}"
  assert_match "## Agent Review Learning Candidates" "${output}"
  assert_match "Pass 8 - ${run_id}" "${output}"
  assert_match "Archive: \`projects/demo/docs/reverse_engineering/reviews/pass-8.md\`" "${output}"
  assert_match "implementation.md" "${output}"
  assert_match "Closeout friction should become a wrapper preflight" "${output}"
  assert_match "review-01.md" "${output}"
  assert_match "aggregate state manually" "${output}"
  assert_match "response-01.md" "${output}"
  assert_match "one command instead of manual init plus ready" "${output}"
  if [[ "${output}" =~ review-02.md ]]; then
    fail "_None._ learning sections must not create process-friction entries"
  fi

  output="$(git -C "${repo}" status --short --untracked-files=all)"
  assert_match "\\?\\? projects/demo/docs/reverse_engineering/reviews/pass-8.md" "${output}" \
    "review archive must remain a tracked project artifact"
  assert_match "\\?\\? projects/demo/PROCESS_FRICTION.md" "${output}" \
    "learning candidates must land in a tracked project queue"
}

test_agent_review_archive_updates_existing_learning_block() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_learning_update_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output friction_path marker_count
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-learning-update"
  friction_path="${repo}/projects/demo/PROCESS_FRICTION.md"

  (
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    cat > ".agents/runs/${run_id}/implementation.md" <<'EOF'
Implemented demo pass.

## Learning Candidates

- Old friction text.
EOF
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    cat > ".agents/runs/${run_id}/review-01.md" <<'EOF'
Verdict: APPROVED

## Learning Candidates

_None._
EOF
    python3 scripts/agent_review.py approve --review ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py archive --pass-id 10
    git add \
      projects/demo/docs/reverse_engineering/reviews/pass-10.md \
      projects/demo/PROCESS_FRICTION.md
    git commit -q -m "Archive pass 10"
    cat > ".agents/runs/${run_id}/implementation.md" <<'EOF'
Implemented demo pass.

## Learning Candidates

- Replacement friction text.
- regex example: \1 backreference.
- path C:\temp\new\file.
EOF
    python3 scripts/agent_review.py archive --pass-id 10 --force
  )

  output="$(<"${friction_path}")"
  assert_match "Replacement friction text" "${output}" \
    "force archive must update the existing generated learning block"
  if [[ "${output}" != *'regex example: \1 backreference.'* ]]; then
    fail "force archive must preserve regex-style backslashes literally"
  fi
  if [[ "${output}" != *'path C:\temp\new\file.'* ]]; then
    fail "force archive must preserve path-style backslashes literally"
  fi
  if [[ "${output}" =~ Old\ friction\ text ]]; then
    fail "force archive must not leave stale learning text in the generated block"
  fi
  marker_count="$(
    grep -c 'agent-review-learning:demo-pass-learning-update:pass-10:start' \
      "${friction_path}"
  )"
  assert_eq "${marker_count}" "1" \
    "force archive must replace the generated learning block instead of duplicating it"

  (
    cd "${repo}"
    python3 scripts/process_friction.py list --project demo > candidates.json
    python3 - <<'PY'
import json
from pathlib import Path
items = json.loads(Path("candidates.json").read_text())
decisions = [{"id": item["id"], "disposition": "discarded", "destinations": [],
              "rationale": "Synthetic observation triaged for lifecycle regression."}
             for item in items]
Path("decisions.json").write_text(json.dumps(decisions))
PY
    python3 scripts/process_friction.py triage --project demo --decisions decisions.json
    python3 scripts/process_friction.py prune --project demo
    git add -u projects/demo
    git add projects/demo/docs/reverse_engineering/inventory/process_friction_receipts.json
    git commit -q -m "Record synthetic queue triage"
    python3 scripts/agent_review.py archive --pass-id 10 --force
  )
  if [[ -e "${friction_path}" ]]; then
    fail "full archive must not recreate a deleted receipted queue"
  fi

  (
    cd "${repo}"
    printf '\n- New evidence after triage.\n' >> ".agents/runs/${run_id}/implementation.md"
    python3 scripts/agent_review.py archive --pass-id 10 --force
  )
  output="$(<"${friction_path}")"
  assert_match "New evidence after triage" "${output}" \
    "full archive must discover new evidence alongside old receipted candidates"
  if [[ "${output}" =~ Replacement\ friction\ text ]]; then
    fail "triaged candidate must remain absent when new evidence is imported"
  fi
}

test_agent_review_archive_skips_empty_learning_candidates() {
  local repo="${NESREV_TEST_TMPDIR}/agent_review_empty_learning_repo"
  _init_agent_review_repo "${repo}"

  local base head run_id output
  base="$(git -C "${repo}" rev-parse HEAD~1)"
  head="$(git -C "${repo}" rev-parse HEAD)"
  run_id="demo-pass-empty-learning"

  output="$(
    cd "${repo}"
    python3 scripts/agent_review.py init \
      --project demo --base "${base}" --head "${head}" --run-id "${run_id}"
    mkdir -p ".agents/runs/${run_id}"
    cat > ".agents/runs/${run_id}/implementation.md" <<'EOF'
Implemented demo pass.

## Learning Candidates

_None._
EOF
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}" "Packet"
    python3 scripts/agent_review.py ready \
      --note ".agents/runs/${run_id}/implementation.md" \
      --packet ".agents/runs/${run_id}/packet.md"
    cat > ".agents/runs/${run_id}/review-01.md" <<'EOF'
Verdict: APPROVED

## Learning Candidates

- _None._
EOF
    python3 scripts/agent_review.py approve --review ".agents/runs/${run_id}/review-01.md"
    python3 scripts/agent_review.py archive --pass-id 9
  )"

  if [[ "${output}" =~ recorded\ learning\ candidates ]]; then
    fail "archive must stay quiet when all learning-candidate sections are empty"
  fi
  if [[ -e "${repo}/projects/demo/PROCESS_FRICTION.md" ]]; then
    fail "_None._ learning sections must not create PROCESS_FRICTION.md"
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

test_agent_review_ready_rejects_failed_process_and_docs_even_with_green_verify() {
  local name repo base head output rc process_status docs_status
  for name in process docs; do
    repo="${NESREV_TEST_TMPDIR}/agent_failed_${name}"
    _init_agent_review_repo "${repo}"
    base="$(git -C "${repo}" rev-parse HEAD~1)"
    head="$(git -C "${repo}" rev-parse HEAD)"
    process_status=0
    docs_status=0
    if [[ "${name}" == process ]]; then process_status=4; else docs_status=5; fi
    (
      cd "${repo}"
      python3 scripts/agent_review.py init --project demo --base "${base}" --head "${head}" --run-id failed-gate
      mkdir -p .agents/runs/failed-gate
      printf 'Implementation evidence\n' > .agents/runs/failed-gate/implementation.md
      _write_agent_packet .agents/runs/failed-gate/packet.md "${head}" Packet 0 "${process_status}" "${docs_status}"
    )
    set +e
    output="$(cd "${repo}" && python3 scripts/agent_review.py ready --note .agents/runs/failed-gate/implementation.md --packet .agents/runs/failed-gate/packet.md 2>&1)"
    rc=$?
    set -e
    assert_eq "${rc}" 2 'all required gates must pass before ready'
    assert_match 'Gate exit status is nonzero' "${output}"
    assert_eq "$(_json_field "${repo}" status)" IMPLEMENTING
  done
}

test_agent_review_ready_and_reused_packet_refuse_incomplete_command_evidence() {
  local variant repo base head output rc
  for variant in no-op missing-output assembler wrong-subject write-prep; do
    repo="${NESREV_TEST_TMPDIR}/evidence_${variant}"
    _init_agent_review_repo "${repo}"
    base="$(git -C "${repo}" rev-parse HEAD~1)"
    head="$(git -C "${repo}" rev-parse HEAD)"
    (
      cd "${repo}"
      python3 scripts/agent_review.py init --project demo --base "${base}" --head "${head}" --run-id evidence
      printf 'Implementation evidence\n' > .agents/runs/evidence/implementation.md
      _write_agent_packet .agents/runs/evidence/packet.md "${head}"
      python3 - "${variant}" "${head}" <<'PY'
import argparse, re, sys
from pathlib import Path
sys.path.insert(0, 'scripts')
import agent_review
import review_packet_evidence as evidence
path = Path('.agents/runs/evidence/packet.md')
value = path.read_text()
variant, head = sys.argv[1:]
if variant == 'no-op':
    _, record = evidence.gate_evidence(value, 'cache-preparation')
    value = value.replace(record['command'], 'true')
elif variant == 'missing-output':
    body = evidence.section(value, 'Project Verify Gate', 3)
    value = value.replace(body, re.sub(r'Output:\n\n(`{3,})text\n.*?\n\1\n', '', body, flags=re.S))
elif variant == 'assembler':
    value = value.replace('XASM_BIN=xasm', 'XASM_BIN=/unexpected/assembler')
elif variant == 'wrong-subject':
    value = value.replace('project-pass-prep PROJECT=demo', 'project-pass-prep PROJECT=another_demo')
else:
    value = value.replace('PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=0', 'PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=1')
path.write_text(value)
state = {'packet': str(path), 'review_head': head, 'project': 'demo'}
try:
    agent_review.ensure_packet(Path.cwd(), state, argparse.Namespace(packet=None, generate_packet=False))
except agent_review.UserError:
    pass
else:
    raise AssertionError('reused packet accepted incomplete command evidence')
PY
    )
    set +e
    output="$(cd "${repo}" && python3 scripts/agent_review.py ready --note .agents/runs/evidence/implementation.md --packet .agents/runs/evidence/packet.md 2>&1)"
    rc=$?
    set -e
    assert_eq "${rc}" 2 "${variant} must refuse handoff"
    assert_eq "$(_json_field "${repo}" status)" IMPLEMENTING
  done
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
    python3 tests/review_packet_fixture.py --output ".agents/runs/${run_id}/packet.md" \
      --head "${head}" --verify-exit 2 \
      --verify-output 'FAIL: 491 distinct LXXXX/LXXXXX labels (1000 refs)'
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

test_make_project_pass_review_start_forwards_learning_text() {
  local repo="${NESREV_TEST_TMPDIR}/make_agent_review_start_repo"
  _init_agent_review_repo "${repo}"
  cp "${REPO_ROOT}/Makefile" "${repo}/Makefile"

  printf '\n; Reference preparation\n' >> "${repo}/projects/demo/asm/demo.asm"
  git -C "${repo}" add projects/demo/asm/demo.asm
  git -C "${repo}" commit -q -m "Reference preparation"

  local run_id="demo-pass-0"
  local counter="${NESREV_TEST_TMPDIR}/make-agent-review-start-count"
  local base learning make_bin output note
  base="$(git -C "${repo}" rev-parse HEAD~2)"
  mkdir -p "${NESREV_TEST_TMPDIR}/make-agent-review-start-bin"
  _write_agent_review_make_stub \
    "${NESREV_TEST_TMPDIR}/make-agent-review-start-bin/make" \
    ok \
    "${counter}"
  make_bin="$(command -v make)"
  learning=$'Process friction kept $44 literal.\nSecond $55 line.'

  output="$(
    cd "${repo}" && PATH="${NESREV_TEST_TMPDIR}/make-agent-review-start-bin:${PATH}" \
      "${make_bin}" project-pass-review-start PROJECT=demo PASS=0 \
        "LEARNING=${learning}" 2>&1
  )"

  note="${repo}/.agents/runs/${run_id}/implementation.md"
  assert_match "READY_FOR_REVIEW ${run_id} round 1" "${output}" \
    "make wrapper must drive start-pass through ready"
  assert_match 'Process friction kept [$]44 literal' "$(<"${note}")" \
    "make wrapper must preserve learning text for generated implementation notes"
  assert_match 'Second [$]55 line' "$(<"${note}")" \
    "make wrapper must preserve multiline learning text"
  assert_eq "$(_json_field "${repo}" "review_base")" "${base}" \
    "make wrapper must preserve the pass-aware HEAD~2 default for pass 0"
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
    _write_agent_packet ".agents/runs/${run_id}/packet.md" "${head}"
    python3 - ".agents/runs/${run_id}/packet.md" <<'PY'
import re, sys
from pathlib import Path
path = Path(sys.argv[1])
path.write_text(re.sub(r'(?ms)^### Project Verify Gate\n.*?(?=^### )', '', path.read_text(), count=1))
PY
  )

  set +e
  output="$(cd "${repo}" && python3 scripts/agent_review.py ready \
    --note ".agents/runs/${run_id}/implementation.md" \
    --packet ".agents/runs/${run_id}/packet.md" 2>&1)"
  rc=$?
  set -e
  assert_eq "${rc}" "2" "ready must reject packets without verify evidence"
  assert_match "packet requires exactly one Project Verify Gate section" "${output}"
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
  cp "${REPO_ROOT}/scripts/process_friction.py" "${repo}/scripts/process_friction.py"
  cp "${REPO_ROOT}/scripts/review_packet_evidence.py" "${repo}/scripts/review_packet_evidence.py"

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
