#!/usr/bin/env bash
# Notify an already-running, bracketed-paste-aware agent session in a tmux pane.
#
# Called by:
#   python3 scripts/agent_review.py watch --notify scripts/agent_review_tmux_notify.sh
#
# Contract:
#   agent_review_tmux_notify.sh <role> <status> <prompt-file>
#
# Required role targets:
#   AGENT_REVIEW_TMUX_REVIEWER=%12
#   AGENT_REVIEW_TMUX_IMPLEMENTER=%13

set -euo pipefail

die() {
  echo "error: $*" >&2
  exit 2
}

if (( $# != 3 )); then
  die "usage: $0 <reviewer|implementer> <status> <prompt-file>"
fi

role="$1"
status="$2"
prompt_file="$3"

case "${role}" in
  reviewer)
    target_var="AGENT_REVIEW_TMUX_REVIEWER"
    target="${AGENT_REVIEW_TMUX_REVIEWER:-}"
    ;;
  implementer)
    target_var="AGENT_REVIEW_TMUX_IMPLEMENTER"
    target="${AGENT_REVIEW_TMUX_IMPLEMENTER:-}"
    ;;
  *)
    die "unknown role: ${role}"
    ;;
esac

if [[ -z "${target}" ]]; then
  die "set ${target_var} to the target tmux pane for ${role}"
fi
if [[ ! -f "${prompt_file}" ]]; then
  die "prompt file does not exist: ${prompt_file}"
fi

tmux_bin="${AGENT_REVIEW_TMUX_BIN:-tmux}"
if ! command -v "${tmux_bin}" >/dev/null 2>&1; then
  die "tmux command not found: ${tmux_bin}"
fi

submit="${AGENT_REVIEW_TMUX_SUBMIT:-1}"
case "${submit}" in
  0|1) ;;
  *) die "AGENT_REVIEW_TMUX_SUBMIT must be 0 or 1" ;;
esac

buffer="agent-review-${role}-$$"
cleanup_buffer() {
  "${tmux_bin}" delete-buffer -b "${buffer}" >/dev/null 2>&1 || true
}
trap cleanup_buffer EXIT

if ! pane_id="$("${tmux_bin}" display-message -p -t "${target}" '#{pane_id}')"; then
  die "tmux target not found: ${target}"
fi
if [[ -z "${pane_id}" ]]; then
  die "tmux target not found: ${target}"
fi
"${tmux_bin}" load-buffer -b "${buffer}" "${prompt_file}"
"${tmux_bin}" paste-buffer -p -d -b "${buffer}" -t "${target}"
if [[ "${submit}" == "1" ]]; then
  "${tmux_bin}" send-keys -t "${target}" Enter
fi

printf 'sent %s prompt to %s pane %s\n' "${status}" "${role}" "${target}"
