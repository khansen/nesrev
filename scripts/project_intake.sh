#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project_slug>" >&2
  exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=scripts/project_common.sh
source "${SCRIPT_DIR}/project_common.sh"

load_project_conf "$1"

inv_dir="${DOC_ROOT}/inventory"
mkdir -p "${inv_dir}"

listing_json="${inv_dir}/intake_listing.json"
xref_json="${inv_dir}/intake_xref.json"
audit_json="${inv_dir}/raw_address_audit.json"

configured_controls=()
for control_path in \
  "${NESREV_CODEPOINTERS_FILE}" \
  "${NESREV_CODEENTRIES_FILE}" \
  "${NESREV_DATAPOINTERS_FILE}" \
  "${NESREV_INLINECALLS_FILE}" \
  "${NESREV_DATARANGES_FILE}"
do
  [[ -n "${control_path}" ]] && configured_controls+=("${control_path}")
done

case "${NESREV_RECOVERY_STATUS}" in
  pending)
    echo "error: NESrev recovery discovery is still pending." >&2
    echo "       Inspect indirect dispatch and hidden-code candidates before intake." >&2
    echo "       Then set NESREV_RECOVERY_STATUS=\"none\" or \"configured\" in projects/$1/project.conf." >&2
    echo "       See agent_playbook/NEW_PROJECT.md#nesrev-intake-sanity-gate." >&2
    exit 2
    ;;
  none)
    if (( ${#configured_controls[@]} != 0 )); then
      echo "error: NESREV_RECOVERY_STATUS=\"none\" conflicts with configured NESrev control files." >&2
      exit 2
    fi
    recovery_summary="Recovery controls: discovery completed; no NESrev control files required."
    ;;
  configured)
    if (( ${#configured_controls[@]} == 0 )); then
      echo "error: NESREV_RECOVERY_STATUS=\"configured\" requires at least one NESREV_*_FILE path in project.conf." >&2
      exit 2
    fi
    for control_path in "${configured_controls[@]}"; do
      if [[ "${control_path}" != "projects/$1/config/nesrev/"* ]]; then
        echo "error: configured NESrev control must live under projects/$1/config/nesrev/: ${control_path}" >&2
        exit 2
      fi
      if [[ ! -f "${control_path}" ]]; then
        echo "error: configured NESrev control file not found: ${control_path}" >&2
        exit 2
      fi
    done
    recovery_summary="Recovery controls: "
    recovery_separator=""
    for control_path in "${configured_controls[@]}"; do
      recovery_summary+="${recovery_separator}${control_path}"
      recovery_separator=", "
    done
    recovery_summary+="."
    ;;
  legacy)
    # Existing projects created before the discovery-state field remain valid.
    recovery_summary=""
    ;;
  *)
    echo "error: invalid NESREV_RECOVERY_STATUS='${NESREV_RECOVERY_STATUS}'; expected pending, none, or configured." >&2
    exit 2
    ;;
esac

echo "[0/8] Preparing intake registries"
bash "${SCRIPT_DIR}/refresh_inventory.sh" "$1"

# Transactional ONBOARDING promotion.
#
# project-docs-check rejects the scaffold's "Status: scaffolded" line in
# ONBOARDING.md, so intake must promote it before that gate runs. But a
# subsequent failure (process-check, docs-check, scorecard sync, or a
# late assembly error) must not leave a false "intake baseline captured"
# claim on disk — a retry would not undo it because the placeholder is
# gone.
#
# Resolution: snapshot ONBOARDING before promotion and register one
# EXIT trap that restores the snapshot on non-zero exit AND cleans any
# seed-stage tmp files. The handler captures $? as its first action so
# the original failure rc is preserved (a multi-command trap body would
# overwrite $? with the cleanup commands' rc=0 and skip rollback).
# project-docs-check sees ordinary docs in either state — no
# suppression env-var or backdoor.
ONBOARDING_SNAPSHOT=""
xasm_seed_log=""
baseline_tmp=""
_intake_cleanup() {
  local rc=$?
  # Disable errexit so a failure in any cleanup command cannot abort
  # the handler before rollback or before `exit "${rc}"` runs. Each
  # cleanup step is best-effort: if it fails, we proceed to the next
  # step with the original rc preserved.
  set +e
  if [[ -n "${xasm_seed_log}" ]]; then
    rm -f "${xasm_seed_log}"
  fi
  if [[ -n "${baseline_tmp}" ]]; then
    rm -f "${baseline_tmp}"
  fi
  # ONBOARDING rollback on non-zero exit.
  if [[ -n "${ONBOARDING_SNAPSHOT}" && -f "${ONBOARDING_SNAPSHOT}" ]]; then
    if (( rc != 0 )) && [[ -f "${ONBOARDING_FILE}" ]]; then
      cp "${ONBOARDING_SNAPSHOT}" "${ONBOARDING_FILE}"
      echo "intake failed (rc=${rc}); restored ONBOARDING.md from snapshot" >&2
    fi
    rm -f "${ONBOARDING_SNAPSHOT}"
  fi
  exit "${rc}"
}
trap _intake_cleanup EXIT

if [[ -f "${ONBOARDING_FILE}" ]] && grep -qF "Status: scaffolded; intake gates have not completed." "${ONBOARDING_FILE}"; then
  ONBOARDING_SNAPSHOT="$(mktemp)"
  cp "${ONBOARDING_FILE}" "${ONBOARDING_SNAPSHOT}"
  python3 - "${ONBOARDING_FILE}" "${recovery_summary}" "$1" <<'PY'
import re
import sys
from pathlib import Path

path = Path(sys.argv[1])
recovery_summary = sys.argv[2]
slug = sys.argv[3]
text = path.read_text(encoding="utf-8")
text = text.replace(
    "Status: scaffolded; intake gates have not completed.",
    "Status: intake baseline captured; semantic naming not started.",
)
if recovery_summary:
    text = text.replace(
        "Recovery controls: pending discovery before intake.",
        recovery_summary,
    )
resume = f"""## Resuming Work

Run from the repository root:

```sh
make project-pass-prep PROJECT={slug}
make project-next-pass PROJECT={slug}
make project-pass-start PROJECT={slug}
```

Use WORKING_NOTES.md when present for durable open questions.
If the ROM or NESrev recovery controls change, rerun:

```sh
make project-regenerate-asm PROJECT={slug}
make project-intake PROJECT={slug}
```
"""
text = re.sub(r"\n## First Steps\n.*\Z", "\n" + resume, text, flags=re.S)
path.write_text(text, encoding="utf-8")
PY
  echo "promoted ONBOARDING intake state (will roll back on intake failure)"
fi

echo "[1/8] Seeding warning baseline if empty"
if ! grep -qv "^[[:space:]]*\(#.*\)\?$" "${WARN_BASELINE_FILE}" 2>/dev/null; then
  mkdir -p "$(dirname "${OUT_BIN}")"
  # Stage the seed and publish atomically: build the complete new
  # baseline (existing content + parsed warnings) in a same-directory
  # tmp file, then mv it into place. A failed xasm or post-xasm step
  # leaves both tmp files and WARN_BASELINE_FILE untouched (the EXIT
  # trap cleans the tmps); a retry can re-seed cleanly.
  xasm_seed_log="$(mktemp)"
  baseline_dir="$(dirname "${WARN_BASELINE_FILE}")"
  baseline_tmp="$(mktemp "${baseline_dir}/WARNING_BASELINE.txt.XXXXXX")"
  set +e
  xasm --pure-binary -o "${OUT_BIN}" "${ASM_FILE}" >"${xasm_seed_log}" 2>&1
  xasm_rc=$?
  set -e
  if (( xasm_rc != 0 )); then
    cat "${xasm_seed_log}" >&2
    echo "error: xasm failed during warning-baseline seed (rc=${xasm_rc}); baseline left unchanged for retry" >&2
    exit "${xasm_rc}"
  fi
  # Build the new baseline content: original file (if any) followed by
  # the deduplicated warning lines.
  if [[ -f "${WARN_BASELINE_FILE}" ]]; then
    cat "${WARN_BASELINE_FILE}" >"${baseline_tmp}"
  fi
  sed -nE "s/.*warning: \`([A-Za-z_][A-Za-z0-9_]*)' defined but not used.*/\\1|REVIEW REQUIRED: intake auto-seed; replace with symbol-specific rationale/p" \
    "${xasm_seed_log}" \
    | sort -u >>"${baseline_tmp}"
  # Atomic publish (rename is atomic within a single filesystem). Once
  # the mv succeeds, baseline_tmp is gone; the EXIT trap's rm -f on the
  # captured name is a harmless no-op.
  mv "${baseline_tmp}" "${WARN_BASELINE_FILE}"
  baseline_tmp=""
  rm -f "${xasm_seed_log}"
  xasm_seed_log=""
  seeded="$(grep -cv "^[[:space:]]*\(#.*\)\?$" "${WARN_BASELINE_FILE}" || true)"
  echo "seeded ${seeded} symbols into ${WARN_BASELINE_FILE}"
else
  echo "OK: warning baseline already populated"
fi

echo "[2/8] Verifying intake baseline"
ALLOW_UNRESOLVED_LXXXX=1 bash "${SCRIPT_DIR}/project_verify.sh" "$1"

echo "[3/8] Generating structured listing"
mkdir -p "$(dirname "${OUT_BIN}")"
xasm --pure-binary -o "${OUT_BIN}" --listing="${listing_json}" --listing-format=json "${ASM_FILE}" >/dev/null

echo "[4/8] Generating structured xref"
xasm --pure-binary -o "${OUT_BIN}" --xref="${xref_json}" --xref-format=json "${ASM_FILE}" >/dev/null

echo "[5/8] Auditing raw addresses"
bash "${SCRIPT_DIR}/project_audit.sh" "$1" json > "${audit_json}"

echo "[6/8] Refreshing inventory"
bash "${SCRIPT_DIR}/refresh_inventory.sh" "$1"

echo "[7/8] Running process/doc checks"
bash "${SCRIPT_DIR}/project_process_check.sh" "$1"
bash "${SCRIPT_DIR}/project_docs_check.sh" "$1"

echo "[8/8] Syncing intake-baseline scorecard row"
bash "${SCRIPT_DIR}/project_scorecard_sync.sh" "$1" 0

# Intake succeeded: clear the rollback snapshot so the trap exits clean
# and the promoted ONBOARDING line stays on disk.
if [[ -n "${ONBOARDING_SNAPSHOT}" ]]; then
  rm -f "${ONBOARDING_SNAPSHOT}"
  ONBOARDING_SNAPSHOT=""
fi
trap - EXIT

echo "intake complete: $1"
