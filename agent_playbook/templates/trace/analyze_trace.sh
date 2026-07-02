#!/usr/bin/env bash
# Template: reduce raw trace logs to a per-capture evidence summary.
set -euo pipefail

IN_LOG="${1:-tmp/traces/trace.log}"
CANONICAL_SUMMARY="${CANONICAL_TRACE_DOC:-TRACE_TRANSITIONS.md}"

normalize_with_existing_parent() {
  local path="$1"
  local dir
  local base
  dir="$(dirname "${path}")"
  base="$(basename "${path}")"
  if [[ -d "${dir}" ]]; then
    printf '%s/%s\n' "$(cd "${dir}" && pwd)" "${base}"
  else
    printf '%s\n' "${path}"
  fi
}

if [[ $# -ge 2 ]]; then
  OUT_SUMMARY="$2"
else
  log_dir="$(dirname "${IN_LOG}")"
  log_base="$(basename "${IN_LOG}")"
  OUT_SUMMARY="${log_dir}/${log_base%.*}.summary.md"
fi

OUT_SUMMARY="$(normalize_with_existing_parent "${OUT_SUMMARY}")"
CANONICAL_SUMMARY="$(normalize_with_existing_parent "${CANONICAL_SUMMARY}")"

if [[ "${OUT_SUMMARY}" == "${CANONICAL_SUMMARY}" && "${ALLOW_CANONICAL_TRACE_OVERWRITE:-0}" != "1" ]]; then
  echo "ERROR: refusing to overwrite curated evidence doc: ${OUT_SUMMARY}" >&2
  echo "       Write the per-capture summary beside the raw log, then merge accepted evidence manually." >&2
  echo "       Set ALLOW_CANONICAL_TRACE_OVERWRITE=1 only for deliberate regeneration." >&2
  exit 2
fi

if [[ ! -f "${IN_LOG}" ]]; then
  echo "ERROR: trace log not found: ${IN_LOG}" >&2
  exit 1
fi

mkdir -p "$(dirname "${OUT_SUMMARY}")"

TOTAL=$(wc -l <"${IN_LOG}" | tr -d ' ')
WATCH_EVENTS=$(grep -c '"event":"watch"' "${IN_LOG}" || true)
NOW_UTC=$(date -u '+%Y-%m-%d %H:%M:%S UTC')

MILESTONES=$(perl -ne 'print "$2 (frame $1)\n" if /"frame":(\d+).*"event":"milestone".*"name":"([^"]+)"/' "${IN_LOG}" \
  | awk '!seen[$1]++')

TRANSITIONS=$(perl -ne '
  my %f;
  $f{frame} = $1 if /"frame":(\d+)/;
  for my $k (qw(id addr old new scenario result pc)) {
    $f{$k} = $1 if /"$k":"([^"]+)"/;
  }
  next unless defined $f{id} && defined $f{old} && defined $f{new};
  my $key = "$f{id} $f{old}->$f{new}";
  $count{$key}++;
  $first{$key} //= $f{frame};
  $addr{$key} //= $f{addr} // "????";
  $scenario{$key} //= $f{scenario} // "??";
  $result{$key} //= $f{result} // "??";
  $pc{$key}{$f{pc}}++ if defined $f{pc};
  END {
    for my $key (sort keys %count) {
      my $pcs = %{$pc{$key}//{}} ? " pc=".join(",", sort keys %{$pc{$key}}) : "";
      printf "%-24s addr=%s n=%-4d first_frame=%-6s scenario=%s result=%s%s\n",
        $key, $addr{$key}, $count{$key}, $first{$key}, $scenario{$key}, $result{$key}, $pcs;
    }
  }' "${IN_LOG}")

{
  echo "# Trace Transition Table (Reduced Evidence)"
  echo
  echo "- Generated: ${NOW_UTC}"
  echo "- Source log: ${IN_LOG} (raw log untracked unless curated as a fixture)"
  echo "- total lines: ${TOTAL}"
  echo "- watch events: ${WATCH_EVENTS}"
  echo
  echo "## Scenario Milestones"
  echo
  echo '```text'
  if [[ -n "${MILESTONES}" ]]; then echo "${MILESTONES}"; else echo "(no milestones recorded)"; fi
  echo '```'
  echo
  echo "## Transitions"
  echo
  echo '```text'
  if [[ -n "${TRANSITIONS}" ]]; then echo "${TRANSITIONS}"; else echo "(no watch transitions recorded)"; fi
  echo '```'
  echo
  echo "## Interpretation Notes"
  echo
  echo "- Replace this section with the domain-specific verdict and promotion notes."
} >"${OUT_SUMMARY}"

echo "Summary written: ${OUT_SUMMARY}"
