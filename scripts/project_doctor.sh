#!/usr/bin/env bash
set -euo pipefail

# Reports the presence and version of every external tool nesrev needs.
# Required tools fail the gate; optional tools warn only.
#
# Presumed POSIX base toolset (not checked individually): cmp, mktemp,
# sort, tee, wc, tr, head, cat, grep, find, basename, dirname. Hosts
# missing these are not supported even if listed tools are present.

REQUIRED=(
  "java:Java runtime (https://adoptium.net or 'brew install --cask temurin')"
  "javac:Java compiler (same install as java)"
  "xasm:6502 assembler used by project-verify / intake (install from your nesrev tooling distribution)"
  "bash:GNU bash (preinstalled on macOS/Linux)"
  "python3:Python 3 (https://python.org or 'brew install python')"
  "rg:ripgrep (https://github.com/BurntSushi/ripgrep or 'brew install ripgrep')"
  "od:POSIX hex dump (coreutils, preinstalled)"
  "dd:POSIX block copy (coreutils, preinstalled)"
  "awk:POSIX awk (preinstalled)"
  "sed:POSIX sed (preinstalled)"
  "perl:Perl 5 for batch text rewrites (preinstalled on macOS/Linux)"
  "make:GNU make (preinstalled)"
  "git:Git (https://git-scm.com or 'brew install git')"
)

OPTIONAL=(
  "jq:JSON inspection for generated pass artifacts ('brew install jq')"
  "shellcheck:Shell script linting ('brew install shellcheck')"
)

missing_required=0

printf '%-12s %-9s %s\n' 'TOOL' 'STATUS' 'NOTES'
printf '%-12s %-9s %s\n' '----' '------' '-----'

check_tool() {
  local entry="$1"
  local required="$2"
  local tool="${entry%%:*}"
  local hint="${entry#*:}"
  if command -v "$tool" >/dev/null 2>&1; then
    local version
    # Probe with --version, then -version. Redirect stdin from /dev/null so a
    # tool that misinterprets the argument as a search pattern (e.g. rg
    # treating "-version" as a pattern) cannot block on stdin. Fall back to
    # "(installed)" if both probes return empty.
    version="$("$tool" --version </dev/null 2>&1 | head -n 1 || true)"
    if [[ -z "$version" ]]; then
      version="$("$tool" -version </dev/null 2>&1 | head -n 1 || true)"
    fi
    if [[ -z "$version" ]]; then
      version="(installed)"
    fi
    printf '%-12s %-9s %s\n' "$tool" 'OK' "$version"
  else
    if [[ "$required" == "required" ]]; then
      printf '%-12s %-9s %s\n' "$tool" 'MISSING' "$hint"
      missing_required=$((missing_required + 1))
    else
      printf '%-12s %-9s %s\n' "$tool" 'OPTIONAL' "$hint"
    fi
  fi
}

for entry in "${REQUIRED[@]}"; do
  check_tool "$entry" required
done
for entry in "${OPTIONAL[@]}"; do
  check_tool "$entry" optional
done

if (( missing_required > 0 )); then
  echo >&2
  echo "doctor: ${missing_required} required tool(s) missing" >&2
  exit 1
fi

echo
echo "doctor: all required tools present"
echo "doctor: presumes a POSIX base toolset (cmp, mktemp, sort, tee, wc, tr, head, cat, grep, find, basename, dirname); not individually checked"
