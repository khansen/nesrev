#!/usr/bin/env bash
# Tests scripts/project_doctor.sh failure cases.
# Runs the doctor under a stripped PATH to simulate missing tools and asserts
# the script exits non-zero with a clear message.

DOCTOR="${REPO_ROOT}/scripts/project_doctor.sh"

# A minimal PATH containing only the tools the test wants to expose. Each
# tool we want present is symlinked into a tmp bindir; the doctor runs with
# only that bindir on PATH.
_make_stub_bindir() {
  local bindir="$1"; shift
  mkdir -p "${bindir}"
  for tool in "$@"; do
    # Resolve the absolute path of the tool and symlink it.
    local src
    src="$(command -v "${tool}" 2>/dev/null || true)"
    if [[ -z "${src}" ]]; then
      fail "_make_stub_bindir: host is missing required tool ${tool}; cannot stub"
    fi
    ln -s "${src}" "${bindir}/${tool}"
  done
}

test_doctor_passes_when_all_required_present() {
  # Sanity: doctor should exit 0 in the normal environment. Run as a
  # regression guard against accidental list bloat.
  set +e
  bash "${DOCTOR}" >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "doctor should exit 0 on a healthy host"
  assert_match "all required tools present" "$(cat "${NESREV_TEST_TMPDIR}/stdout")"
}

test_doctor_fails_when_required_tool_missing() {
  local bindir="${NESREV_TEST_TMPDIR}/stub_bin"
  # Provide every required tool except 'rg'. Also include `head`, which the
  # doctor pipes its version probes through but does not check itself.
  _make_stub_bindir "${bindir}" \
    java javac xasm bash python3 od dd awk sed perl make git head
  set +e
  PATH="${bindir}" bash "${DOCTOR}" >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "1" "doctor should fail when rg is missing"
  local stderr; stderr="$(cat "${NESREV_TEST_TMPDIR}/stderr")"
  assert_match "1 required tool" "${stderr}"
  local stdout; stdout="$(cat "${NESREV_TEST_TMPDIR}/stdout")"
  assert_match "rg .* MISSING" "${stdout}" "MISSING line for rg should appear on stdout"
}

test_doctor_does_not_fail_on_missing_optional() {
  local bindir="${NESREV_TEST_TMPDIR}/stub_bin"
  # Include all required tools, omit jq + shellcheck (both optional). Also
  # include `head`, which the doctor's version probes pipe through.
  _make_stub_bindir "${bindir}" \
    java javac xasm bash python3 rg od dd awk sed perl make git head
  set +e
  PATH="${bindir}" bash "${DOCTOR}" >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "doctor should exit 0 when only optional tools are missing"
  local stdout; stdout="$(cat "${NESREV_TEST_TMPDIR}/stdout")"
  assert_match "jq .* OPTIONAL" "${stdout}"
  assert_match "shellcheck .* OPTIONAL" "${stdout}"
}

test_doctor_captures_version_printed_to_stderr() {
  local bindir="${NESREV_TEST_TMPDIR}/stub_bin"
  _make_stub_bindir "${bindir}" \
    java javac xasm bash python3 rg od dd awk sed perl make git head
  rm -f "${bindir}/javac"
  cat > "${bindir}/javac" <<'SH'
#!/usr/bin/env bash
if [[ "${1:-}" == "-version" || "${1:-}" == "--version" ]]; then
  echo "javac stderr-version-fixture" >&2
  exit 0
fi
exit 0
SH
  chmod +x "${bindir}/javac"

  PATH="${bindir}" bash "${DOCTOR}" >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr"

  assert_match "javac .* stderr-version-fixture" "$(cat "${NESREV_TEST_TMPDIR}/stdout")"
}
