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
  assert_match "pdftotext .* OPTIONAL" "${stdout}"
  assert_match "pdftoppm .* OPTIONAL" "${stdout}"
  assert_match "tesseract .* OPTIONAL" "${stdout}"
}

test_reference_tool_readiness() {
  python3 "${REPO_ROOT}/tests/reference_tools_test.py"
}

_reference_doctor_fixture() {
  local root="${NESREV_TEST_TMPDIR}/reference checkout"
  mkdir -p "${root}/projects/demo/docs/game_reference/"{manuals,faqs}
  ln -s "${REPO_ROOT}/scripts" "${root}/scripts"
  _make_stub_bindir "${NESREV_TEST_TMPDIR}/stub_bin" \
    java javac xasm bash python3 rg od dd awk sed perl make git head
  cd "${root}"
}

test_doctor_project_text_references_need_no_pdf_or_ocr_tools() {
  _reference_doctor_fixture
  printf 'Manual text\n' > projects/demo/docs/game_reference/manuals/manual.txt
  printf '<html>FAQ</html>\n' > projects/demo/docs/game_reference/faqs/faq.html
  PATH="${NESREV_TEST_TMPDIR}/stub_bin" make -f "${REPO_ROOT}/Makefile" project-doctor PROJECT=demo \
    >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr"
  assert_match "all required tools present" "$(cat "${NESREV_TEST_TMPDIR}/stdout")"
}

test_doctor_project_pdf_faq_requires_extraction_and_ocr_tools() {
  _reference_doctor_fixture
  printf 'Manual text\n' > projects/demo/docs/game_reference/manuals/manual.txt
  printf 'PDF fixture\n' > projects/demo/docs/game_reference/faqs/guide.PDF
  local rc=0
  PATH="${NESREV_TEST_TMPDIR}/stub_bin" make -f "${REPO_ROOT}/Makefile" project-doctor PROJECT=demo \
    >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr" || rc=$?
  assert_eq "${rc}" "2" "Make must reject missing PDF/OCR tools for a supplied FAQ"
  local stdout; stdout="$(cat "${NESREV_TEST_TMPDIR}/stdout")"
  assert_match "pdftotext .* MISSING" "${stdout}"
  assert_match "pdftoppm .* MISSING" "${stdout}"
  assert_match "tesseract .* MISSING" "${stdout}"
  assert_match "reference extraction prerequisites failed" "$(cat "${NESREV_TEST_TMPDIR}/stderr")"
}

_reference_tesseract_stub() {
  local language="$1"
  cat > "${NESREV_TEST_TMPDIR}/stub_bin/tesseract" <<SH
#!/bin/bash
case "\$1" in
  --version) echo 'tesseract fixture' ;;
  --list-langs) printf 'List of available languages (1):\\n%s\\n' '${language}' ;;
  *) exit 1 ;;
esac
SH
  chmod +x "${NESREV_TEST_TMPDIR}/stub_bin/tesseract"
}

test_doctor_project_image_requires_ocr_but_not_poppler() {
  _reference_doctor_fixture
  printf 'Image fixture\n' > projects/demo/docs/game_reference/manuals/page.PNG
  _reference_tesseract_stub jpn
  PATH="${NESREV_TEST_TMPDIR}/stub_bin" bash "${DOCTOR}" demo >"${NESREV_TEST_TMPDIR}/stdout"
  assert_match "tesseract .* OK.*1 recognition language" "$(cat "${NESREV_TEST_TMPDIR}/stdout")"
  assert_match "pdftoppm .* OPTIONAL" "$(cat "${NESREV_TEST_TMPDIR}/stdout")"
}

test_doctor_project_rejects_ocr_without_recognition_language_data() {
  _reference_doctor_fixture
  printf 'Image fixture\n' > projects/demo/docs/game_reference/manuals/page.png
  _reference_tesseract_stub osd
  local rc=0
  PATH="${NESREV_TEST_TMPDIR}/stub_bin" bash "${DOCTOR}" demo \
    >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr" || rc=$?
  assert_eq "${rc}" "1" "OCR orientation data alone cannot read a manual"
  assert_match "no usable OCR language data" "$(cat "${NESREV_TEST_TMPDIR}/stdout")"
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

test_doctor_reports_installed_when_version_probe_fails() {
  local bindir="${NESREV_TEST_TMPDIR}/stub_bin"
  _make_stub_bindir "${bindir}" \
    java javac xasm bash python3 rg od dd awk sed perl make git head
  # Mimic a BSD utility with no --version flag: diagnose on stderr, exit
  # non-zero. The diagnostic must never be reported as a version string.
  rm -f "${bindir}/od"
  cat > "${bindir}/od" <<'SH'
#!/usr/bin/env bash
echo "od: illegal option -- -" >&2
echo "usage: od [-aBbcDdeFfHhIiLlOosvXx] [file ...]" >&2
exit 1
SH
  chmod +x "${bindir}/od"

  PATH="${bindir}" bash "${DOCTOR}" >"${NESREV_TEST_TMPDIR}/stdout" 2>"${NESREV_TEST_TMPDIR}/stderr"

  local stdout; stdout="$(cat "${NESREV_TEST_TMPDIR}/stdout")"
  assert_match "od .* \(installed\)" "${stdout}" \
    "a failed version probe must fall back to (installed)"
  if [[ "${stdout}" == *"illegal option"* ]]; then
    printf '%s\n' "${stdout}" >&2
    fail "doctor reported a usage error as a version string"
  fi
}
