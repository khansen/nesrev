#!/usr/bin/env bash
# Tests scripts/new_project.sh — the scaffold generator. Each test invokes
# the script with a per-test unique slug, asserts on exit code + side
# effects, and cleans up via the EXIT trap.

NEW_PROJECT="${REPO_ROOT}/scripts/new_project.sh"
MAKEFILE="${REPO_ROOT}/Makefile"
ROOT_NEW_PROJECT_DOC="${REPO_ROOT}/agent_playbook/NEW_PROJECT.md"
ROOT_TOOLING_DOC="${REPO_ROOT}/agent_playbook/TOOLING.md"

_run_scaffold() {
  local slug="$1"; shift
  set +e
  bash "${NEW_PROJECT}" "${slug}" \
    >"${NESREV_TEST_TMPDIR}/scaffold.stdout" 2>"${NESREV_TEST_TMPDIR}/scaffold.stderr"
  local rc=$?
  set -e
  echo "${rc}"
}

_mark_recovery_none() {
  local slug="$1"
  sed -i.bak \
    's/NESREV_RECOVERY_STATUS="pending"/NESREV_RECOVERY_STATUS="none"/' \
    "projects/${slug}/project.conf"
  rm -f "projects/${slug}/project.conf.bak"
}

_prepare_docs_check_fixture() {
  local slug="$1"
  make project-init "PROJECT=${slug}" >/dev/null
  make_ines "${NESREV_TEST_TMPDIR}/${slug}.nes"
  cp "${NESREV_TEST_TMPDIR}/${slug}.nes" "projects/${slug}/reference/${slug}.nes"
  make project-regenerate-asm "PROJECT=${slug}" >/dev/null
  _mark_recovery_none "${slug}"

  local onboarding="projects/${slug}/docs/reverse_engineering/ONBOARDING.md"
  sed -i.bak \
    -e 's/Status: scaffolded; intake gates have not completed./Status: intake baseline captured; semantic naming not started./' \
    -e 's/Recovery controls: pending discovery before intake./Recovery controls: discovery completed; no NESrev control files required./' \
    "${onboarding}"
  rm -f "${onboarding}.bak"

  cat >> "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" <<'EOF'

Legacy fixture: Initial intake; run `project-inventory` and KPI scripts to seed values.
EOF
}

_run_intake_expect_recovery_error() {
  local slug="$1"
  set +e
  make project-intake "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/intake.stdout" 2>"${NESREV_TEST_TMPDIR}/intake.stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "2" "invalid recovery configuration must make intake exit 2"
}

test_make_project_init_scaffolds_a_project() {
  # End-to-end test of the canonical entry point. Catches a broken
  # make target even if scripts/new_project.sh itself is healthy.
  local slug; slug="$(unique_slug scaffold_make_init)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  set +e
  make project-init "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/make.stdout" 2>"${NESREV_TEST_TMPDIR}/make.stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "make project-init PROJECT=<slug> must exit 0"
  [[ -d "projects/${slug}" ]] \
    || fail "make project-init did not create projects/${slug}"
  [[ -f "projects/${slug}/project.conf" ]] \
    || fail "make project-init did not write project.conf"
  [[ -f "projects/${slug}/docs/reverse_engineering/inventory/data_format_targets.csv" ]] \
    || fail "make project-init did not write data_format_targets.csv"
  grep -qF 'DATA_FORMAT_TARGETS_REQUIRED="1"' "projects/${slug}/project.conf" \
    || fail "make project-init did not opt into data-format target maturity checks"
  grep -qF "audio_music_jingles,not_yet_reviewed" \
    "projects/${slug}/docs/reverse_engineering/inventory/data_format_targets.csv" \
    || fail "data_format_targets.csv must include an explicit music disposition row"
  grep -qF "audio_sfx_cues,not_yet_reviewed" \
    "projects/${slug}/docs/reverse_engineering/inventory/data_format_targets.csv" \
    || fail "data_format_targets.csv must include an explicit SFX disposition row"
}

test_failed_xasm_leaves_warning_baseline_empty() {
  # Regression test for warning-baseline atomicity. If xasm emits
  # warnings then exits non-zero during the seed step, WARN_BASELINE
  # must be left untouched so a retry can re-seed cleanly. Earlier
  # versions used a direct ">> WARN_BASELINE" pipeline and would
  # partially populate the file on partial xasm output.
  #
  # Implementation: front of PATH gets a stub xasm that emits a fake
  # "defined but not used" warning to stderr/stdout, then exits 1.
  # Other intake gates are not reached because intake exits as soon
  # as the seed step's xasm fails.
  local slug; slug="$(unique_slug fresh_xasm_fail)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  local stub_bin="${NESREV_TEST_TMPDIR}/stub_xasm"
  mkdir -p "${stub_bin}"
  # Symlink every real required tool into stub_bin, then add a fake xasm.
  for tool in java javac bash python3 rg od dd awk sed perl make git head cmp mktemp sort tee wc tr cat grep find basename dirname jq cp mv rm ls touch mkdir; do
    local src
    src="$(command -v "${tool}" 2>/dev/null || true)"
    [[ -n "${src}" ]] && ln -s "${src}" "${stub_bin}/${tool}" 2>/dev/null || true
  done
  cat > "${stub_bin}/xasm" <<'STUB'
#!/usr/bin/env bash
echo "warning: \`FakeUnused' defined but not used" >&2
exit 1
STUB
  chmod +x "${stub_bin}/xasm"

  make project-init "PROJECT=${slug}" >/dev/null
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes"
  cp "${NESREV_TEST_TMPDIR}/rom.nes" "projects/${slug}/reference/${slug}.nes"
  # regenerate still uses the REAL xasm (we don't shadow PATH yet).
  make project-regenerate-asm "PROJECT=${slug}" >/dev/null
  _mark_recovery_none "${slug}"

  local baseline_file="projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
  # Pre-condition: baseline must be empty / comment-only so the seed
  # path will run.
  : > "${baseline_file}"
  local before_size
  before_size=$(wc -c < "${baseline_file}" | tr -d ' ')

  # Now run intake under the stub xasm.
  set +e
  PATH="${stub_bin}:${PATH}" \
    make project-intake "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/intake.stdout" 2>"${NESREV_TEST_TMPDIR}/intake.stderr"
  local rc=$?
  set -e
  if (( rc == 0 )); then
    fail "intake unexpectedly succeeded under stub xasm; failure-path injection did not bite"
  fi

  # WARN_BASELINE must still be empty — the atomic mv must not have run.
  local after_size
  after_size=$(wc -c < "${baseline_file}" | tr -d ' ')
  assert_eq "${after_size}" "${before_size}" \
    "warning baseline must remain unchanged when xasm fails (before=${before_size} after=${after_size})"

  # No leftover .XXXXXX tmp files in the baseline directory.
  local leftover
  leftover=$(find "projects/${slug}/docs/reverse_engineering" \
    -maxdepth 1 -name 'WARNING_BASELINE.txt.*' 2>/dev/null | wc -l | tr -d ' ')
  assert_eq "${leftover}" "0" \
    "atomic-publish tmp files must be cleaned up when xasm fails"
}

test_failed_intake_leaves_onboarding_status_unchanged() {
  # Regression test for the ONBOARDING status-update ordering. The
  # intake script must not promote ONBOARDING to "intake baseline
  # captured" until every gate (verify, process-check, docs-check,
  # scorecard sync) has succeeded. Inject a docs-check failure mode
  # (backticked `Makefile` inside docs/reverse_engineering/) after
  # regen but before intake, then assert intake fails AND ONBOARDING
  # still claims "scaffolded". A retry must still be able to seed.
  local slug; slug="$(unique_slug fresh_fail_status)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  local out="${NESREV_TEST_TMPDIR}/e2e_fail"
  mkdir -p "${out}"

  make project-init "PROJECT=${slug}" >"${out}/init.stdout" 2>&1
  make_ines "${out}/rom.nes"
  cp "${out}/rom.nes" "projects/${slug}/reference/${slug}.nes"
  make project-regenerate-asm "PROJECT=${slug}" >"${out}/regen.stdout" 2>&1
  _mark_recovery_none "${slug}"

  # Inject the failure: backticked Makefile in QUICK_REFERENCE.md.
  # project-docs-check will treat it as an unknown asm symbol and exit
  # non-zero, which becomes intake's exit code.
  sed -i.bak 's|the top-level Makefile|the top-level `Makefile`|' \
    "projects/${slug}/docs/reverse_engineering/QUICK_REFERENCE.md"
  rm -f "projects/${slug}/docs/reverse_engineering/QUICK_REFERENCE.md.bak"

  set +e
  make project-intake "PROJECT=${slug}" >"${out}/intake.stdout" 2>"${out}/intake.stderr"
  local rc=$?
  set -e

  # Intake must have failed.
  if (( rc == 0 )); then
    fail "intake unexpectedly succeeded; failure-path injection did not bite"
  fi

  # ONBOARDING status must still be the scaffold placeholder, NOT
  # "intake baseline captured".
  local onboarding="projects/${slug}/docs/reverse_engineering/ONBOARDING.md"
  grep -qF "Status: scaffolded; intake gates have not completed." \
    "${onboarding}" \
    || fail "ONBOARDING status was promoted before all intake gates succeeded"
  ! grep -qF "intake baseline captured" "${onboarding}" \
    || fail "ONBOARDING contains 'intake baseline captured' after a failed intake"
  grep -qF "## First Steps" "${onboarding}" \
    || fail "failed intake should restore the scaffold First Steps section"
  ! grep -qF "## Resuming Work" "${onboarding}" \
    || fail "failed intake should not leave the post-intake Resuming Work section"
}

test_fresh_project_init_regenerate_intake_happy_path() {
  # End-to-end test of the documented fresh-project path:
  #   1. make project-init
  #   2. place a supported ROM
  #   3. make project-regenerate-asm
  #   4. make project-intake
  # All four steps must exit 0; intake's project-docs-check sub-step
  # validates the scaffolded docs against the regenerated asm. A
  # symbol-shaped token in any generated doc that does not appear in
  # the asm fails docs-check, so this test catches doc drift that
  # earlier component tests miss.
  local slug; slug="$(unique_slug fresh_e2e)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  local out="${NESREV_TEST_TMPDIR}/e2e"
  mkdir -p "${out}"

  # Step 1: scaffold via the Make target.
  set +e
  make project-init "PROJECT=${slug}" \
    >"${out}/init.stdout" 2>"${out}/init.stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "0" "make project-init must exit 0 in the fresh-project path"

  # Step 2: synthesize a strict iNES 1.0 ROM and drop it into the
  # scaffold's reference directory under the expected name.
  make_ines "${out}/rom.nes"
  cp "${out}/rom.nes" "projects/${slug}/reference/${slug}.nes"

  # Step 3: regenerate asm.
  set +e
  make project-regenerate-asm "PROJECT=${slug}" \
    >"${out}/regen.stdout" 2>"${out}/regen.stderr"
  rc=$?
  set -e
  if (( rc != 0 )); then
    cat "${out}/regen.stderr" >&2 || true
    fail "make project-regenerate-asm must exit 0 in the fresh-project path"
  fi

  # Step 4: record the required discovery outcome, then intake. This
  # synthetic ROM has no indirect-dispatch recovery controls.
  _mark_recovery_none "${slug}"

  # Intake bundles verify (relaxed), inventory refresh,
  # process-check, docs-check, and scorecard sync. A warning-producing
  # fresh ROM may first fail after seeding REVIEW REQUIRED baseline
  # placeholders; curate those rationales, then rerun intake.
  set +e
  make project-intake "PROJECT=${slug}" \
    >"${out}/intake.stdout" 2>"${out}/intake.stderr"
  rc=$?
  set -e
  if (( rc != 0 )) && grep -qF "warning baseline still has auto-seed rationale" "${out}/intake.stderr"; then
    perl -0pi -e 's/REVIEW REQUIRED: intake auto-seed; replace with symbol-specific rationale/synthetic ROM warning retained for fixture/g' \
      "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"
    set +e
    make project-intake "PROJECT=${slug}" \
      >"${out}/intake-rerun.stdout" 2>"${out}/intake-rerun.stderr"
    rc=$?
    set -e
    if (( rc != 0 )); then
      cat "${out}/intake-rerun.stderr" >&2 || true
      fail "make project-intake rerun must exit 0 after curating warning-baseline placeholders"
    fi
  fi
  if (( rc != 0 )); then
    cat "${out}/intake.stderr" >&2 || true
    fail "make project-intake must exit 0 in the fresh-project path"
  fi

  local onboarding="projects/${slug}/docs/reverse_engineering/ONBOARDING.md"
  grep -qF "Status: intake baseline captured; semantic naming not started." "${onboarding}" \
    || fail "successful intake did not write a durable onboarding status"
  grep -qF "Recovery controls: discovery completed; no NESrev control files required." "${onboarding}" \
    || fail "successful intake did not record the no-controls discovery outcome"
  grep -qF "## Resuming Work" "${onboarding}" \
    || fail "successful intake did not replace setup steps with a Resuming Work section"
  ! grep -qF "## First Steps" "${onboarding}" \
    || fail "successful intake left the scaffold First Steps section in ONBOARDING.md"
  ! rg -q "Place the reference ROM|Generate the assembly|Run intake" "${onboarding}" \
    || fail "successful intake left scaffold setup directions in ONBOARDING.md"
  ! rg -q "replace with project-specific|update this snapshot" "${onboarding}" \
    || fail "successful intake left scaffold replacement instructions in ONBOARDING.md"
}

test_intake_rejects_pending_recovery_discovery() {
  local slug; slug="$(unique_slug pending_recovery)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  make project-init "PROJECT=${slug}" >/dev/null
  make_ines "${NESREV_TEST_TMPDIR}/rom.nes"
  cp "${NESREV_TEST_TMPDIR}/rom.nes" "projects/${slug}/reference/${slug}.nes"
  make project-regenerate-asm "PROJECT=${slug}" >/dev/null

  set +e
  make project-intake "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/intake.stdout" 2>"${NESREV_TEST_TMPDIR}/intake.stderr"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "intake must reject pending recovery discovery"
  assert_match "recovery discovery is still pending" \
    "$(cat "${NESREV_TEST_TMPDIR}/intake.stderr")"
}

test_intake_rejects_none_with_configured_control() {
  local slug; slug="$(unique_slug none_with_control)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make project-init "PROJECT=${slug}" >/dev/null
  sed -i.bak \
    -e 's/NESREV_RECOVERY_STATUS="pending"/NESREV_RECOVERY_STATUS="none"/' \
    -e "s|NESREV_CODEENTRIES_FILE=\"\"|NESREV_CODEENTRIES_FILE=\"projects/${slug}/config/nesrev/codeentries.txt\"|" \
    "projects/${slug}/project.conf"
  rm -f "projects/${slug}/project.conf.bak"

  _run_intake_expect_recovery_error "${slug}"
  assert_match 'NESREV_RECOVERY_STATUS="none" conflicts' "$(cat "${NESREV_TEST_TMPDIR}/intake.stderr")"
}

test_intake_rejects_configured_without_control() {
  local slug; slug="$(unique_slug configured_empty)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make project-init "PROJECT=${slug}" >/dev/null
  sed -i.bak \
    's/NESREV_RECOVERY_STATUS="pending"/NESREV_RECOVERY_STATUS="configured"/' \
    "projects/${slug}/project.conf"
  rm -f "projects/${slug}/project.conf.bak"

  _run_intake_expect_recovery_error "${slug}"
  assert_match "requires at least one" "$(cat "${NESREV_TEST_TMPDIR}/intake.stderr")"
}

test_intake_rejects_configured_control_outside_tracked_directory() {
  local slug; slug="$(unique_slug configured_outside)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make project-init "PROJECT=${slug}" >/dev/null
  sed -i.bak \
    -e 's/NESREV_RECOVERY_STATUS="pending"/NESREV_RECOVERY_STATUS="configured"/' \
    -e "s|NESREV_CODEENTRIES_FILE=\"\"|NESREV_CODEENTRIES_FILE=\"projects/${slug}/reference/codeentries.txt\"|" \
    "projects/${slug}/project.conf"
  rm -f "projects/${slug}/project.conf.bak"

  _run_intake_expect_recovery_error "${slug}"
  assert_match "must live under projects/${slug}/config/nesrev/" \
    "$(cat "${NESREV_TEST_TMPDIR}/intake.stderr")"
}

test_intake_rejects_missing_configured_control() {
  local slug; slug="$(unique_slug configured_missing)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  make project-init "PROJECT=${slug}" >/dev/null
  sed -i.bak \
    -e 's/NESREV_RECOVERY_STATUS="pending"/NESREV_RECOVERY_STATUS="configured"/' \
    -e "s|NESREV_CODEENTRIES_FILE=\"\"|NESREV_CODEENTRIES_FILE=\"projects/${slug}/config/nesrev/missing.txt\"|" \
    "projects/${slug}/project.conf"
  rm -f "projects/${slug}/project.conf.bak"

  _run_intake_expect_recovery_error "${slug}"
  assert_match "configured NESrev control file not found" \
    "$(cat "${NESREV_TEST_TMPDIR}/intake.stderr")"
}

test_legacy_project_allows_pre_contract_scorecard_note() {
  local slug; slug="$(unique_slug legacy_scorecard)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _prepare_docs_check_fixture "${slug}"

  # Simulate a project.conf created before the recovery lifecycle existed.
  sed -i.bak '/^NESREV_/d' "projects/${slug}/project.conf"
  rm -f "projects/${slug}/project.conf.bak"

  make project-docs-check "PROJECT=${slug}" >/dev/null \
    || fail "legacy project must not fail solely for the pre-contract pass-0 note"
}

test_new_project_rejects_pre_contract_scorecard_note() {
  local slug; slug="$(unique_slug new_scorecard)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _prepare_docs_check_fixture "${slug}"

  set +e
  make project-docs-check "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/docs.stdout" 2>"${NESREV_TEST_TMPDIR}/docs.stderr"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "new project must reject the stale pass-0 scorecard note"
  assert_match "Initial intake; run" "$(cat "${NESREV_TEST_TMPDIR}/docs.stderr")"
}

test_docs_check_rejects_unresolved_label_in_systems_overview() {
  local slug; slug="$(unique_slug systems_lxxxx)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _prepare_docs_check_fixture "${slug}"

  local systems_doc="projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
  printf '\nRendering enters through `LCAFE`.\n' >> "${systems_doc}"

  set +e
  make project-docs-check "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/docs.stdout" 2>"${NESREV_TEST_TMPDIR}/docs.stderr"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "systems overview must reject unresolved LXXXX/LXXXXX labels"
  assert_match "systems doc contains unresolved LXXXX/LXXXXX labels" \
    "$(cat "${NESREV_TEST_TMPDIR}/docs.stderr")"
}

test_docs_check_rejects_future_pass_planning_in_systems_overview() {
  local slug; slug="$(unique_slug systems_future_plan)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _prepare_docs_check_fixture "${slug}"

  local systems_doc="projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
  printf '\nThe audio entry point is queued for a future pass.\n' >> "${systems_doc}"

  set +e
  make project-docs-check "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/docs.stdout" 2>"${NESREV_TEST_TMPDIR}/docs.stderr"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "systems overview must reject future-pass planning"
  assert_match "systems doc contains provisional/future-pass planning" \
    "$(cat "${NESREV_TEST_TMPDIR}/docs.stderr")"
}

test_docs_check_rejects_warning_baseline_review_required() {
  local slug; slug="$(unique_slug warning_review_required)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT
  _prepare_docs_check_fixture "${slug}"

  printf 'FakeUnused|REVIEW REQUIRED: intake auto-seed; replace with symbol-specific rationale\n' \
    >> "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt"

  set +e
  make project-docs-check "PROJECT=${slug}" \
    >"${NESREV_TEST_TMPDIR}/docs.stdout" 2>"${NESREV_TEST_TMPDIR}/docs.stderr"
  local rc=$?
  set -e

  assert_eq "${rc}" "2" "docs-check must reject uncurated warning-baseline placeholders"
  assert_match "warning baseline still has auto-seed rationale" \
    "$(cat "${NESREV_TEST_TMPDIR}/docs.stderr")"
}

test_valid_scaffold_creates_required_files() {
  local slug; slug="$(unique_slug scaffold_ok)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  local rc; rc=$(_run_scaffold "${slug}")
  assert_eq "${rc}" "0" "valid scaffold must exit 0"

  # Top-level files
  for f in \
    "projects/${slug}/README.md" \
    "projects/${slug}/project.conf" \
    "projects/${slug}/config/nesrev/.gitkeep" \
    "projects/${slug}/asm/.gitkeep" \
    "projects/${slug}/reference/.gitkeep" \
    "projects/${slug}/docs/reverse_engineering/ONBOARDING.md" \
    "projects/${slug}/docs/reverse_engineering/QUICK_REFERENCE.md" \
    "projects/${slug}/docs/reverse_engineering/MEMORY_MAP.md" \
    "projects/${slug}/docs/reverse_engineering/PROGRESS_SCORECARD.md" \
    "projects/${slug}/docs/reverse_engineering/WARNING_BASELINE.txt" \
    "projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md" \
    "projects/${slug}/docs/reverse_engineering/inventory/renames.csv" \
    "projects/${slug}/docs/crosswalk/TERMINOLOGY_CROSSWALK.md" \
    "projects/${slug}/docs/crosswalk/MANUAL_TERMS.md"
  do
    [[ -e "${f}" ]] || fail "scaffold did not create ${f}"
  done
  [[ -d "projects/${slug}/build" ]] || fail "scaffold did not create projects/${slug}/build"
  [[ ! -e "projects/${slug}/build/.gitkeep" ]] || fail "build directory must not contain .gitkeep"
}

test_generated_systems_overview_stays_deferred_until_promotion() {
  local slug; slug="$(unique_slug systems_deferred)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  local systems_doc="projects/${slug}/docs/reverse_engineering/${slug}_DX_Systems.md"
  grep -qF "Status: intentionally not promoted during intake." "${systems_doc}" \
    || fail "generated systems overview must state that promotion is deferred"
  grep -qF "DOCUMENTATION.md#dx-systems-scope" "${systems_doc}" \
    || fail "generated systems overview must link to the promotion criteria"
  ! grep -qF "Recommended sections:" "${systems_doc}" \
    || fail "generated systems overview must not invite eager subsystem expansion"
}

test_valid_scaffold_substitutes_slug_in_templates() {
  local slug; slug="$(unique_slug scaffold_subst)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null
  # project.conf must reference the slug, not the literal template
  grep -q "PROJECT_NAME=\"${slug}\"" "projects/${slug}/project.conf" \
    || fail "project.conf is missing PROJECT_NAME=${slug}"
  grep -q "ASM_FILE=\"projects/${slug}/asm/${slug}.asm\"" "projects/${slug}/project.conf" \
    || fail "project.conf is missing the templated ASM_FILE path"
  grep -q 'NESREV_RECOVERY_STATUS="pending"' "projects/${slug}/project.conf" \
    || fail "project.conf must start with pending recovery discovery"
  grep -q 'NESREV_CODEPOINTERS_FILE=""' "projects/${slug}/project.conf" \
    || fail "project.conf is missing the code-pointer control setting"
  [[ ! -e "projects/${slug}/docs/game_reference/metadata/MANUAL_TERMS.md" ]] \
    || fail "authored MANUAL_TERMS.md must not be created in ignored game_reference/"
  # No literal '${slug}' should leak into generated docs
  ! grep -rl '\${slug}' "projects/${slug}" >/dev/null \
    || fail "templates leaked an unsubstituted \${slug} into generated files"
}

test_invalid_slug_uppercase_is_rejected() {
  local rc; rc=$(_run_scaffold "InvalidSlug")
  assert_eq "${rc}" "2" "uppercase slug must exit 2"
  assert_match "must match" "$(cat "${NESREV_TEST_TMPDIR}/scaffold.stderr")"
  [[ ! -e "projects/InvalidSlug" ]] || fail "rejected slug must not create a directory"
}

test_invalid_slug_with_space_is_rejected() {
  local rc; rc=$(_run_scaffold "bad slug")
  assert_eq "${rc}" "2" "slug containing whitespace must exit 2"
  assert_match "must match" "$(cat "${NESREV_TEST_TMPDIR}/scaffold.stderr")"
}

test_invalid_slug_with_slash_is_rejected() {
  local rc; rc=$(_run_scaffold "bad/slug")
  assert_eq "${rc}" "2" "slug containing a slash must exit 2"
  assert_match "must match" "$(cat "${NESREV_TEST_TMPDIR}/scaffold.stderr")"
  [[ ! -e "projects/bad" ]] || fail "rejected slug must not create a directory"
}

test_missing_slug_argument_emits_usage() {
  set +e
  bash "${NEW_PROJECT}" \
    >"${NESREV_TEST_TMPDIR}/scaffold.stdout" 2>"${NESREV_TEST_TMPDIR}/scaffold.stderr"
  local rc=$?
  set -e
  assert_eq "${rc}" "1" "missing slug must exit 1"
  assert_match "usage:" "$(cat "${NESREV_TEST_TMPDIR}/scaffold.stderr")"
}

test_duplicate_project_is_rejected() {
  local slug; slug="$(unique_slug scaffold_dup)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  # Initial scaffold
  _run_scaffold "${slug}" >/dev/null
  # Second scaffold must fail without touching the existing tree
  local rc; rc=$(_run_scaffold "${slug}")
  assert_eq "${rc}" "3" "duplicate scaffold must exit 3"
  assert_match "already exists" "$(cat "${NESREV_TEST_TMPDIR}/scaffold.stderr")"
  # Existing project still present and intact
  [[ -e "projects/${slug}/project.conf" ]] || fail "duplicate run damaged existing project"
}

test_quick_reference_commands_are_real_make_targets() {
  local slug; slug="$(unique_slug scaffold_targets)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  # Extract every "make <target> PROJECT=..." line from QUICK_REFERENCE.md
  # and confirm each <target> is in the Makefile's .PHONY list.
  local phony_line
  phony_line="$(grep '^\.PHONY:' "${MAKEFILE}")"
  while IFS= read -r target; do
    [[ -z "${target}" ]] && continue
    if ! grep -qE "(^| )${target}( |$)" <<<"${phony_line}"; then
      fail "QUICK_REFERENCE.md references make target '${target}' that is not in .PHONY"
    fi
  done < <(
    grep -oE 'make project-[a-z-]+' \
      "projects/${slug}/docs/reverse_engineering/QUICK_REFERENCE.md" \
      | awk '{print $2}' | sort -u
  )
}

test_onboarding_support_matrix_link_resolves() {
  local slug; slug="$(unique_slug scaffold_onlink)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  local onboarding="projects/${slug}/docs/reverse_engineering/ONBOARDING.md"
  # The support-matrix reference must be a real markdown link
  # ("[..](../../../../agent_playbook/NEW_PROJECT.md#rom-support-matrix)").
  grep -qE '\[[^]]+\]\(\.\./\.\./\.\./\.\./agent_playbook/NEW_PROJECT\.md#rom-support-matrix\)' \
    "${onboarding}" \
    || fail "ONBOARDING.md is missing the support-matrix markdown link"
  # The relative path must resolve to the actual NEW_PROJECT.md.
  local resolved
  resolved="$(cd "$(dirname "${onboarding}")" && cd ../../../../ && pwd)/agent_playbook/NEW_PROJECT.md"
  [[ -f "${resolved}" ]] || fail "support-matrix link does not resolve: ${resolved}"
  # The anchor must exist in the target.
  grep -q '<a id="rom-support-matrix">' "${resolved}" \
    || fail "#rom-support-matrix anchor missing from agent_playbook/NEW_PROJECT.md"
}

test_quick_reference_optional_variables_link_resolves() {
  local slug; slug="$(unique_slug scaffold_qrlink)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  local qref="projects/${slug}/docs/reverse_engineering/QUICK_REFERENCE.md"
  # Optional-variables section heading must exist (target of the in-page link)
  grep -q '^## Optional variables' "${qref}" \
    || fail "QUICK_REFERENCE.md is missing the Optional variables section heading"
  # The trailing-byte override link must resolve to the canonical anchor.
  grep -qE 'agent_playbook/NEW_PROJECT\.md#trailing-byte-override' "${qref}" \
    || fail "QUICK_REFERENCE.md is missing the trailing-byte-override pointer"
  grep -q '<a id="trailing-byte-override">' "${ROOT_NEW_PROJECT_DOC}" \
    || fail "#trailing-byte-override anchor missing from agent_playbook/NEW_PROJECT.md"
}

test_project_readme_hint_link_resolves() {
  local slug; slug="$(unique_slug scaffold_hintlink)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  local readme="projects/${slug}/README.md"
  grep -qE '\[[^]]+\]\(\.\./\.\./agent_playbook/TOOLING\.md#nesrev-controls\)' \
    "${readme}" \
    || fail "project README.md is missing the hint-formats markdown link"
  # Anchor present at target
  grep -q '<a id="nesrev-controls">' "${ROOT_TOOLING_DOC}" \
    || fail "#nesrev-controls anchor missing from agent_playbook/TOOLING.md"
}

test_project_readme_corridor_contract_link_resolves() {
  local slug; slug="$(unique_slug scaffold_corridorlink)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  local readme="projects/${slug}/README.md"
  grep -qE '\[Corridor Execution Contract\]\(\.\./\.\./AGENTS\.md#work-order\)' \
    "${readme}" \
    || fail "project README.md is missing the Corridor Execution Contract link"
  grep -q '<a id="work-order">' "${REPO_ROOT}/AGENTS.md" \
    || fail "#work-order anchor missing from AGENTS.md"
}

test_generated_docs_state_repository_root_requirement() {
  local slug; slug="$(unique_slug scaffold_repo_root)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  # The top-level project README, ONBOARDING.md, and QUICK_REFERENCE.md
  # must each call out that make commands run from the repository root.
  # Match a lowercase "repository root" phrase so reasonable wording
  # variations pass.
  for f in \
    "projects/${slug}/README.md" \
    "projects/${slug}/docs/reverse_engineering/ONBOARDING.md" \
    "projects/${slug}/docs/reverse_engineering/QUICK_REFERENCE.md"
  do
    grep -qi "repository root" "${f}" \
      || fail "${f} must state the repository-root requirement"
  done
}

test_all_generated_markdown_links_resolve() {
  # Generic generated-doc link checker. For every markdown link
  # `[text](target)` in every generated `.md` file under projects/<slug>/:
  #   - skip external URLs (http/https/mailto)
  #   - skip same-file anchor-only links ("#foo") that point to a heading
  #     in the same file (validated via explicit <a id="..."> anchors or
  #     ## headings)
  #   - require relative file paths to resolve under the repo root
  #   - if the target carries an "#anchor", require either
  #     <a id="anchor"></a> in the target file or an "## Anchor"-style
  #     heading whose slug matches.
  #
  # Drift-resistant: any new link the scaffold emits is checked
  # automatically.

  local slug; slug="$(unique_slug scaffold_linkcheck)"
  cleanup_project "${slug}"
  trap "cleanup_project ${slug}" EXIT

  _run_scaffold "${slug}" >/dev/null

  # strip_code regression fixture. Every fake link below is inside a
  # CommonMark code construct that strip_code should remove before the
  # link checker scans the document. Each fake link uses a UNIQUE target
  # naming its delimiter style, so a regression report points at the
  # exact branch that leaked. The control link at the bottom uses a
  # unique target (../../Makefile) that does not appear elsewhere in
  # the scaffold; it is asserted as resolved below so an over-broad
  # strip_code that swallows the entire fixture cannot pass silently.
  cat >> "projects/${slug}/README.md" <<'FIXTURE'

<!-- strip_code regression fixture (see new_project_test.sh) -->

inline 1-backtick: `[fake-1bt](does/not/exist-1bt.md)`
inline 2-backtick: ``[fake-2bt](does/not/exist-2bt.md)``
inline 3-backtick: ```[fake-3bt](does/not/exist-3bt.md)```

triple-backtick fence:

```
[fake-3bt-fence](does/not/exist-3bt-fence.md)
```

four-backtick fence (nesting a triple-backtick fence):

````
```
[fake-4bt-fence](does/not/exist-4bt-fence.md)
```
````

triple-tilde fence:

~~~
[fake-3tilde-fence](does/not/exist-3tilde-fence.md)
~~~

four-tilde fence:

~~~~
[fake-4tilde-fence](does/not/exist-4tilde-fence.md)
~~~~

[strip-code-fixture-control](../../Makefile)
FIXTURE

  EXPECTED_CONTROL_LINK='[strip-code-fixture-control](../../Makefile)' \
    python3 - "projects/${slug}" "${REPO_ROOT}" <<'PY'
import os, re, sys, pathlib
from urllib.parse import unquote

project_root = pathlib.Path(sys.argv[1]).resolve()
repo_root = pathlib.Path(sys.argv[2]).resolve()

# Link grammar: target excludes `)` so the regex terminates at the link's
# closing paren rather than the first nested one. The optional title
# suffix is permitted but ignored. Empty `[text]()` and bare `[text](#)`
# are captured for explicit rejection below.
#
# Documented restrictions:
# - Targets containing literal `)` (e.g. `file_(x).md`) are not supported
#   in generated docs; the scaffold templates avoid them. Use URL-encoded
#   `%29` if a target ever needs a literal close-paren.
# - Links inside CommonMark code constructs are stripped before scanning
#   so example markdown in documentation prose is not treated as a real
#   link. The strip handles:
#     * backtick fences of 3+ backticks (```...```, ````...````, ...)
#     * tilde fences of 3+ tildes (~~~...~~~, ~~~~...~~~~, ...)
#     * inline spans of N backticks (`x`, ``x``, ```x```, ...) — the
#       closing run must match the opening run's length.
#   4-space indented code blocks are NOT recognized; the scaffold
#   templates do not use them.
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]*?)(?:\s+\"[^\"]*\")?\)")
FENCED_CODE_RE = re.compile(r"(`{3,}|~{3,}).*?\1", re.DOTALL)
CODE_SPAN_RE = re.compile(r"(`+).*?\1", re.DOTALL)
ANCHOR_TAG_RE = re.compile(r'<a\s+id="([^"]+)"\s*></a>')
HEADING_RE = re.compile(r"^#+\s+(.*?)\s*$", re.MULTILINE)

def strip_code(text):
    text = FENCED_CODE_RE.sub("", text)
    text = CODE_SPAN_RE.sub("", text)
    return text

def slugify(text):
    s = text.strip().lower()
    s = re.sub(r"[^a-z0-9\s_-]", "", s)
    s = re.sub(r"\s+", "-", s)
    return s

def collect_anchors(path):
    text = path.read_text(encoding="utf-8")
    anchors = set(ANCHOR_TAG_RE.findall(text))
    for h in HEADING_RE.findall(text):
        anchors.add(slugify(h))
    return anchors

# A required-control marker that this test's strip_code fixture appends
# to projects/<slug>/README.md. The checker must observe it in the
# resolved-link set; if it does not, strip_code may have over-broad
# matching and swallowed the fixture (and possibly other prose) — the
# checker fails with a specific message rather than silently passing
# because earlier scaffold links still resolved.
REQUIRED_CONTROL = os.environ.get("EXPECTED_CONTROL_LINK", "").strip()

errors = []
seen = 0
resolved_link_strings = set()
for md in project_root.rglob("*.md"):
    text = strip_code(md.read_text(encoding="utf-8"))
    for m in LINK_RE.finditer(text):
        seen += 1
        link_text = m.group(0)
        target = unquote(m.group(1)).strip()
        if target.startswith(("http://", "https://", "mailto:")):
            continue
        if target == "" or target == "#":
            errors.append(
                f"{md.relative_to(repo_root)}: empty link target {link_text}"
            )
            continue
        if "#" in target:
            path_part, anchor = target.split("#", 1)
            if not anchor:
                errors.append(
                    f"{md.relative_to(repo_root)}: link has empty fragment {link_text}"
                )
                continue
        else:
            path_part, anchor = target, ""
        if path_part:
            target_path = (md.parent / path_part).resolve()
        else:
            target_path = md
        try:
            target_path.relative_to(repo_root)
        except ValueError:
            errors.append(f"{md.relative_to(repo_root)}: link target outside repo {link_text}")
            continue
        if not target_path.exists():
            errors.append(
                f"{md.relative_to(repo_root)}: missing target file {link_text} "
                f"(resolved {target_path})"
            )
            continue
        if anchor and target_path.is_file() and target_path.suffix.lower() == ".md":
            anchors = collect_anchors(target_path)
            if anchor not in anchors:
                errors.append(
                    f"{md.relative_to(repo_root)}: anchor missing for {link_text} "
                    f"(target {target_path.relative_to(repo_root)})"
                )
                continue
        resolved_link_strings.add(link_text)

if REQUIRED_CONTROL and REQUIRED_CONTROL not in resolved_link_strings:
    errors.append(
        f"required control link not resolved: {REQUIRED_CONTROL!r} "
        f"(strip_code may be over-broad and swallowing the fixture)"
    )

if errors:
    print("link-checker findings:", file=sys.stderr)
    for e in errors:
        print(f"  {e}", file=sys.stderr)
    sys.exit(1)
print(f"checked {seen} markdown link(s) across generated docs")
PY
}
