#!/usr/bin/env bash
# Tests that the playbook audit snippets can source project_common.sh from
# bash and zsh.

_scaffold_common_fixture() {
  local slug="$1"
  local rom="${NESREV_TEST_TMPDIR}/fixture.nes"
  make_ines "${rom}"
  scaffold_project "${slug}" "${rom}"
}

test_project_common_loads_project_conf_from_bash() {
  local slug; slug="$(unique_slug common_bash)"
  trap "cleanup_project ${slug}" EXIT
  _scaffold_common_fixture "${slug}"

  local output
  output="$(bash -c 'source scripts/project_common.sh && load_project_conf "$1" && echo "ASM=${ASM_FILE}"' _ "${slug}" 2>&1)"

  assert_match "ASM=projects/${slug}/asm/${slug}.asm" "${output}"
  assert_not_match "No such file|parameter not set" "${output}"
}

test_project_common_loads_project_conf_from_zsh() {
  if ! command -v zsh >/dev/null 2>&1; then
    return 0
  fi
  local slug; slug="$(unique_slug common_zsh)"
  trap "cleanup_project ${slug}" EXIT
  _scaffold_common_fixture "${slug}"

  local output
  output="$(zsh -c 'source scripts/project_common.sh && load_project_conf "$1" && echo "ASM=${ASM_FILE}"' _ "${slug}" 2>&1)"

  assert_match "ASM=projects/${slug}/asm/${slug}.asm" "${output}"
  assert_not_match "No such file|parameter not set" "${output}" \
    "zsh must resolve the helper scripts beside project_common.sh"
}
