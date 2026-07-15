#!/usr/bin/env bash
# Tests the core data-format target inventory checker.

DATA_FORMAT_TARGETS_CHECK="${REPO_ROOT}/scripts/data_format_targets_check.py"

_write_scaffold_targets() {
  local path="$1"
  # Keep this fixture aligned with CANONICAL_FAMILIES in
  # scripts/data_format_targets_check.py and the scaffold in scripts/new_project.sh.
  # The fresh-project process-check integration test catches scaffold/checker drift.
  cat > "${path}" <<'CSV'
family,disposition,artifact,evidence
levels_rooms_maps,not_yet_reviewed,,intake scaffold - identify level room map screen area transition or track data
objects_actors_enemies_hazards,not_yet_reviewed,,intake scaffold - identify object actor enemy hazard and spawn definitions
items_pickups_powerups,not_yet_reviewed,,intake scaffold - identify item pickup powerup inventory or reward formats
projectiles_collision,not_yet_reviewed,,intake scaffold - identify projectile collision hitbox or damage formats
behavior_state_movement_animation,not_yet_reviewed,,intake scaffold - identify behavior state action movement and animation streams
metasprites_sprite_animation,not_yet_reviewed,,intake scaffold - identify metasprite sprite strip frame and coordinate formats
graphics_tiles_chr_nametables,not_yet_reviewed,,intake scaffold - identify graphics tile CHR nametable attribute and image formats
ppu_packet_update_streams,not_yet_reviewed,,intake scaffold - identify PPU packet VRAM update queue and screen-transfer streams
audio_music_jingles,not_yet_reviewed,,intake scaffold - identify music jingle song channel instrument and envelope formats
audio_sfx_cues,not_yet_reviewed,,intake scaffold - identify SFX cue request effect-state and channel formats
password_save_progression,not_yet_reviewed,,intake scaffold - identify password save progression checkpoint or mark absent
CSV
}

_write_mature_targets() {
  local path="$1"
  cat > "${path}" <<'CSV'
family,disposition,artifact,evidence
levels_rooms_maps,documented,ROOM_FORMAT.md,room format doc covers the level map and room stream model
objects_actors_enemies_hazards,absent_not_applicable,,project has no actor or enemy system
items_pickups_powerups,absent_not_applicable,,project has no collectible item system
projectiles_collision,absent_not_applicable,,project has no projectile or collision data
behavior_state_movement_animation,runtime_gated,,static tables are absent; runtime traces would be needed if behavior appears later
metasprites_sprite_animation,documented,METASPRITE_FORMAT.md,metasprite records are documented with parser evidence
graphics_tiles_chr_nametables,documented,GRAPHICS_FORMAT.md,graphics data formats are documented with consumer evidence
ppu_packet_update_streams,documented,PPU_FORMAT.md,PPU packet stream format is documented
audio_music_jingles,documented,AUDIO_FORMAT.md,audio doc explicitly covers music and jingles
audio_sfx_cues,documented,AUDIO_FORMAT.md,audio doc explicitly covers SFX cues
password_save_progression,absent_not_applicable,,project has no password or save system
CSV
}

_touch_mature_docs() {
  local doc_root="$1"
  for doc in ROOM_FORMAT.md METASPRITE_FORMAT.md GRAPHICS_FORMAT.md PPU_FORMAT.md AUDIO_FORMAT.md; do
    printf '# %s\n' "${doc}" > "${doc_root}/${doc}"
  done
}

test_data_format_targets_process_accepts_scaffold_rows() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  _write_scaffold_targets "${inv}"

  assert_exit 0 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode process --required
}

test_data_format_targets_maturity_rejects_unreviewed_rows() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  _write_scaffold_targets "${inv}"

  assert_exit 1 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode maturity --required
}

test_data_format_targets_maturity_accepts_dispositioned_rows() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  _write_mature_targets "${inv}"
  _touch_mature_docs "${doc_root}"

  assert_exit 0 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode maturity --required
}

test_data_format_targets_required_rejects_missing_canonical_family() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  cat > "${inv}" <<'CSV'
family,disposition,artifact,evidence
levels_rooms_maps,absent_not_applicable,,project has no level data
CSV

  assert_exit 1 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode process --required
}

test_data_format_targets_documented_artifact_must_exist() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  _write_mature_targets "${inv}"

  assert_exit 1 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode maturity --required
}

test_data_format_targets_rejects_unquoted_commas() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  cat > "${inv}" <<'CSV'
family,disposition,artifact,evidence
levels_rooms_maps,absent_not_applicable,,project has no rooms, maps, or stages
CSV

  assert_exit 1 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode process
}

test_data_format_targets_absent_rows_must_not_link_artifacts() {
  local doc_root="${NESREV_TEST_TMPDIR}/docs"
  local inv="${NESREV_TEST_TMPDIR}/data_format_targets.csv"
  mkdir -p "${doc_root}"
  printf '# Notes\n' > "${doc_root}/NOTES.md"
  cat > "${inv}" <<'CSV'
family,disposition,artifact,evidence
levels_rooms_maps,absent_not_applicable,NOTES.md,project has no level data
CSV

  assert_exit 1 python3 "${DATA_FORMAT_TARGETS_CHECK}" \
    "${inv}" --doc-root "${doc_root}" --mode process
}
