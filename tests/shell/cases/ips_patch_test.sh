#!/usr/bin/env bash

test_ips_create_apply_roundtrips_binary_delta() {
  local base="${NESREV_TEST_TMPDIR}/base.bin"
  local target="${NESREV_TEST_TMPDIR}/target.bin"
  local patch="${NESREV_TEST_TMPDIR}/delta.ips"
  local out="${NESREV_TEST_TMPDIR}/out.bin"

  printf '\x00\x01\x02\x03\x04\x05' >"${base}"
  printf '\x00\x01\xAA\xBB\x04\x05\x06' >"${target}"

  python3 scripts/ips_patch.py create "${base}" "${target}" "${patch}"
  python3 scripts/ips_patch.py apply "${base}" "${patch}" "${out}"

  cmp -s "${target}" "${out}" || fail "IPS create/apply did not round-trip target"
}

test_ips_apply_supports_rle_records() {
  local base="${NESREV_TEST_TMPDIR}/base-rle.bin"
  local patch="${NESREV_TEST_TMPDIR}/rle.ips"
  local out="${NESREV_TEST_TMPDIR}/out-rle.bin"
  local expected="${NESREV_TEST_TMPDIR}/expected-rle.bin"

  printf '\x00\x00\x00\x00\x00\x00' >"${base}"
  printf '\xAA\xAA\xAA\xAA\x00\x00' >"${expected}"
  printf 'PATCH' >"${patch}"
  printf '\x00\x00\x00\x00\x00\x00\x04\xAA' >>"${patch}"
  printf 'EOF' >>"${patch}"

  python3 scripts/ips_patch.py apply "${base}" "${patch}" "${out}"

  cmp -s "${expected}" "${out}" || fail "IPS RLE apply did not produce expected bytes"
}
