#!/usr/bin/env bash
set -euo pipefail

STRICT=0
ASM_FILE=""
for arg in "$@"; do
  case "${arg}" in
    --strict) STRICT=1 ;;
    -*) echo "usage: $0 <asm_file> [--strict]" >&2; exit 64 ;;
    *) ASM_FILE="${arg}" ;;
  esac
done

if [[ -z "${ASM_FILE}" ]]; then
  echo "usage: $0 <asm_file> [--strict]" >&2
  exit 64
fi
if [[ ! -f "${ASM_FILE}" ]]; then
  echo "error: asm file not found: ${ASM_FILE}" >&2
  exit 65
fi

# Base-readability check for the Literal Base Readability rule
# (agent_playbook/ASM_STYLE.md#literal-base-readability). It flags hex #$00 /
# #$01 immediates in contexts that are unambiguously human-readable quantities,
# where the rule requires decimal:
#   - index-register loads/compares: LDX/LDY/CPX/CPY  (a count/index seed)
#   - unit-step arithmetic:          ADC/SBC #$01     (add/subtract one)
# These carry a near-zero false-positive rate: index registers and +/-1
# arithmetic are essentially never machine tokens, masks, or pointer math, so a
# non-zero count is genuine base-by-habit debt rather than a judgment call.
# Broader LDA/AND/ORA hex zeros are intentionally NOT flagged; those legitimately
# hold tile ids, sentinels, masks, pointer-low bytes, and register-control values.
#
# Default (report) mode prints the count and per-site hints and always exits 0.
# --strict mode additionally hard-fails (exit 68) when the count is non-zero;
# project-verify uses it for projects that opt in with BASE_READABILITY_REQUIRED
# after a base pass has driven the count to zero, protecting them from regression.
STRICT_HEX_QUANTITY_IMMEDIATES="$(
  awk '
    {
      line = $0
      sub(/;.*/, "", line)                                       # drop comment
      sub(/^[[:space:]]+/, "", line)                             # left-trim
      sub(/^(@@)?[A-Za-z_][A-Za-z0-9_]*:[[:space:]]*/, "", line) # drop any leading label
      first = line
      sub(/[[:space:]].*$/, "", first)
      mn = toupper(first)
      if (mn !~ /^[A-Z]{3}(\.[A-Z])?$/) next
      op = line
      sub(/^[A-Za-z]{3}(\.[A-Za-z])?[[:space:]]+/, "", op)
      sub(/[[:space:]]+$/, "", op)
      base = mn
      sub(/\..*/, "", base)

      hit = ""
      if (base == "LDX" || base == "LDY" || base == "CPX" || base == "CPY") {
        if (op == "#$00" || op == "#$01") hit = "index/count context"
      } else if (base == "ADC" || base == "SBC") {
        if (op == "#$01") hit = "unit-step arithmetic"
      }
      if (hit != "") {
        dec = op; sub(/#\$0*/, "#", dec); if (dec == "#") dec = "#0"
        printf("advisory: %s:%d  %s %s -> use %s %s (%s)\n",
               FILENAME, FNR, mn, op, mn, dec, hit) > "/dev/stderr"
        c++
      }
    }
    END { print c + 0 }
  ' "${ASM_FILE}"
)"

echo "[base-readability] strict_hex_quantity_immediates=${STRICT_HEX_QUANTITY_IMMEDIATES}"

if (( STRICT_HEX_QUANTITY_IMMEDIATES > 0 )); then
  if (( STRICT == 1 )); then
    echo "FAIL: ${STRICT_HEX_QUANTITY_IMMEDIATES} hex zero/one immediate(s) in decimal-quantity contexts;" \
         "use decimal per agent_playbook/ASM_STYLE.md#literal-base-readability" >&2
    exit 68
  fi
  echo "advisory: ${STRICT_HEX_QUANTITY_IMMEDIATES} hex zero/one immediate(s) in decimal-quantity contexts;" \
       "prefer decimal per agent_playbook/ASM_STYLE.md#literal-base-readability" >&2
fi

exit 0
