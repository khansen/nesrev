#!/usr/bin/env bash
set -euo pipefail

STRICT=0
CHECK_EQUATES=0
STRICT_EQUATES=0
ASM_FILE=""
for arg in "$@"; do
  case "${arg}" in
    --strict) STRICT=1 ;;
    --check-equates) CHECK_EQUATES=1 ;;
    --strict-equates) CHECK_EQUATES=1; STRICT_EQUATES=1 ;;
    -*) echo "usage: $0 <asm_file> [--strict] [--check-equates|--strict-equates]" >&2; exit 64 ;;
    *) ASM_FILE="${arg}" ;;
  esac
done

if [[ -z "${ASM_FILE}" ]]; then
  echo "usage: $0 <asm_file> [--strict] [--check-equates|--strict-equates]" >&2
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

HEX_QUANTITY_EQUATES=0
if (( CHECK_EQUATES == 1 )); then
  # A semantic quantity suffix makes these equates substantially less
  # ambiguous than general .EQU literals. ZP_/RAM_ declarations are excluded:
  # their right-hand sides are addresses even when the role ends in Count or
  # Index. Existing projects opt into strictness separately so this wider class
  # does not become a retroactive hard gate.
  HEX_QUANTITY_EQUATES="$(
    awk '
      function hex_to_dec(value,    digits, i, n, ch) {
        sub(/^\$/, "", value)
        value = toupper(value)
        digits = "0123456789ABCDEF"
        n = 0
        for (i = 1; i <= length(value); i++) {
          ch = substr(value, i, 1)
          n = (n * 16) + index(digits, ch) - 1
        }
        return n
      }
      {
        line = $0
        sub(/;.*/, "", line)
        sub(/^[[:space:]]+/, "", line)
        sub(/[[:space:]]+$/, "", line)
        if (line !~ /^[A-Za-z_][A-Za-z0-9_]*[[:space:]]+[.][Ee][Qq][Uu][[:space:]]+/) next

        symbol = line
        sub(/[[:space:]].*$/, "", symbol)
        upper_symbol = toupper(symbol)
        if (upper_symbol ~ /^(ZP_|RAM_)/) next
        if (upper_symbol !~ /_(COUNT|INDEX|IDX|RELOAD|FRAMES)$/) next

        rhs = line
        sub(/^[A-Za-z_][A-Za-z0-9_]*[[:space:]]+[.][Ee][Qq][Uu][[:space:]]+/, "", rhs)
        sub(/[[:space:]]+$/, "", rhs)
        if (rhs !~ /^\$[0-9A-Fa-f]+$/) next

        dec = hex_to_dec(rhs)
        printf("advisory: %s:%d  %s .EQU %s -> review decimal %d (quantity-suffixed equate)\n",
               FILENAME, FNR, symbol, rhs, dec) > "/dev/stderr"
        c++
      }
      END { print c + 0 }
    ' "${ASM_FILE}"
  )"
fi

echo "[base-readability] hex_quantity_equates=${HEX_QUANTITY_EQUATES}"

if (( STRICT_HEX_QUANTITY_IMMEDIATES > 0 )); then
  if (( STRICT == 1 )); then
    echo "FAIL: ${STRICT_HEX_QUANTITY_IMMEDIATES} hex zero/one immediate(s) in decimal-quantity contexts;" \
         "use decimal per agent_playbook/ASM_STYLE.md#literal-base-readability" >&2
    exit 68
  fi
  echo "advisory: ${STRICT_HEX_QUANTITY_IMMEDIATES} hex zero/one immediate(s) in decimal-quantity contexts;" \
       "prefer decimal per agent_playbook/ASM_STYLE.md#literal-base-readability" >&2
fi

if (( HEX_QUANTITY_EQUATES > 0 )); then
  if (( STRICT_EQUATES == 1 )); then
    echo "FAIL: ${HEX_QUANTITY_EQUATES} quantity-suffixed .EQU literal(s) use hex;" \
         "use decimal or signed decimal per agent_playbook/ASM_STYLE.md#literal-base-readability" >&2
    exit 69
  fi
  echo "advisory: ${HEX_QUANTITY_EQUATES} quantity-suffixed .EQU literal(s) use hex;" \
       "review decimal notation per agent_playbook/ASM_STYLE.md#literal-base-readability" >&2
fi

exit 0
