#!/usr/bin/env bash
set -euo pipefail

load_project_conf() {
  if [[ $# -ne 1 ]]; then
    echo "usage: load_project_conf <project_slug>" >&2
    exit 64
  fi

  local slug="$1"
  local conf="projects/${slug}/project.conf"

  if [[ ! -f "${conf}" ]]; then
    echo "error: project config not found: ${conf}" >&2
    exit 65
  fi

  # Reset optional recovery settings before sourcing so repeated calls in one
  # shell cannot leak one project's controls into another project.
  NESREV_RECOVERY_STATUS="legacy"
  # Semantic-claims maturity opt-in (legacy projects default off). New scaffolds
  # set SEMANTIC_CLAIMS_REQUIRED="1" in project.conf to make the check strict.
  SEMANTIC_CLAIMS_REQUIRED="0"
  # Procedure-contract maturity opt-in (legacy projects default off). New
  # scaffolds set PROCEDURE_CONTRACTS_REQUIRED="1" so gold closeout cannot
  # silently accept a zero-contract codebase after labels are mature.
  PROCEDURE_CONTRACTS_REQUIRED="0"
  # Legacy retrofit marker opt-in (legacy projects default off). Projects that
  # have been re-audited against current gold policy set this to require a
  # machine-validated scorecard marker during maturity checks.
  LEGACY_RETROFIT_REQUIRED="0"
  # Working-notes maturity opt-in (legacy projects default off). New scaffolds
  # set WORKING_NOTES_MATURITY_REQUIRED="1" so gold closeout cannot silently
  # accept a large notes file full of promotable findings or stale pass context.
  WORKING_NOTES_MATURITY_REQUIRED="0"
  MIN_MATURITY_DOCUMENTED_PROCEDURES="1"
  MIN_MATURITY_DOCUMENTED_GLOBAL_CODE_LABELS="1"
  MAX_MATURITY_WORKING_NOTES_LINES="120"
  NESREV_CODEPOINTERS_FILE=""
  NESREV_CODEENTRIES_FILE=""
  NESREV_DATAPOINTERS_FILE=""
  NESREV_INLINECALLS_FILE=""
  NESREV_DATARANGES_FILE=""

  # shellcheck disable=SC1090
  source "${conf}"

  if [[ -z "${ASM_FILE:-}" ]]; then
    echo "error: ASM_FILE missing in ${conf}" >&2
    exit 66
  fi
  if [[ -z "${REF_NES:-}" && -n "${REF_BIN:-}" ]]; then
    REF_NES="${REF_BIN}"
  fi
  if [[ -z "${REF_NES:-}" ]]; then
    echo "error: REF_NES missing in ${conf}" >&2
    exit 67
  fi
  if [[ -z "${DOC_ROOT:-}" ]]; then
    echo "error: DOC_ROOT missing in ${conf}" >&2
    exit 68
  fi
  if [[ -z "${SYSTEMS_DOC:-}" ]]; then
    echo "error: SYSTEMS_DOC missing in ${conf}" >&2
    exit 69
  fi
  if [[ -z "${WARN_BASELINE_FILE:-}" ]]; then
    echo "error: WARN_BASELINE_FILE missing in ${conf}" >&2
    exit 70
  fi

  if [[ -z "${CROSSWALK_FILE:-}" ]]; then
    CROSSWALK_FILE="projects/${slug}/docs/crosswalk/TERMINOLOGY_CROSSWALK.md"
  fi
  if [[ -z "${ONBOARDING_FILE:-}" ]]; then
    ONBOARDING_FILE="${DOC_ROOT}/ONBOARDING.md"
  fi
  if [[ -z "${QUICK_REFERENCE_FILE:-}" ]]; then
    QUICK_REFERENCE_FILE="${DOC_ROOT}/QUICK_REFERENCE.md"
  fi
  if [[ -z "${PARITY_GAPS_FILE:-}" ]]; then
    PARITY_GAPS_FILE="${DOC_ROOT}/PARITY_GAPS.md"
  fi
  if [[ -z "${PROGRESS_SCORECARD_FILE:-}" ]]; then
    PROGRESS_SCORECARD_FILE="${DOC_ROOT}/PROGRESS_SCORECARD.md"
  fi
  if [[ -z "${RENAMES_FILE:-}" ]]; then
    RENAMES_FILE="${DOC_ROOT}/inventory/renames.csv"
  fi
  if [[ -z "${SEMANTIC_CLAIMS_FILE:-}" ]]; then
    SEMANTIC_CLAIMS_FILE="${DOC_ROOT}/SEMANTIC_CLAIMS.md"
  fi
  if [[ -z "${WORKING_NOTES_FILE:-}" ]]; then
    WORKING_NOTES_FILE="${DOC_ROOT}/WORKING_NOTES.md"
  fi
  : "${SEMANTIC_CLAIMS_REQUIRED:=0}"
  : "${PROCEDURE_CONTRACTS_REQUIRED:=0}"
  : "${LEGACY_RETROFIT_REQUIRED:=0}"
  : "${WORKING_NOTES_MATURITY_REQUIRED:=0}"
  : "${MIN_MATURITY_DOCUMENTED_PROCEDURES:=1}"
  : "${MIN_MATURITY_DOCUMENTED_GLOBAL_CODE_LABELS:=1}"
  : "${MAX_MATURITY_WORKING_NOTES_LINES:=120}"

  # Optional, tracked NESrev recovery controls. New projects declare these
  # in project.conf; older projects may omit them.
  : "${NESREV_RECOVERY_STATUS:=legacy}"
  : "${NESREV_CODEPOINTERS_FILE:=}"
  : "${NESREV_CODEENTRIES_FILE:=}"
  : "${NESREV_DATAPOINTERS_FILE:=}"
  : "${NESREV_INLINECALLS_FILE:=}"
  : "${NESREV_DATARANGES_FILE:=}"

  if [[ -z "${OUT_BIN:-}" ]]; then
    OUT_BIN="${ASM_FILE/\/asm\//\/build\/}"
    OUT_BIN="${OUT_BIN%.asm}.o"
  fi
  # Single consolidated KPI config; each runner sources it and picks its own MAX_* variable.
  : "${KPI_FILE:=${DOC_ROOT}/inventory/kpis.conf}"
  : "${RAW_KPI_FILE:=${KPI_FILE}}"
  : "${CONST_KPI_FILE:=${KPI_FILE}}"
  : "${PROC_DOC_KPI_FILE:=${KPI_FILE}}"
  : "${GLOBAL_CODE_LABEL_DOC_KPI_FILE:=${KPI_FILE}}"
  : "${BRANCH_KPI_FILE:=${KPI_FILE}}"
  : "${INFERRED_KPI_FILE:=${KPI_FILE}}"
  : "${COMMENT_KPI_FILE:=${KPI_FILE}}"
  : "${DATA_LABEL_DOC_KPI_FILE:=${KPI_FILE}}"
  : "${DATA_EXTENT_ASSERTIONS_FILE:=${DOC_ROOT}/inventory/data_extent_assertions.csv}"
  if [[ -z "${BRANCH_SITES_FILE:-}" ]]; then
    BRANCH_SITES_FILE="${DOC_ROOT}/inventory/branch_literal_sites.csv"
  fi
  if [[ -z "${POINTER_TARGETS_FILE:-}" ]]; then
    POINTER_TARGETS_FILE="${DOC_ROOT}/inventory/pointer_targets.csv"
  fi
  if [[ -z "${XASM_AUDIT_ROM_RANGE:-}" || -z "${XASM_COMPARE_CPU_BASE:-}" ]]; then
    local rom_cpu_base='$C000'
    if [[ -n "${REF_NES:-}" && -f "${REF_NES}" ]]; then
      local magic prg_units flags6 flags7 header_bits mapper_number
      magic="$(od -An -tx1 -N4 "${REF_NES}" | tr -d ' \n')"
      if [[ "${magic}" == "4e45531a" ]]; then
        prg_units="$(od -An -tu1 -j4 -N1 "${REF_NES}" | tr -d ' ')"
        flags6="$(od -An -tu1 -j6 -N1 "${REF_NES}" | tr -d ' ')"
        flags7="$(od -An -tu1 -j7 -N1 "${REF_NES}" | tr -d ' ')"
        mapper_number=$(( (flags6 >> 4) | (flags7 & 0xF0) ))
        header_bits=$(( (flags7 & 0x0C) >> 2 ))
        if (( header_bits == 2 )); then
          local nes2_byte8 nes2_byte9 nes2_mapper_high nes2_prg_units_high
          nes2_byte8="$(od -An -tu1 -j8 -N1 "${REF_NES}" | tr -d ' ')"
          nes2_byte9="$(od -An -tu1 -j9 -N1 "${REF_NES}" | tr -d ' ')"
          nes2_mapper_high=$(( nes2_byte8 & 0x0F ))
          nes2_prg_units_high=$(( nes2_byte9 & 0x0F ))
          mapper_number=$(( mapper_number | (nes2_mapper_high << 8) ))
          prg_units=$(( prg_units | (nes2_prg_units_high << 8) ))
        fi
        if [[ "${mapper_number}" == "0" && "${prg_units}" == "2" ]]; then
          rom_cpu_base='$8000'
        fi
      fi
    fi
    if [[ -z "${XASM_AUDIT_ROM_RANGE:-}" ]]; then
      XASM_AUDIT_ROM_RANGE="${rom_cpu_base}-\$FFFF"
    fi
    if [[ -z "${XASM_COMPARE_CPU_BASE:-}" ]]; then
      XASM_COMPARE_CPU_BASE="${rom_cpu_base}"
    fi
  fi
}

extract_reference_prg_from_ines() {
  if [[ $# -ne 2 ]]; then
    echo "usage: extract_reference_prg_from_ines <ref_nes> <out_prg>" >&2
    return 64
  fi

  local ref_nes="$1"
  local ref_prg="$2"

  if [[ ! -f "${ref_nes}" ]]; then
    echo "error: reference iNES file not found: ${ref_nes}" >&2
    return 1
  fi

  local ines_magic
  ines_magic="$(od -An -tx1 -N4 "${ref_nes}" | tr -d ' \n')"
  if [[ "${ines_magic}" != "4e45531a" ]]; then
    echo "error: ${ref_nes} is not a valid iNES file (bad magic)" >&2
    return 2
  fi

  local prg_units chr_units flags6 flags7
  prg_units="$(od -An -tu1 -j4 -N1 "${ref_nes}" | tr -d ' ')"
  chr_units="$(od -An -tu1 -j5 -N1 "${ref_nes}" | tr -d ' ')"
  flags6="$(od -An -tu1 -j6 -N1 "${ref_nes}" | tr -d ' ')"
  flags7="$(od -An -tu1 -j7 -N1 "${ref_nes}" | tr -d ' ')"
  if [[ -z "${prg_units}" || -z "${chr_units}" || -z "${flags6}" || -z "${flags7}" ]]; then
    echo "error: failed to parse iNES header fields from ${ref_nes}" >&2
    return 2
  fi

  local header_bits=$(( (flags7 & 0x0C) >> 2 ))
  if (( header_bits == 2 )); then
    local nes2_byte9 nes2_prg_units_high nes2_chr_units_high
    nes2_byte9="$(od -An -tu1 -j9 -N1 "${ref_nes}" | tr -d ' ')"
    if [[ -z "${nes2_byte9}" ]]; then
      echo "error: failed to parse NES 2.0 ROM size extension from ${ref_nes}" >&2
      return 2
    fi
    nes2_prg_units_high=$(( nes2_byte9 & 0x0F ))
    nes2_chr_units_high=$(( (nes2_byte9 >> 4) & 0x0F ))
    prg_units=$(( prg_units | (nes2_prg_units_high << 8) ))
    chr_units=$(( chr_units | (nes2_chr_units_high << 8) ))
  fi

  if (( prg_units <= 0 )); then
    echo "error: ${ref_nes} advertises zero PRG banks" >&2
    return 2
  fi

  local trainer_size=0
  if (( (flags6 & 0x04) != 0 )); then
    trainer_size=512
  fi

  local prg_offset=$((16 + trainer_size))
  local prg_size=$((prg_units * 16384))
  local chr_size=$((chr_units * 8192))
  local expected_size=$((prg_offset + prg_size + chr_size))
  local actual_size
  actual_size="$(wc -c < "${ref_nes}" | tr -d ' ')"
  if [[ -z "${actual_size}" || "${actual_size}" -lt "${expected_size}" ]]; then
    echo "error: ${ref_nes} is truncated; expected at least ${expected_size} bytes for advertised PRG/CHR payload, found ${actual_size:-0}" >&2
    return 2
  fi

  mkdir -p "$(dirname "${ref_prg}")"
  dd if="${ref_nes}" of="${ref_prg}" bs=1 skip="${prg_offset}" count="${prg_size}" status=none
}
