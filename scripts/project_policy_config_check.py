#!/usr/bin/env python3
"""Reject project configuration that selects repository quality policy."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


FORBIDDEN_POLICY_FIELDS = (
    "SEMANTIC_CLAIMS_REQUIRED",
    "PROCEDURE_CONTRACTS_REQUIRED",
    "LEGACY_RETROFIT_REQUIRED",
    "WORKING_NOTES_MATURITY_REQUIRED",
    "PROOF_DEBT_REQUIRED",
    "DATA_FORMAT_TARGETS_REQUIRED",
    "DATA_BLOB_DISPOSITIONS_REQUIRED",
    "EMBEDDED_POINTER_AUDIT_REQUIRED",
    "BASE_READABILITY_REQUIRED",
    "BASE_READABILITY_EQU_REQUIRED",
    "SCORECARD_LIFECYCLE_REQUIRED",
)
VALID_RECOVERY_STATUSES = {"pending", "none", "configured"}
ALLOWED_PROJECT_FACT_FIELDS = {
    "PROJECT_NAME",
    "ASM_FILE",
    "REF_NES",
    "REF_BIN",  # compatibility alias normalized by project_common.sh
    "OUT_BIN",
    "DOC_ROOT",
    "SYSTEMS_DOC",
    "WARN_BASELINE_FILE",
    "CROSSWALK_FILE",
    "ONBOARDING_FILE",
    "QUICK_REFERENCE_FILE",
    "PARITY_GAPS_FILE",
    "PROGRESS_SCORECARD_FILE",
    "RENAMES_FILE",
    "SEMANTIC_CLAIMS_FILE",
    "WORKING_NOTES_FILE",
    "KPI_FILE",
    "RAW_KPI_FILE",
    "CONST_KPI_FILE",
    "PROC_DOC_KPI_FILE",
    "GLOBAL_CODE_LABEL_DOC_KPI_FILE",
    "BRANCH_KPI_FILE",
    "INFERRED_KPI_FILE",
    "COMMENT_KPI_FILE",
    "DATA_LABEL_DOC_KPI_FILE",
    "DATA_EXTENT_ASSERTIONS_FILE",
    "DATA_FORMAT_TARGETS_FILE",
    "DATA_BLOB_DISPOSITIONS_FILE",
    "BRANCH_SITES_FILE",
    "POINTER_TARGETS_FILE",
    "EMBEDDED_POINTER_TARGETS_FILE",
    "SPLIT_POINTER_TARGETS_FILE",
    "XASM_AUDIT_ROM_RANGE",
    "XASM_COMPARE_CPU_BASE",
    "MIN_MATURITY_DOCUMENTED_PROCEDURES",
    "MIN_MATURITY_DOCUMENTED_GLOBAL_CODE_LABELS",
    "MAX_MATURITY_WORKING_NOTES_LINES",
    "NESREV_RECOVERY_STATUS",
    "NESREV_CODEPOINTERS_FILE",
    "NESREV_CODEENTRIES_FILE",
    "NESREV_DATAPOINTERS_FILE",
    "NESREV_INLINECALLS_FILE",
    "NESREV_DATARANGES_FILE",
}
ASSIGNMENT_RE = re.compile(
    r"^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*?)\s*(?:#.*)?$"
)
SENTINEL_RE = re.compile(r"^MAX_[A-Z0-9_]+$")
DISABLING_CEILING_MINIMUM = 100_000
QUALITY_WRAPPERS = (
    "project_verify.sh",
    "project_process_check.sh",
    "project_docs_check.sh",
    "project_prior_reuse_check.sh",
    "project_maturity_check.sh",
    "project_maturity_summary.sh",
    "project_next_pass.sh",
    "projects_policy_check.sh",
    "projects_ci.sh",
    "check_docs.sh",
)
UNIVERSAL_ARTIFACT_FIELDS = {
    "EMBEDDED_POINTER_TARGETS_FILE",
    "SPLIT_POINTER_TARGETS_FILE",
    "DATA_FORMAT_TARGETS_FILE",
    "DATA_BLOB_DISPOSITIONS_FILE",
    "SEMANTIC_CLAIMS_FILE",
}
# Every upper-case variable that may appear in a shell predicate in a quality
# wrapper is classified here. Adding an arbitrary project.conf field and using
# it as a gate therefore fails closed until the repository contract explicitly
# identifies it as a fact or a bounded one-run workflow input.
ALLOWED_CONDITIONAL_FIELDS = {
    "PROJECT_VERIFY_REFRESH_INVENTORY",  # one-run wrapper refresh request
    "DATA_BLOB_RENAMED_PASS",  # closeout-scoped pass identifier
    "ASM_FILE",
    "SYSTEMS_DOC",
    "DOC_ROOT",
    "WARN_BASELINE_FILE",
    "RENAMES_FILE",
    "RAW_RAM_REVIEW_FILE",
    "NESREV_XREF_FILE",  # shared-artifact reuse, never check applicability
    "DATA_FORMAT_TARGETS_FILE",
    "DATA_BLOB_DISPOSITIONS_FILE",
    "TMPDIR_CHECK_DOCS",  # wrapper-owned temporary workspace
    "FORMAT",  # validated presentation choice
    "PROJECT_NEXT_PASS_AUTO_PREP",  # one-run cache refresh control
    "CURRENT_HEAD",
    "HEAD_MARKER",
    "NEEDS_PREP",
}
CONDITIONAL_VARIABLE_RE = re.compile(r"\$(?:\{)?([A-Z][A-Z0-9_]*)")
EXPECTED_WRAPPER_TOKENS = {
    "project_verify.sh": (
        "project_policy_config_check.py\" kpis",
        "pointer_targets_check.sh",
        "embedded_pointer_targets_check.sh",
        "split_pointer_targets_check.sh",
        "embedded_pointer_audit.py",
        "--strict --strict-equates",
    ),
    "project_process_check.sh": (
        "project_artifact_manifest.py",
        "scorecard_lifecycle_check.py",
        "project_prior_reuse_check.sh",
        "raw_immediate_constant_check.py",
        "semantic_evidence_check.py",
        "ppu_packet_line_check.py",
        "negative_data_offset_check.py",
        "rename_reason_consistency_check.py",
        "oam_standard_prose_check.py",
        "data_format_targets_check.py",
        "data_blob_dispositions_check.py",
    ),
    "project_docs_check.sh": ("check_docs.sh", "--mode strict"),
    "project_prior_reuse_check.sh": ("scorecard_analogue.py",),
    "project_maturity_check.sh": (
        "embedded_pointer_targets_check.sh",
        "split_pointer_targets_check.sh",
        "embedded_pointer_audit.py",
        "project_policy_baseline_check.sh",
        "working_notes_maturity_check.sh",
        "--mode maturity",
    ),
    "project_maturity_summary.sh": (
        "data_format_targets_summary.py",
        "proof_debt.py",
        "symbol_vocabulary_check.py",
    ),
    "project_next_pass.sh": (
        "proof_debt.collect(",
        "if _r.returncode != 0:",
    ),
    "projects_policy_check.sh": ("git ls-files 'projects/*/project.conf'",),
    "projects_ci.sh": ("git ls-files 'projects/*/project.conf'",),
}


def assignments(path: Path) -> dict[str, tuple[str, int]]:
    found: dict[str, tuple[str, int]] = {}
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        raise ValueError(f"cannot read {path}: {exc}") from exc
    for line_no, raw in enumerate(lines, start=1):
        match = ASSIGNMENT_RE.match(raw)
        if not match:
            continue
        value = match.group(2).strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in {'\"', "'"}:
            value = value[1:-1]
        found[match.group(1)] = (value, line_no)
    return found


def validate_config(path: Path, tracked: bool = False) -> list[str]:
    errors: list[str] = []
    try:
        fields = assignments(path)
    except ValueError as exc:
        return [str(exc)]
    for name in FORBIDDEN_POLICY_FIELDS:
        if name in fields:
            errors.append(
                f"{path}:{fields[name][1]}: {name} is a removed quality-policy switch; "
                "delete it because all project gates are mandatory"
            )
    for name, (_, line_no) in fields.items():
        if name not in ALLOWED_PROJECT_FACT_FIELDS and name not in FORBIDDEN_POLICY_FIELDS:
            errors.append(
                f"{path}:{line_no}: {name} is not a declared project fact; "
                "project.conf may not introduce workflow or quality-policy controls"
            )
    recovery = fields.get("NESREV_RECOVERY_STATUS")
    if recovery is None:
        errors.append(
            f"{path}: NESREV_RECOVERY_STATUS must be declared explicitly as "
            "pending, none, or configured"
        )
    else:
        value, line_no = recovery
        if value not in VALID_RECOVERY_STATUSES:
            errors.append(
                f"{path}:{line_no}: NESREV_RECOVERY_STATUS={value!r}; expected "
                "pending, none, or configured (legacy is not a valid policy state)"
            )
        elif tracked and value == "pending":
            errors.append(
                f"{path}:{line_no}: tracked projects must finish recovery discovery and "
                "record NESREV_RECOVERY_STATUS as none or configured"
            )
    return errors


def validate_kpis(path: Path) -> list[str]:
    errors: list[str] = []
    try:
        fields = assignments(path)
    except ValueError as exc:
        return [str(exc)]
    for name, (value, line_no) in fields.items():
        if not SENTINEL_RE.match(name):
            continue
        try:
            ceiling = int(value, 10)
        except ValueError:
            errors.append(f"{path}:{line_no}: {name} must be a finite non-negative integer")
            continue
        if ceiling < 0:
            errors.append(f"{path}:{line_no}: {name} must be non-negative")
        if ceiling >= DISABLING_CEILING_MINIMUM:
            errors.append(
                f"{path}:{line_no}: {name}={ceiling} is a disabled/sentinel ceiling; "
                "replace it with the current measured finite ratchet"
            )
    return errors


def validate_wrapper_contract(repo: Path) -> list[str]:
    errors: list[str] = []
    scripts = repo / "scripts"
    for wrapper in QUALITY_WRAPPERS:
        path = scripts / wrapper
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(f"cannot read quality wrapper {path}: {exc}")
            continue
        for name in FORBIDDEN_POLICY_FIELDS:
            if name in text:
                errors.append(
                    f"{path}: quality wrapper still depends on removed policy field {name}"
                )
        for line_no, line in enumerate(text.splitlines(), start=1):
            if not re.search(r"\b(?:if|elif)\b", line):
                continue
            if "[[" in line or "((" in line:
                for name in CONDITIONAL_VARIABLE_RE.findall(line):
                    if name not in ALLOWED_CONDITIONAL_FIELDS:
                        errors.append(
                            f"{path}:{line_no}: unclassified config-style variable {name} "
                            "appears in a quality-wrapper conditional; project facts may "
                            "select inputs, not check execution or strictness"
                        )
            # A path remains useful as an input and in an unconditional
            # check's error handling.  Only a file-test predicate makes the
            # path an opt-in switch by allowing absence to skip the check.
            if not re.search(r"\[\[\s+-(?:e|f|r|s)\s", line):
                continue
            for name in UNIVERSAL_ARTIFACT_FIELDS:
                if name in line:
                    errors.append(
                        f"{path}:{line_no}: {name} may supply a path but may not "
                        "select whether its quality check runs"
                    )
        if wrapper in {
            "project_process_check.sh",
            "project_docs_check.sh",
            "project_prior_reuse_check.sh",
            "check_docs.sh",
        } and "NESREV_RECOVERY_STATUS" in text:
            errors.append(
                f"{path}: recovery-discovery facts must not select quality-check execution or strictness"
            )
        for token in EXPECTED_WRAPPER_TOKENS.get(wrapper, ()):
            if token not in text:
                errors.append(f"{path}: universal quality-check token missing: {token}")
        if wrapper == "project_process_check.sh":
            for checker in (
                "check_hardware_constant_drift.py",
                "raw_immediate_constant_check.py",
                "semantic_evidence_check.py",
                "ppu_packet_line_check.py",
                "negative_data_offset_check.py",
                "rename_reason_consistency_check.py",
                "oam_standard_prose_check.py",
                "data_extent_missing_scan.py",
            ):
                command = re.search(rf"{re.escape(checker)}(.{{0,300}}?)(?:\n\n|$)", text, re.S)
                if command and "|| true" in command.group(0):
                    errors.append(
                        f"{path}: {checker} operational failure is suppressed; "
                        "advisory findings may be soft, checker failures may not"
                    )
        if wrapper in {"projects_policy_check.sh", "projects_ci.sh"} and re.search(
            r"\b(?:PROJECTS|ALLOWLIST)\s*=|allowlist", text, re.I
        ):
            errors.append(f"{path}: aggregate project discovery must not use an allowlist")
    return errors


def tracked_configs(repo: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "projects/*/project.conf"],
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [repo / line for line in result.stdout.splitlines() if line]


def report(errors: list[str]) -> int:
    for message in errors:
        print(f"project_policy_config_check: {message}", file=sys.stderr)
    return 1 if errors else 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    config = sub.add_parser("config")
    config.add_argument("path", type=Path)
    config.add_argument("--tracked", action="store_true")
    kpis = sub.add_parser("kpis")
    kpis.add_argument("path", type=Path)
    wrappers = sub.add_parser("wrappers")
    wrappers.add_argument("repo", type=Path, nargs="?", default=Path("."))
    corpus = sub.add_parser("corpus")
    corpus.add_argument("repo", type=Path, nargs="?", default=Path("."))
    args = parser.parse_args(argv)

    if args.command == "config":
        return report(validate_config(args.path, tracked=args.tracked))
    if args.command == "kpis":
        return report(validate_kpis(args.path))
    if args.command == "wrappers":
        return report(validate_wrapper_contract(args.repo.resolve()))

    repo = args.repo.resolve()
    errors = validate_wrapper_contract(repo)
    configs = tracked_configs(repo)
    if not configs:
        errors.append("no tracked projects/*/project.conf files found")
    for path in configs:
        errors.extend(validate_config(path, tracked=True))
        project_dir = path.parent
        kpi_path = project_dir / "docs/reverse_engineering/inventory/kpis.conf"
        errors.extend(validate_kpis(kpi_path))
    return report(errors)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
