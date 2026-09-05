#!/usr/bin/env python3
"""Validate active policy-review membership and scorecard accounting."""

from __future__ import annotations

import argparse
import csv
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


MARKER_RE = re.compile(
    r"policy-baseline-audit:\s*"
    r"semantic_claims=(created|reviewed|advisory);\s*"
    r"procedures=(\d+)/(\d+);\s*"
    r"global_code_labels=(\d+)/(\d+);\s*"
    r"retained_headerless=(\d+);\s*"
    r"action=(.+?)\s*$"
)
MANIFEST_FIELDS = ("symbol", "inventory", "disposition", "localization", "rationale")
INVENTORIES = {"callable", "global", "callable+global"}
DISPOSITIONS = {"retained_headerless", "pending"}
LOCALIZATIONS = {"retain_global", "deferred", "pending"}


@dataclass(frozen=True)
class Marker:
    line_no: int
    pass_id: int
    semantic_claims: str
    procedures_reviewed: int
    procedures_denominator: int
    global_reviewed: int
    global_denominator: int
    retained_headerless: int
    action: str


def parse_scorecard_marker(scorecard_path: Path) -> tuple[Marker | None, list[str]]:
    errors: list[str] = []
    header: list[str] | None = None
    header_index: dict[str, int] | None = None
    markers: list[Marker] = []

    try:
        lines = scorecard_path.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        return None, [f"scorecard not found: {scorecard_path}"]

    for line_no, raw in enumerate(lines, start=1):
        stripped = raw.strip()
        if not (stripped.startswith("|") and stripped.endswith("|")):
            continue
        cells = [cell.strip() for cell in stripped.strip("|").split("|")]
        if "pass_id" in cells and "notes" in cells:
            header = cells
            header_index = {name: idx for idx, name in enumerate(header)}
            continue
        if "policy-baseline-audit:" not in raw:
            continue
        if header is None or header_index is None:
            errors.append(f"{scorecard_path}:{line_no}: marker appears before scorecard header")
            continue
        if len(cells) != len(header):
            errors.append(f"{scorecard_path}:{line_no}: marker row column count mismatch")
            continue
        try:
            pass_id = int(cells[header_index["pass_id"]])
            notes = cells[header_index["notes"]]
        except ValueError:
            errors.append(f"{scorecard_path}:{line_no}: marker row missing numeric pass_id or notes cell")
            continue

        marker_start = notes.find("policy-baseline-audit:")
        if marker_start == -1:
            errors.append(f"{scorecard_path}:{line_no}: policy-baseline-audit marker must live in the notes column")
            continue
        marker_text = notes[marker_start:].strip()
        match = MARKER_RE.match(marker_text)
        if match is None:
            errors.append(f"{scorecard_path}:{line_no}: malformed policy-baseline-audit marker")
            continue

        action = match.group(7).strip()
        if not action:
            errors.append(f"{scorecard_path}:{line_no}: policy-baseline-audit action must not be empty")
            continue

        markers.append(
            Marker(
                line_no=line_no,
                pass_id=pass_id,
                semantic_claims=match.group(1),
                procedures_reviewed=int(match.group(2)),
                procedures_denominator=int(match.group(3)),
                global_reviewed=int(match.group(4)),
                global_denominator=int(match.group(5)),
                retained_headerless=int(match.group(6)),
                action=action,
            )
        )

    if errors:
        return None, errors
    if not markers:
        return None, []
    return max(markers, key=lambda m: (m.pass_id, m.line_no)), []


def run_detail_kpi(
    script_path: Path, asm_path: Path, metric_name: str
) -> tuple[dict[str, int], list[str]]:
    errors: list[str] = []
    members: dict[str, int] = {}
    with tempfile.NamedTemporaryFile(prefix="policy_baseline_detail.", delete=False) as detail_file:
        detail_path = Path(detail_file.name)
    try:
        env = dict(os.environ)
        env["KPI_DETAIL_FILE"] = str(detail_path)
        proc = subprocess.run(
            ["bash", str(script_path), str(asm_path)],
            check=False,
            capture_output=True,
            text=True,
            env=env,
        )
        if proc.returncode != 0:
            errors.append(
                f"{script_path.name} failed with exit {proc.returncode}: "
                f"{proc.stderr.strip() or proc.stdout.strip()}"
            )
            return members, errors

        details = [line for line in detail_path.read_text(encoding="utf-8").splitlines() if line.strip()]
        detail_count = len(details)
        for detail in details:
            match = re.fullmatch(r"([1-9]\d*):([A-Za-z_][A-Za-z0-9_]*)", detail)
            if match is None:
                errors.append(f"{script_path.name} emitted malformed detail: {detail!r}")
                continue
            line_no, symbol = match.groups()
            if symbol in members:
                errors.append(f"{script_path.name} emitted duplicate detail symbol: {symbol}")
            members[symbol] = int(line_no)
        metric_match = re.search(rf"^{re.escape(metric_name)}=(\d+)$", proc.stdout, re.MULTILINE)
        if metric_match is None:
            errors.append(f"{script_path.name} did not emit {metric_name}")
            return members, errors
        metric_count = int(metric_match.group(1))
        if metric_count != detail_count:
            errors.append(
                f"{script_path.name} detail line count {detail_count} does not match "
                f"{metric_name}={metric_count}"
            )
        return members, errors
    finally:
        detail_path.unlink(missing_ok=True)


def check_manifest(
    manifest_path: Path, marker: Marker, procedures: set[str], globals_: set[str]
) -> list[str]:
    errors: list[str] = []
    members: set[str] = set()
    retained: set[str] = set()
    expected = procedures | globals_
    try:
        with manifest_path.open(encoding="utf-8", newline="") as manifest_file:
            reader = csv.DictReader(manifest_file, strict=True)
            if reader.fieldnames != list(MANIFEST_FIELDS):
                return [f"{manifest_path}: expected CSV header {','.join(MANIFEST_FIELDS)}"]
            for raw in reader:
                location = f"{manifest_path}:{reader.line_num}"
                if None in raw or any(value is None for value in raw.values()):
                    errors.append(f"{location}: manifest row column count mismatch")
                    continue
                row = {key: value.strip() for key, value in raw.items()}
                symbol = row["symbol"]
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", symbol):
                    errors.append(f"{location}: invalid global symbol {symbol!r}")
                if symbol in members:
                    errors.append(f"{location}: duplicate manifest symbol {symbol}")
                members.add(symbol)
                if row["inventory"] not in INVENTORIES:
                    errors.append(f"{location}: invalid inventory {row['inventory']!r}")
                elif symbol in expected:
                    inventory = (
                        "callable+global" if symbol in procedures and symbol in globals_
                        else "callable" if symbol in procedures else "global"
                    )
                    if row["inventory"] != inventory:
                        errors.append(f"{location}: {symbol} inventory must be {inventory}")
                if row["disposition"] not in DISPOSITIONS:
                    errors.append(f"{location}: invalid disposition {row['disposition']!r}")
                if row["localization"] not in LOCALIZATIONS:
                    errors.append(f"{location}: invalid localization {row['localization']!r}")
                if not row["rationale"]:
                    errors.append(f"{location}: rationale must not be empty")
                if row["disposition"] == "retained_headerless":
                    retained.add(symbol)
                    if row["localization"] == "pending":
                        errors.append(f"{location}: reviewed {symbol} requires a localization decision")
    except (OSError, UnicodeError, csv.Error) as exc:
        return [f"cannot read active policy manifest {manifest_path}: {exc}"]

    for symbol in sorted(expected - members):
        errors.append(f"{manifest_path}: missing live detail symbol {symbol}")
    for symbol in sorted(members - expected):
        errors.append(f"{manifest_path}: {symbol} is not in the live detail union")
    for label, recorded, actual in (
        ("procedures reviewed", marker.procedures_reviewed, len(retained & procedures)),
        ("global_code_labels reviewed", marker.global_reviewed, len(retained & globals_)),
        ("retained_headerless", marker.retained_headerless, len(retained)),
    ):
        if recorded != actual:
            errors.append(f"{label} count {recorded} does not match active manifest count {actual}")
    return errors


def check_semantic_claims(marker: Marker, asm_path: Path, claims_path: Path, scripts_dir: Path) -> list[str]:
    if marker.semantic_claims == "advisory":
        return []

    checker = scripts_dir / "project_semantic_claims_check.py"
    proc = subprocess.run(
        [
            "python3",
            str(checker),
            str(asm_path),
            str(claims_path),
            "--mode",
            "maturity",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0:
        return []
    detail = proc.stderr.strip() or proc.stdout.strip()
    return [
        f"semantic_claims={marker.semantic_claims} requires a maturity-valid "
        f"SEMANTIC_CLAIMS.md ledger: {detail}"
    ]


def validate(args: argparse.Namespace) -> int:
    scorecard_path = Path(args.scorecard)
    asm_path = Path(args.asm)
    scripts_dir = Path(args.scripts_dir)
    marker, errors = parse_scorecard_marker(scorecard_path)
    if errors:
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if marker is None:
        if args.require:
            print(
                "FAIL: universal current-policy audit requires a valid "
                "policy-baseline-audit marker",
                file=sys.stderr,
            )
            return 1
        print("NOT CHECKED: no policy-baseline-audit marker recorded (advisory)")
        return 0

    procedures, proc_errors = run_detail_kpi(
        scripts_dir / "procedure_doc_kpi.sh",
        asm_path,
        "strict_callable_procedures_undocumented",
    )
    globals_, global_errors = run_detail_kpi(
        scripts_dir / "global_code_label_doc_kpi.sh",
        asm_path,
        "strict_global_code_labels_undocumented",
    )
    errors.extend(proc_errors)
    errors.extend(global_errors)
    proc_detail_count = len(procedures)
    global_detail_count = len(globals_)
    manifest_path = Path(args.manifest) if args.manifest else scorecard_path.parent / "inventory/policy_baseline.csv"
    if not proc_errors and not global_errors:
        errors.extend(check_manifest(manifest_path, marker, set(procedures), set(globals_)))

    if marker.procedures_denominator != proc_detail_count:
        errors.append(
            f"procedures denominator {marker.procedures_denominator} does not match "
            f"live procedure detail line count {proc_detail_count}"
        )
    if marker.global_denominator != global_detail_count:
        errors.append(
            f"global_code_labels denominator {marker.global_denominator} does not match "
            f"live global-code-label detail line count {global_detail_count}"
        )
    if marker.procedures_reviewed > marker.procedures_denominator:
        errors.append("procedures reviewed count exceeds its denominator")
    if marker.global_reviewed > marker.global_denominator:
        errors.append("global_code_labels reviewed count exceeds its denominator")
    errors.extend(
        check_semantic_claims(
            marker,
            asm_path,
            Path(args.semantic_claims),
            scripts_dir,
        )
    )
    if args.require and marker.semantic_claims == "advisory":
        errors.append(
            "universal current-policy audit requires semantic_claims=created or reviewed"
        )

    complete = (
        marker.procedures_reviewed == marker.procedures_denominator
        and marker.global_reviewed == marker.global_denominator
    )
    if args.require and not complete:
        errors.append(
            "universal current-policy audit requires complete audit fractions "
            f"(procedures={marker.procedures_reviewed}/{marker.procedures_denominator}; "
            f"global_code_labels={marker.global_reviewed}/{marker.global_denominator})"
        )

    if errors:
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        return 1

    status = "complete" if complete else "in-progress"
    print(
        "OK: policy baseline audit marker "
        f"{status} at {scorecard_path}:{marker.line_no} "
        f"(semantic_claims={marker.semantic_claims}; "
        f"procedures={marker.procedures_reviewed}/{marker.procedures_denominator}; "
        f"global_code_labels={marker.global_reviewed}/{marker.global_denominator}; "
        f"retained_headerless={marker.retained_headerless}; "
        f"manifest={manifest_path}; distinct_candidates={len(set(procedures) | set(globals_))})"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--asm", required=True)
    parser.add_argument("--scorecard", required=True)
    parser.add_argument("--semantic-claims", required=True)
    parser.add_argument("--scripts-dir", required=True)
    parser.add_argument("--manifest", help="active CSV; defaults to inventory/policy_baseline.csv beside the scorecard")
    parser.add_argument("--require", action="store_true")
    return validate(parser.parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
