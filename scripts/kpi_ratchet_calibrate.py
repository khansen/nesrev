#!/usr/bin/env python3
"""Replace a new project's pending KPI scaffold with measured finite ratchets."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


PENDING_MARKER = "# Intake calibration pending."
MEASUREMENTS = (
    ("raw_address_kpi.sh", "strict_active_raw_lowaddr", "MAX_ACTIVE_RAW_LOWADDR"),
    ("raw_address_kpi.sh", "strict_active_raw_absrom", "MAX_ACTIVE_RAW_ABSROM"),
    ("constant_kpi.sh", "strict_active_magic_immediates", "MAX_ACTIVE_MAGIC_IMMEDIATES"),
    ("branch_literal_kpi.sh", "strict_active_branch_literals", "MAX_ACTIVE_BRANCH_LITERALS"),
    ("inferred_kpi.sh", "strict_inferred_annotations", "MAX_INFERRED_ANNOTATIONS"),
    ("comment_quality_kpi.sh", "strict_placeholder_comments", "MAX_PLACEHOLDER_COMMENTS"),
    (
        "procedure_doc_kpi.sh",
        "strict_callable_procedures_undocumented",
        "MAX_UNDOCUMENTED_PROCEDURES",
    ),
    (
        "global_code_label_doc_kpi.sh",
        "strict_global_code_labels_undocumented",
        "MAX_UNDOCUMENTED_GLOBAL_CODE_LABELS",
    ),
    (
        "data_label_doc_kpi.sh",
        "strict_data_labels_noncompliant",
        "MAX_UNDOCUMENTED_DATA_LABELS",
    ),
)


def measure(script_dir: Path, asm: Path) -> dict[str, int]:
    reports: dict[str, str] = {}
    values: dict[str, int] = {}
    for script, metric, ceiling in MEASUREMENTS:
        if script not in reports:
            result = subprocess.run(
                ["bash", str(script_dir / script), str(asm)],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
            )
            reports[script] = result.stdout
        match = re.search(rf"(?:^|\s){re.escape(metric)}=(\d+)(?:\s|$)", reports[script])
        if not match:
            raise ValueError(f"{script} did not report {metric}")
        values[ceiling] = int(match.group(1), 10)
    return values


def calibrate(path: Path, values: dict[str, int]) -> None:
    text = path.read_text(encoding="utf-8")
    if PENDING_MARKER not in text:
        raise ValueError(
            f"{path} is not an uncalibrated intake scaffold; refusing to reset reviewed ratchets"
        )
    for name, value in values.items():
        pattern = re.compile(rf"(?m)^{re.escape(name)}=\d+$")
        text, count = pattern.subn(f"{name}={value}", text)
        if count != 1:
            raise ValueError(f"{path} must define {name} exactly once")
    text = text.replace(
        PENDING_MARKER,
        "# Finite intake baseline; tighten only with semantic/readability progress.",
        1,
    )
    path.write_text(text, encoding="utf-8")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: kpi_ratchet_calibrate.py <asm> <kpis.conf>", file=sys.stderr)
        return 64
    asm, kpis = map(Path, argv)
    try:
        values = measure(Path(__file__).resolve().parent, asm)
        calibrate(kpis, values)
    except (OSError, subprocess.CalledProcessError, ValueError) as exc:
        print(f"kpi_ratchet_calibrate: {exc}", file=sys.stderr)
        return 1
    print(f"OK: calibrated finite KPI ratchets in {kpis}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
