#!/usr/bin/env python3
"""Replace a new project's pending KPI scaffold with measured finite ratchets."""

from __future__ import annotations

import re
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import analysis_bundle as analysis


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


def measure(script_dir: Path, asm: Path, instruction_bundle=None) -> dict[str, int]:
    reports: dict[str, str] = {}
    values: dict[str, int] = {}
    for script, metric, ceiling in MEASUREMENTS:
        if script not in reports:
            result = subprocess.run(
                ["bash", str(script_dir / script), str(asm)],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
                env=(dict(os.environ, NESREV_ANALYSIS_BUNDLE=str(instruction_bundle))
                     if script in {"branch_literal_kpi.sh", "raw_address_kpi.sh"}
                     and instruction_bundle is not None else None),
            )
            reports[script] = result.stdout
        matches = re.findall(rf"(?:^|\s){re.escape(metric)}=([^\s]+)", reports[script])
        if len(matches) != 1 or re.fullmatch(r"[0-9]+", matches[0]) is None:
            raise ValueError(f"{script} did not report {metric}")
        values[ceiling] = int(matches[0], 10)
    return values


def calibrate(path: Path, values: dict[str, int], before_publish=lambda: None) -> None:
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
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        staged = Path(stream.name)
        try:
            stream.write(text)
            stream.close()
            before_publish()
            os.replace(staged, path)
        finally:
            staged.unlink(missing_ok=True)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: kpi_ratchet_calibrate.py <asm> <kpis.conf>", file=sys.stderr)
        return 64
    asm, kpis = map(Path, argv)
    try:
        if PENDING_MARKER not in kpis.read_text(encoding="utf-8"):
            raise ValueError(f"{kpis} is not an uncalibrated intake scaffold; refusing to reset reviewed ratchets")
        with tempfile.TemporaryDirectory(prefix="nesrev-calibrate-") as directory:
            shared = analysis.supplied(asm)
            if shared is None:
                analysis.prepare_source(directory, asm, [kpis])
                rc = analysis.produce(directory, asm, Path(directory) / "output.bin")
                if rc:
                    raise ValueError(f"instruction production failed (exit {rc})")
                shared = analysis.Bundle(Path(directory) / "bundle.json", asm)
            shared.require_policy(kpis)
            values = measure(Path(__file__).resolve().parent, asm, shared.path)
            calibrate(kpis, values, shared.validate)
    except (OSError, subprocess.CalledProcessError, ValueError) as exc:
        print(f"kpi_ratchet_calibrate: {exc}", file=sys.stderr)
        return 1
    print(f"OK: calibrated finite KPI ratchets in {kpis}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
