#!/usr/bin/env python3
"""Validate the canonical authored project artifact set."""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Artifact:
    relative_path: str
    header: str | None
    remedy: str


ARTIFACTS = (
    Artifact("SEMANTIC_CLAIMS.md", None, "create the pass-time semantic-claims ledger"),
    Artifact("inventory/data_extent_assertions.csv", "label,expected_size,reason", "create the canonical extent ledger"),
    Artifact("inventory/data_format_targets.csv", "family,disposition,artifact,evidence", "record pass-time family dispositions"),
    Artifact(
        "inventory/data_blob_dispositions.csv",
        "label,disposition,format,artifact,consumer_evidence,pointer_evidence,extent_evidence,reflow_status,notes",
        "record pass-time blob dispositions",
    ),
    Artifact(
        "inventory/deferrals.csv",
        "pass_id,corridor,subject,kind,deferral,revisit_condition,status",
        "create the canonical deferral ledger",
    ),
    Artifact(
        "inventory/proof_debt_acknowledged.csv",
        "signal,reason,pass_id",
        "create the canonical proof-debt acknowledgement ledger",
    ),
)


def validate(doc_root: Path, project: str) -> list[str]:
    errors: list[str] = []
    for artifact in ARTIFACTS:
        path = doc_root / artifact.relative_path
        if not path.is_file():
            errors.append(
                f"canonical project artifact missing: {path}; {artifact.remedy.replace('<project>', project)}"
            )
            continue
        if artifact.header is None:
            continue
        try:
            header = path.open(encoding="utf-8").readline().rstrip("\r\n")
        except OSError as exc:
            errors.append(f"cannot read canonical project artifact {path}: {exc}")
            continue
        if header != artifact.header:
            errors.append(
                f"invalid header in canonical project artifact {path}; "
                f"expected: {artifact.header}"
            )
    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project")
    parser.add_argument("doc_root", type=Path)
    args = parser.parse_args(argv)
    errors = validate(args.doc_root, args.project)
    for message in errors:
        print(f"project_artifact_manifest: {message}", file=sys.stderr)
    if errors:
        return 1
    print(f"OK: canonical project artifact set complete ({args.project})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
