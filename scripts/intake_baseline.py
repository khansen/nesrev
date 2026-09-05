"""Protect historical pass rows while publishing current successful intake measurements."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import tempfile
from pathlib import Path

from scorecard_metrics import measure
from process_friction import structural_lines


PENDING = "<!-- nesrev:intake-baseline pending -->"
REQUIRED = {"pass_id", "focus", "labels_remaining", "verify", "docs_check", "rework_items", "notes"}
OUTCOMES = {"verify": "pass (intake-relaxed)", "docs_check": "pass", "rework_items": "0",
            "raw_ptr_immediates_remaining": "not measured",
            "notes": "Intake baseline captured; semantic naming not started."}


def digest(value):
    return hashlib.sha256(value).hexdigest()


def scorecard(path):
    text = path.read_text(encoding="utf-8")
    header, rows = None, []
    for index, line in structural_lines(text):
        if not line.strip().startswith("|"):
            continue
        if not line.strip().endswith("|"):
            raise ValueError("incompatible scorecard row; missing closing delimiter")
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if cells[0] == "pass_id":
            if ((header is not None and header != cells) or len(set(cells)) != len(cells)
                    or not REQUIRED.issubset(cells)):
                raise ValueError("incompatible scorecard header")
            header = cells
        elif header is not None and not all(re.fullmatch(r":?-{3,}:?", cell) for cell in cells):
            if len(cells) != len(header) or (not cells[0].isdigit() and cells[0] != "retro-0"):
                raise ValueError("incompatible scorecard row; expected numeric pass ID and matching columns")
            rows.append((index, int(cells[0]) if cells[0].isdigit() else cells[0], dict(zip(header, cells))))
    numeric_ids = [pass_id for _, pass_id, _ in rows if isinstance(pass_id, int)]
    if (not header or not numeric_ids or any(left >= right for left, right in zip(numeric_ids, numeric_ids[1:]))
            or sum(pass_id == "retro-0" for _, pass_id, _ in rows) > 1):
        raise ValueError("scorecard requires unique increasing pass rows")
    return text, header, rows


def pending_count(text):
    return sum(line.strip() == PENDING for _, line in structural_lines(text))


def migration(path):
    value = json.loads(path.read_text(encoding="utf-8"))
    if (not isinstance(value, dict) or type(value.get("schema_version")) is not int or value["schema_version"] != 1
            or set(value) != {"schema_version", "disposition", "scorecard_sha256_at_migration", "historical_baseline"}
            or value.get("disposition") != "preserve-history-without-pass-zero"
            or not isinstance(value.get("scorecard_sha256_at_migration"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", value["scorecard_sha256_at_migration"])
            or value.get("historical_baseline") != "not recorded; not reconstructed"):
        raise ValueError("invalid legacy intake migration receipt")
    return value


def preflight(path, receipt):
    text, header, rows = scorecard(path)
    pending = pending_count(text)
    if pending:
        allowed = {"pass_id": "0", "focus": "Intake baseline", "warnings_baseline_delta": "0"}
        if pending != 1 or len(rows) != 1 or rows[0][1] != 0:
            raise ValueError("pending intake marker requires the sole scaffold pass-zero row")
        if any(value != allowed.get(key, "") for key, value in rows[0][2].items()):
            raise ValueError("pending intake row contains historical values; remove marker to preserve them, never overwrite")
        mode = "capture-scaffold"
    elif any(pass_id == 0 for _, pass_id, _ in rows):
        mode = "preserve-history"
    else:
        if not receipt.is_file():
            raise ValueError("legacy scorecard has no pass 0; run make project-intake-migrate PROJECT=<slug> before intake")
        migration(receipt)
        mode = "preserve-history"
    return {"mode": mode, "scorecard_sha256": digest(path.read_bytes())}


def atomic_bytes(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(value)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def migrate(path, receipt):
    text, _, rows = scorecard(path)
    if pending_count(text) or any(pass_id == 0 for _, pass_id, _ in rows):
        raise ValueError("legacy migration applies only to scorecards without pass zero; existing rows remain unchanged")
    if receipt.exists():
        migration(receipt)
        return False
    atomic_bytes(receipt, encoded({"schema_version": 1, "disposition": "preserve-history-without-pass-zero",
                                  "scorecard_sha256_at_migration": digest(path.read_bytes()),
                                  "historical_baseline": "not recorded; not reconstructed"}))
    return True


def publish(path, receipt, snapshot, expected, metrics, source, reference):
    actual = preflight(path, receipt)
    if actual != expected:
        raise ValueError("scorecard changed after intake preflight; rerun intake from the intended state")
    original = path.read_bytes()
    updated = original
    if actual["mode"] == "capture-scaffold":
        text, header, rows = scorecard(path)
        index, _, row = rows[0]
        row.update({key: value for key, value in {**metrics, **OUTCOMES}.items() if key in header})
        lines = text.splitlines(keepends=True)
        lines[index] = "| " + " | ".join(row[key] for key in header) + " |\n"
        updated = "".join(lines).replace(PENDING + "\n", "").encode()
    record = {"schema_version": 1, "kind": "current-intake-snapshot", "metrics": metrics,
              "source_sha256": digest(source.read_bytes()), "reference_sha256": digest(reference.read_bytes()),
              "gates": {"project-verify": {"exit_status": 0, "mode": "intake-relaxed"},
                        "project-process-check": {"exit_status": 0}, "project-docs-check": {"exit_status": 0}}}
    previous_snapshot = snapshot.read_bytes() if snapshot.exists() else None
    payload = encoded(record)
    if previous_snapshot != payload:
        atomic_bytes(snapshot, payload)
    try:
        if updated != original:
            atomic_bytes(path, updated)
    except OSError:
        if previous_snapshot is None:
            snapshot.unlink()
        elif previous_snapshot != payload:
            atomic_bytes(snapshot, previous_snapshot)
        raise
    return actual["mode"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preflight", "migrate", "publish"))
    parser.add_argument("--scorecard", required=True, type=Path)
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--snapshot", type=Path)
    parser.add_argument("--preflight")
    parser.add_argument("--source", type=Path)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--constant-kpi", type=Path)
    args = parser.parse_args()
    try:
        if args.action == "preflight":
            print(json.dumps(preflight(args.scorecard, args.receipt), sort_keys=True))
        elif args.action == "migrate":
            changed = migrate(args.scorecard, args.receipt)
            print("legacy intake migration recorded" if changed else "legacy intake migration already recorded")
        else:
            if any(value is None for value in (args.snapshot, args.preflight, args.source, args.reference, args.constant_kpi)):
                parser.error("publish requires snapshot, preflight, source, reference and constant-kpi")
            metrics = measure(args.source, args.constant_kpi, Path(__file__).parent)
            mode = publish(args.scorecard, args.receipt, args.snapshot, json.loads(args.preflight), metrics, args.source, args.reference)
            print(f"current intake snapshot published; history mode: {mode}")
    except (OSError, ValueError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()
