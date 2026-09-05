#!/usr/bin/env python3
"""Triage friction queues with durable, candidate-level import receipts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


DISPOSITIONS = {"accepted", "promoted", "project_local", "duplicate", "fixed", "superseded", "discarded"}
ROUTED = {"accepted", "promoted", "project_local", "duplicate"}
BLOCK_RE = re.compile(
    r"(?m)^<!-- agent-review-learning:(?P<key>[^\n<>]+):start -->\n"
    r"(?P<body>[\s\S]*?)^<!-- agent-review-learning:(?P=key):end -->\n?"
)
SOURCE_RE = re.compile(r"(?m)^#### [^\n]+\n\nSource: `(?P<source>[^`\n]+)`\n")
BOILERPLATE = (
    "Durable queue of process, harness, and tooling learning candidates.\n"
    "Entries are raw observations until triaged through process review.",
    "Raw candidates captured during agent-review handoffs. They are not "
    "playbook rules until triaged through process review.",
)


class FrictionError(ValueError):
    pass


def normalized(text: str) -> str:
    return "\n".join(line.rstrip() for line in text.splitlines()).strip()


def candidate_id(text: str) -> str:
    return hashlib.sha256(normalized(text).encode("utf-8")).hexdigest()


def empty_candidate(text: str) -> bool:
    values = []
    headings = []
    for line in text.splitlines():
        if re.match(r"^#{1,6}\s", line):
            headings.append(line)
            continue
        value = re.sub(r"^\s*(?:[-*+]|\d+[.)])\s+", "", line)
        value = value.strip().strip("_*`").strip().lower().rstrip(".")
        if value:
            values.append(value)
    if not values:
        return not headings
    return all(value in {"none", "n/a", "na", "no learning candidates", "nothing", "no actionable learning candidates"} for value in values)


def structural_lines(text: str):
    """Yield Markdown line indices and text outside fenced examples."""
    fence = None
    for index, line in enumerate(text.splitlines(keepends=True)):
        match = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line.rstrip("\r\n"))
        if fence is not None:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence) and not match[2].strip():
                fence = None
            continue
        if match:
            fence = match[1]
            continue
        yield index, line


def candidate_chunks(text: str) -> list[str]:
    lines = text.splitlines(keepends=True)
    boundaries = [0]
    for index, line in structural_lines(text):
        if re.match(r"^(?:#{1,6}|[-*+]|\d+[.)])\s+\S", line):
            if index:
                boundaries.append(index)
    boundaries.append(len(lines))
    return ["".join(lines[start:end]) for start, end in zip(boundaries, boundaries[1:])]


def untriaged_body(text: str, receipts: dict[str, dict]) -> str:
    if empty_candidate(text):
        return ""
    return "\n\n".join(
        chunk.strip() for chunk in candidate_chunks(text)
        if not empty_candidate(chunk) and candidate_id(chunk) not in receipts
    )


@dataclass(frozen=True)
class Part:
    prefix: str
    body: str
    source: str


def generated_parts(block: re.Match) -> tuple[str, list[Part]]:
    body = block["body"]
    line_offsets = []
    offset = 0
    for line in body.splitlines(keepends=True):
        line_offsets.append(offset)
        offset += len(line)
    structural_offsets = {line_offsets[index] for index, _ in structural_lines(body)}
    matches = [match for match in SOURCE_RE.finditer(body) if match.start() in structural_offsets]
    if not matches:
        raise FrictionError(f"unrecognized learning block {block['key']}; preserve it for manual review")
    parts = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(body)
        parts.append(Part(match[0], body[match.end():end], match["source"]))
    prefix = block[0][:block.start("body") - block.start()] + body[:matches[0].start()]
    return prefix, parts


def manual_prefix_and_body(text: str) -> tuple[str, str]:
    original = text
    text = text.lstrip()
    if text.splitlines()[:1] == ["# Process Friction"]:
        text = text.partition("\n")[2].lstrip()
    for prefix in (BOILERPLATE[0], "## Agent Review Learning Candidates", BOILERPLATE[1]):
        if text.startswith(prefix):
            text = text[len(prefix):].lstrip()
    return original[:len(original) - len(text)], text


def manual_body(text: str) -> str:
    return manual_prefix_and_body(text)[1]


def queue_sections(document: str):
    lines = document.splitlines(keepends=True)
    offsets = []
    offset = 0
    for line in lines:
        offsets.append(offset)
        offset += len(line)
    position = 0
    start = None
    key = None
    for index, line in structural_lines(document):
        if "<!-- agent-review-learning:" not in line:
            continue
        marker = re.fullmatch(r"<!-- agent-review-learning:([^\n<>]+):(start|end) -->\n?", line)
        if marker is None:
            raise FrictionError("unmatched learning marker; preserve the queue for manual review")
        if marker[2] == "start":
            if start is not None:
                raise FrictionError("nested learning marker; preserve the queue for manual review")
            start, key = offsets[index], marker[1]
        else:
            if start is None or marker[1] != key:
                raise FrictionError("unmatched learning marker; preserve the queue for manual review")
            end = offsets[index] + len(line)
            block = BLOCK_RE.fullmatch(document[start:end])
            if block is None:
                raise FrictionError("unrecognized learning block; preserve the queue for manual review")
            yield None, document[position:start]
            yield block, block[0]
            position = end
            start = None
    if start is not None:
        raise FrictionError("unmatched learning marker; preserve the queue for manual review")
    yield None, document[position:]


def queue_candidates(document: str, queue_source: str) -> dict[str, dict]:
    candidates = {}
    for block, text in queue_sections(document):
        if block is None:
            parts = [Part("", manual_body(text), queue_source)]
        else:
            _, parts = generated_parts(block)
        for part in parts:
            if empty_candidate(part.body):
                continue
            for chunk in candidate_chunks(part.body):
                if empty_candidate(chunk):
                    continue
                identity = candidate_id(chunk)
                item = candidates.setdefault(identity, {"id": identity, "content": normalized(chunk), "sources": []})
                if part.source not in item["sources"]:
                    item["sources"].append(part.source)
    return candidates


def project_paths(root: Path, project: str) -> tuple[Path, Path]:
    if not re.fullmatch(r"[A-Za-z0-9_-]+", project):
        raise FrictionError("invalid project slug")
    root = root.resolve()
    project_path = root / "projects" / project
    project_root = project_path.resolve()
    if project_root != project_path or not project_root.is_dir():
        raise FrictionError("project must be an existing directory within the repository")
    paths = (project_root / "PROCESS_FRICTION.md", project_root / "docs/reverse_engineering/inventory/process_friction_receipts.json")
    if any(not path.resolve().is_relative_to(project_root) for path in paths):
        raise FrictionError("queue and receipts must remain inside their project")
    return paths


def read_receipts(root: Path, project: str) -> dict[str, dict]:
    _, path = project_paths(root, project)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if (not isinstance(data, dict) or type(data.get("schema_version")) is not int
                or data["schema_version"] != 1 or data.get("project") != project):
            raise FrictionError("receipt schema/project mismatch")
        if not isinstance(data.get("receipts"), list):
            raise FrictionError("receipts must be a list")
        receipts = {}
        for entry in data["receipts"]:
            validate_receipt(entry)
            if entry["id"] in receipts:
                raise FrictionError("duplicate receipt id")
            receipts[entry["id"]] = entry
        return receipts
    except (OSError, UnicodeError, json.JSONDecodeError, FrictionError) as exc:
        raise FrictionError(f"cannot read receipts {path}: {exc}") from exc


def validate_receipt(entry: dict) -> None:
    if not isinstance(entry, dict):
        raise FrictionError("receipt must be an object")
    for name in ("id", "content", "disposition", "rationale"):
        if not isinstance(entry.get(name), str) or not entry[name].strip():
            raise FrictionError(f"receipt {name} must be nonempty text")
    if candidate_id(entry["content"]) != entry["id"]:
        raise FrictionError("receipt id does not match candidate content")
    if entry["disposition"] not in DISPOSITIONS:
        raise FrictionError("invalid receipt disposition")
    for name in ("sources", "destinations"):
        if not isinstance(entry.get(name), list) or any(not isinstance(value, str) or not value.strip() for value in entry[name]):
            raise FrictionError(f"receipt {name} must be a list of nonempty references")
    if not entry["sources"] or (entry["disposition"] in ROUTED and not entry["destinations"]):
        raise FrictionError("receipt requires source identity and a destination for routed work")


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.", delete=False) as output:
            temporary = Path(output.name)
            output.write(text)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def prune_document(document: str, receipts: dict[str, dict]) -> str:
    output = []
    for block, text in queue_sections(document):
        if block is None:
            prefix, body = manual_prefix_and_body(text)
            output.append(prefix + "".join(
                chunk for chunk in candidate_chunks(body)
                if empty_candidate(chunk) or candidate_id(chunk) not in receipts
            ))
            continue
        prefix, parts = generated_parts(block)
        retained = []
        for part in parts:
            body = untriaged_body(part.body, receipts)
            if body:
                retained.append(part.prefix + "\n" + body + "\n\n")
        if retained:
            output.append(prefix + "".join(retained) + f"<!-- agent-review-learning:{block['key']}:end -->\n")
    return "".join(output).strip() + "\n"


def prune(root: Path, project: str) -> int:
    queue, receipt_path = project_paths(root, project)
    receipts = read_receipts(root, project)
    if not queue.exists():
        return 0
    if not receipt_path.is_file():
        raise FrictionError("backfill durable receipts before pruning")
    original = queue.read_text(encoding="utf-8")
    before = queue_candidates(original, str(queue.relative_to(root)))
    updated = prune_document(original, receipts)
    after = queue_candidates(updated, str(queue.relative_to(root)))
    if queue.read_text(encoding="utf-8") != original:
        raise FrictionError("queue changed during pruning; retry without overwriting it")
    if not after:
        queue.unlink()
    elif updated != original:
        atomic_write(queue, updated)
    return len(before) - len(after)


def triage(root: Path, project: str, decisions: list[dict], prune_after: bool = False) -> int:
    queue, receipt_path = project_paths(root, project)
    original = queue.read_text(encoding="utf-8")
    candidates = queue_candidates(original, str(queue.relative_to(root)))
    receipts = read_receipts(root, project)
    if not isinstance(decisions, list) or not decisions:
        raise FrictionError("decisions must be a nonempty list")
    seen = set()
    for decision in decisions:
        if not isinstance(decision, dict) or not isinstance(decision.get("id"), str):
            raise FrictionError("each decision must identify a candidate id")
        identity = decision["id"]
        if identity not in candidates or identity in seen:
            raise FrictionError(f"unknown or repeated candidate id {identity}")
        seen.add(identity)
        entry = {**candidates[identity], **{name: decision.get(name) for name in ("disposition", "destinations", "rationale")}}
        validate_receipt(entry)
        for target in entry["destinations"]:
            if re.match(r"https?://\S+$", target):
                continue
            path = (root / target.split("#", 1)[0]).resolve()
            if not path.is_relative_to(root) or not path.is_file():
                raise FrictionError(f"destination does not resolve to a repository file: {target}")
        if identity in receipts:
            previous = receipts[identity]
            if any(previous[name] != entry[name] for name in ("content", "disposition", "destinations", "rationale")):
                raise FrictionError(f"receipt already exists with a different decision: {identity}")
            entry["sources"] = sorted(set(previous["sources"]) | set(entry["sources"]))
        receipts[identity] = entry
    if queue.read_text(encoding="utf-8") != original:
        raise FrictionError("queue changed during triage; retry without pruning")
    payload = {"schema_version": 1, "project": project, "receipts": [receipts[key] for key in sorted(receipts)]}
    atomic_write(receipt_path, json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
    if prune_after:
        return prune(root, project)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("list", "triage", "prune"))
    parser.add_argument("--project", required=True)
    parser.add_argument("--decisions", type=Path)
    parser.add_argument("--prune", action="store_true", dest="prune_after")
    args = parser.parse_args()
    if args.command != "triage" and (args.decisions is not None or args.prune_after):
        parser.error("--decisions and --prune are only valid with triage")
    try:
        root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()).resolve()
        queue, _ = project_paths(root, args.project)
        if args.command == "list":
            receipts = read_receipts(root, args.project)
            candidates = queue_candidates(queue.read_text(encoding="utf-8"), str(queue.relative_to(root))) if queue.exists() else {}
            print(json.dumps([{**item, "triaged": identity in receipts} for identity, item in candidates.items()], indent=2, ensure_ascii=False))
        elif args.command == "triage":
            if args.decisions is None:
                raise FrictionError("triage requires --decisions")
            removed = triage(root, args.project, json.loads(args.decisions.read_text(encoding="utf-8")), args.prune_after)
            print(f"receipts saved; removed {removed} triaged candidate(s)")
        else:
            print(f"removed {prune(root, args.project)} triaged candidate(s)")
        return 0
    except (FrictionError, OSError, UnicodeError, json.JSONDecodeError, subprocess.CalledProcessError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
