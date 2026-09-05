"""Shared producer/consumer contract for terminal review-packet gate evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import shutil
from pathlib import Path

from process_friction import structural_lines


GATES = {
    "project-verify": "Project Verify Gate",
    "project-process-check": "Project Process Gate",
    "project-docs-check": "Project Docs Gate",
}
SUPPORTING = {
    "cache-preparation": "Cache Preparation",
    "next-pass": "Generated Next-Pass Evidence",
    "proof-debt": "Proof Debt Signals",
    "crosswalk": "Crosswalk Currency",
}
COMMANDS = {**GATES, **SUPPORTING}
TOOLS = {"make", "assembler", "python3", "bash", "git", "rg"}


class PacketError(ValueError):
    pass


def section(document, title, level):
    lines = document.splitlines(keepends=True)
    headings = []
    for index, line in structural_lines(document):
        match = re.fullmatch(r"(#{1,6})\s+(.+?)\s*\n?", line)
        if match:
            headings.append((index, len(match[1]), match[2]))
    matches = [(index, depth) for index, depth, name in headings if depth == level and name == title]
    if len(matches) != 1:
        raise PacketError(f"packet requires exactly one {title} section")
    start, _ = matches[0]
    end = next((index for index, depth, _ in headings if index > start and depth <= level), len(lines))
    return "".join(lines[start + 1:end])


def one_field(body, pattern, field):
    outside = "".join(line for _, line in structural_lines(body))
    matches = re.findall(pattern, outside, re.M)
    if len(matches) != 1:
        raise PacketError(f"packet must declare exactly one {field}")
    return matches[0]


def code_block(body, language):
    matches, content, fence, current_language = [], [], None, None
    for line in body.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line.rstrip("\r\n"))
        if fence is None:
            if marker:
                fence, current_language, content = marker[1], marker[2].strip(), []
        elif marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not marker[2].strip():
            if current_language == language:
                matches.append("".join(content).rstrip("\n"))
            fence = None
        else:
            content.append(line)
    if fence is not None:
        raise PacketError("packet contains an unterminated evidence block")
    if len(matches) != 1:
        raise PacketError(f"packet requires exactly one {language} evidence block")
    return matches[0]


def packet_head(document):
    return one_field(section(document, "Reviewed State", 2),
                     r"^-\s*Review head SHA:\s*`?([0-9a-fA-F]{40})`?\s*$", "Review head SHA").lower()


def evidence_json(value):
    def unique_fields(pairs):
        result = {}
        for key, item in pairs:
            if key in result:
                raise PacketError(f"duplicate JSON evidence field: {key}")
            result[key] = item
        return result
    return json.loads(value, object_pairs_hook=unique_fields)


def command_evidence(document, title):
    body = section(document, title, 3)
    state = one_field(body, r"^State:\s*`review_head ([0-9a-fA-F]{40})`\s*$", f"{title} state").lower()
    raw = one_field(body, r"^Exit status:\s*`([0-9]+|not-run)`\s*$", f"{title} Exit status")
    command = code_block(body, "sh")
    return body, {"review_head": state, "command": command,
                  "exit_status": None if raw == "not-run" else int(raw)}


def gate_evidence(document, name):
    body, record = command_evidence(document, COMMANDS[name])
    return body, {"name": name, **record}


def failure_summary(prerequisite, records, state_integrity):
    failures = list(prerequisite["failures"])
    if state_integrity != "pass":
        failures.append("review head or tracked worktree changed during packet generation")
    failures.extend(f"{row['name']} " + ("not run" if row["exit_status"] is None else f"exit {row['exit_status']}")
                    for row in records if row["exit_status"] != 0)
    return failures


def validate_environment(record):
    for group, required in (("tools", TOOLS), ("inputs", {"source", "reference"})):
        entries = record.get(group)
        if not isinstance(entries, dict) or set(entries) != required:
            raise PacketError(f"prerequisite evidence requires complete {group} metadata")
        for name, item in entries.items():
            if not isinstance(item, dict) or item.get("status") not in ("present", "missing", "missing_or_empty", "unreadable"):
                raise PacketError(f"invalid prerequisite metadata: {name}")
            if record["status"] == "pass" and item["status"] != "present":
                raise PacketError(f"prerequisite pass hides unavailable {name}")
            if group == "tools" and (not isinstance(item.get("requested"), str) or not item["requested"]):
                raise PacketError(f"prerequisite evidence requires requested tool: {name}")
            if item["status"] == "present":
                if (not isinstance(item.get("path"), str) or not Path(item["path"]).is_absolute()
                        or not isinstance(item.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", item["sha256"])):
                    raise PacketError(f"prerequisite evidence requires resolved path and hash: {name}")
                if group == "inputs" and (type(item.get("size")) is not int or item["size"] <= 0):
                    raise PacketError(f"prerequisite evidence requires nonempty input size: {name}")


def validate_packet(document, expected_head, expected_project=None):
    if packet_head(document) != expected_head.lower():
        raise PacketError("packet review head does not match state")
    try:
        summary = evidence_json(code_block(section(document, "Required Gate Summary", 2), "json"))
    except json.JSONDecodeError as exc:
        raise PacketError(f"invalid terminal gate summary: {exc}") from exc
    if not isinstance(summary, dict) or type(summary.get("schema_version")) is not int or summary["schema_version"] != 1:
        raise PacketError("invalid terminal gate summary schema")
    if summary.get("review_head") != expected_head.lower():
        raise PacketError("terminal gate summary does not match review head")
    project = summary.get("project")
    if not isinstance(project, str) or not re.fullmatch(r"[a-z0-9_-]+", project):
        raise PacketError("terminal gate summary requires project")
    declared = one_field(section(document, "Reviewed State", 2), r"^- Project:\s*`([a-z0-9_-]+)`\s*$", "Project")
    if project != declared or (expected_project is not None and project != expected_project):
        raise PacketError("packet project does not match reviewed state")
    gates, supporting = summary.get("gates"), summary.get("supporting_evidence")
    if not isinstance(gates, list) or len(gates) != len(GATES):
        raise PacketError("terminal gate summary must include every required gate")
    if not isinstance(supporting, list) or len(supporting) != len(SUPPORTING):
        raise PacketError("terminal summary must include required supporting evidence")
    records = gates + supporting
    executables = []
    seen, failures = set(), []
    for index, record in enumerate(records):
        domain = GATES if index < len(GATES) else SUPPORTING
        if (not isinstance(record, dict) or not isinstance(record.get("name"), str)
                or record["name"] not in domain or record["name"] in seen
                or set(record) != {"name", "review_head", "command", "exit_status"}):
            raise PacketError("unknown or duplicate terminal gate")
        name = record["name"]
        seen.add(name)
        _, actual = gate_evidence(document, name)
        if actual["review_head"] != expected_head.lower():
            raise PacketError(f"{COMMANDS[name]} does not match review head")
        if any(record.get(key) != value for key, value in actual.items()):
            raise PacketError(f"terminal summary disagrees with {COMMANDS[name]}")
        if record.get("exit_status") is not None and type(record["exit_status"]) is not int:
            raise PacketError(f"invalid {COMMANDS[name]} exit status")
        try:
            argv = shlex.split(actual["command"])
        except ValueError as exc:
            raise PacketError(f"invalid gate command: {exc}") from exc
        while argv and re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", argv[0]):
            argv.pop(0)
        if name in GATES and (len(argv) != 3 or argv[1:] != [name, f"PROJECT={project}"]):
            raise PacketError(f"{GATES[name]} does not run its canonical command")
        if name in GATES:
            executables.append((name, argv[0]))
        status = actual["exit_status"]
        if status != 0:
            failures.append(f"{COMMANDS[name]} " + ("was not run" if status is None else f"exit status is nonzero: {status}"))
    body, preflight = command_evidence(document, "Build and Fixture Prerequisites")
    try:
        environment_record = evidence_json(code_block(body, "text"))
    except json.JSONDecodeError as exc:
        raise PacketError(f"invalid prerequisite evidence: {exc}") from exc
    if (environment_record != summary.get("environment") or not isinstance(environment_record, dict)
            or not isinstance(environment_record.get("failures"), list)
            or any(not isinstance(item, str) for item in environment_record["failures"])
            or preflight["review_head"] != expected_head.lower()):
        raise PacketError("terminal prerequisite summary disagrees with evidence")
    prerequisite_status = "fail" if environment_record["failures"] else "pass"
    if environment_record.get("status") != prerequisite_status or preflight["exit_status"] != int(prerequisite_status == "fail"):
        raise PacketError("prerequisite status disagrees with observed failures")
    validate_environment(environment_record)
    make = environment_record["tools"]["make"]
    for name, executable in executables:
        if executable not in (make["requested"], make.get("path")):
            raise PacketError(f"{GATES[name]} command does not match recorded make tool")
    state_integrity = summary.get("state_integrity")
    if not isinstance(state_integrity, str) or state_integrity not in {"pass", "fail"}:
        raise PacketError("terminal summary requires state integrity result")
    if prerequisite_status != "pass":
        failures.extend(environment_record["failures"])
    if state_integrity != "pass":
        failures.append("review head or tracked worktree changed during packet generation")
    if summary.get("failures") != failure_summary(environment_record, records, state_integrity):
        raise PacketError("terminal failure categories disagree with observed results")
    expected_status = "fail" if failures else "pass"
    if summary.get("status") != expected_status:
        raise PacketError("terminal status disagrees with required evidence")
    if failures:
        raise PacketError("packet " + "; ".join(failures))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def environment(source, reference, make, assembler, expected_assembler=None, expected_reference=None):
    result = {"tools": {}, "inputs": {}, "failures": []}
    for name, executable in (("make", make), ("assembler", assembler), ("python3", "python3"),
                             ("bash", "bash"), ("git", "git"), ("rg", "rg")):
        resolved = shutil.which(executable)
        if resolved is None:
            result["tools"][name] = {"requested": executable, "status": "missing"}
            result["failures"].append(f"missing tool: {name} ({executable})")
        else:
            path = Path(resolved).resolve()
            try:
                result["tools"][name] = {"requested": executable, "path": str(path), "sha256": digest(path), "status": "present"}
            except OSError as exc:
                result["tools"][name] = {"requested": executable, "path": str(path), "status": "unreadable"}
                result["failures"].append(f"unreadable tool {name}: {exc}")
    for name, value in (("source", source), ("reference", reference)):
        path = Path(value).resolve()
        try:
            if not path.is_file() or path.stat().st_size == 0:
                result["inputs"][name] = {"path": str(path), "status": "missing_or_empty"}
                result["failures"].append(f"missing or empty {name} input: {path}")
            else:
                result["inputs"][name] = {"path": str(path), "sha256": digest(path), "size": path.stat().st_size, "status": "present"}
        except OSError as exc:
            result["inputs"][name] = {"path": str(path), "status": "unreadable"}
            result["failures"].append(f"unreadable {name} input: {exc}")
    for name, expected, actual in (
        ("assembler", expected_assembler, result["tools"]["assembler"].get("sha256")),
        ("reference", expected_reference, result["inputs"]["reference"].get("sha256")),
    ):
        if expected and (not re.fullmatch(r"[0-9a-fA-F]{64}", expected) or expected.lower() != actual):
            result["failures"].append(f"{name} SHA-256 mismatch against supplied expectation")
    result["status"] = "fail" if result["failures"] else "pass"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    preflight = commands.add_parser("environment")
    for name in ("source", "reference", "make", "assembler", "output"):
        preflight.add_argument("--" + name, required=True)
    preflight.add_argument("--expected-assembler")
    preflight.add_argument("--expected-reference")
    summary = commands.add_parser("summary")
    for name in ("head", "project", "environment", "state-integrity"):
        summary.add_argument("--" + name, required=True)
    for name in COMMANDS:
        summary.add_argument("--" + name + "-command", required=True)
        summary.add_argument("--" + name + "-exit", required=True)
    args = parser.parse_args()
    if args.action == "environment":
        result = environment(args.source, args.reference, args.make, args.assembler,
                             args.expected_assembler, args.expected_reference)
        payload = json.dumps(result, indent=2) + "\n"
        Path(args.output).write_text(payload)
        print(payload, end="")
        return int(result["status"] != "pass")
    prerequisite = json.loads(Path(args.environment).read_text())
    exits = lambda raw: None if raw == "not-run" else int(raw)
    records = [{"name": name, "review_head": args.head,
                "command": getattr(args, name.replace("-", "_") + "_command"),
                "exit_status": exits(getattr(args, name.replace("-", "_") + "_exit"))} for name in COMMANDS]
    failures = failure_summary(prerequisite, records, args.state_integrity)
    print(json.dumps({"schema_version": 1, "review_head": args.head, "project": args.project,
                      "environment": prerequisite, "state_integrity": args.state_integrity,
                      "gates": records[:len(GATES)], "supporting_evidence": records[len(GATES):],
                      "failures": failures, "status": "fail" if failures else "pass"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
