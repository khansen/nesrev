#!/usr/bin/env python3
"""Validate active runtime questions and exercise their analyzer fixtures.

This checks membership, tracked artifacts, and executable acceptance/refusal
contracts. It does not prove that a live capture resolves the stated question.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from data_format_targets_check import FIELDS as FAMILY_FIELDS, VALID_DISPOSITIONS as FAMILY_DISPOSITIONS

DEFERRAL_FIELDS = ["pass_id", "corridor", "subject", "kind", "deferral", "revisit_condition", "status"]


class EvidenceError(ValueError):
    pass


def text(value, field):
    if not isinstance(value, str) or not value.strip():
        raise EvidenceError(f"{field} must be nonempty text")
    return value.strip()


def strings(value, field, *, empty=False):
    if not isinstance(value, list) or (not value and not empty):
        raise EvidenceError(f"{field} must be a {'possibly empty' if empty else 'nonempty'} list")
    result = [text(item, field) for item in value]
    if len(set(result)) != len(result):
        raise EvidenceError(f"{field} contains duplicates")
    return result


def read_deferrals(doc_root):
    path = doc_root / "inventory/deferrals.csv"
    if not path.exists():
        return set()
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != DEFERRAL_FIELDS:
            raise EvidenceError("runtime reconciliation requires the canonical deferrals.csv header")
        subjects = set()
        for number, row in enumerate(reader, 2):
            if None in row or any(value is None for value in row.values()):
                raise EvidenceError(f"deferrals.csv:{number}: malformed row")
            if row["kind"].strip() not in {"static", "runtime"} or row["status"].strip() not in {"open", "closed"}:
                raise EvidenceError(f"deferrals.csv:{number}: invalid kind/status")
            if row["kind"].strip() == "runtime" and row["status"].strip() == "open":
                subjects.add(text(row["subject"], f"deferrals.csv:{number}: subject"))
        return subjects


def repository_and_project(doc_root):
    try:
        root = Path(subprocess.check_output(
            ["git", "-C", str(doc_root), "rev-parse", "--show-toplevel"],
            text=True, stderr=subprocess.PIPE,
        ).strip()).resolve()
    except subprocess.CalledProcessError as exc:
        raise EvidenceError("runtime evidence requires a Git worktree for tracked-artifact checks") from exc
    for parent in (doc_root, *doc_root.parents):
        if parent == root:
            break
        if (parent / "project.conf").is_file():
            return root, parent
    raise EvidenceError("DOC_ROOT must belong to a project with project.conf")


def read_runtime_families(doc_root):
    path = doc_root / "inventory/data_format_targets.csv"
    if not path.exists():
        return {}
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != FAMILY_FIELDS:
            raise EvidenceError("runtime reconciliation requires the canonical data_format_targets.csv header")
        result, seen = {}, set()
        for number, row in enumerate(reader, 2):
            if None in row or any(value is None for value in row.values()):
                raise EvidenceError(f"data_format_targets.csv:{number}: malformed row")
            family = text(row["family"], f"data_format_targets.csv:{number}: family")
            if family in seen or row["disposition"].strip() not in FAMILY_DISPOSITIONS:
                raise EvidenceError(f"data_format_targets.csv:{number}: duplicate family or invalid disposition")
            seen.add(family)
            if row["disposition"].strip() == "runtime_gated":
                result[family] = row
        return result


def tracked_file(root, project, value, field):
    raw = text(value, field)
    name, _, fragment = raw.partition("#")
    if not name or Path(name).is_absolute():
        raise EvidenceError(f"{field} must be a project-relative file")
    path = (project / name).resolve()
    if not path.is_relative_to(project) or not path.is_file():
        raise EvidenceError(f"{field} is missing or escapes the project: {raw}")
    tracked = subprocess.run(
        ["git", "--literal-pathspecs", "-C", str(root), "ls-files", "--error-unmatch", "--", str(path.relative_to(root))],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    if tracked.returncode:
        raise EvidenceError(f"{field} must be tracked: {raw}")
    if fragment:
        if path.suffix.lower() != ".md" or fragment not in markdown_anchors(path.read_text(encoding="utf-8")):
            raise EvidenceError(f"{field} has no matching Markdown anchor: {raw}")
    return path, fragment


def markdown_anchors(source):
    """Explicit HTML ids and plain ATX headings, excluding fenced examples."""
    anchors, counts, fence = set(), {}, None
    for line in source.splitlines():
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not marker[2].strip():
                fence = None
            continue
        if marker:
            fence = marker[1]
            continue
        anchors.update(re.findall(r'<a\s+id=[\"\']([^\"\']+)[\"\']', line))
        heading = re.match(r"^ {0,3}#{1,6}\s+(.+?)(?:\s+#+\s*)?$", line)
        if heading:
            slug = re.sub(r"[^\w\- ]", "", heading[1].lower()).replace(" ", "-")
            count = counts.get(slug, 0)
            anchors.add(f"{slug}-{count}" if count else slug)
            counts[slug] = count + 1
    return anchors


def run_case(question, case, analyzer, fixtures, command):
    with tempfile.TemporaryDirectory(prefix="runtime-evidence-check-") as directory:
        scratch = Path(directory)
        args = []
        for token in command:
            if token == "{fixtures}":
                args.extend(str(path) for path in fixtures)
            else:
                args.append(token.replace("{analyzer}", str(analyzer)).replace("{output}", str(scratch / "summary.out")))
        try:
            result = subprocess.run(args, cwd=scratch, capture_output=True, text=True, timeout=30)
        except (OSError, UnicodeError, subprocess.TimeoutExpired) as exc:
            raise EvidenceError(f"{question}/{case['name']}: analyzer could not complete: {exc}") from exc
        expected = case["expected_exit"]
        if result.returncode != expected:
            raise EvidenceError(f"{question}/{case['name']}: expected exit {expected}, got {result.returncode}; {result.stderr.strip()[:300]}")
        output = result.stdout + "\n" + result.stderr
        summary = scratch / "summary.out"
        if summary.is_file():
            output += "\n" + summary.read_text(encoding="utf-8")
        for expected_text in case["diagnostics"]:
            if expected_text not in output:
                raise EvidenceError(f"{question}/{case['name']}: missing diagnostic {expected_text!r}")
        return f"{question}/{case['name']}: {case['expect']} exit={result.returncode}"


def links_plan(row, doc_root, plan, plan_fragment):
    for artifact in text(row.get("artifact"), "runtime artifact").split(";"):
        name, _, fragment = artifact.strip().partition("#")
        if not name or (doc_root / name).resolve() != plan:
            continue
        if fragment and fragment not in markdown_anchors(plan.read_text(encoding="utf-8")):
            continue
        if not fragment or not plan_fragment or fragment == plan_fragment:
            return True
    return False


def validate_runtime_evidence(doc_root, rows, mode="process"):
    doc_root = Path(doc_root).resolve()
    manifest = doc_root / "inventory/runtime_evidence.json"
    try:
        runtime_rows = {}
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get("disposition"), str):
                raise EvidenceError("malformed blob disposition row")
            if row["disposition"].strip() == "runtime_gated":
                runtime_rows[text(row.get("label"), "runtime blob label")] = row
        subjects = read_deferrals(doc_root)
        families = read_runtime_families(doc_root)
        if not manifest.exists():
            if runtime_rows or subjects or families:
                raise EvidenceError("runtime_gated inventories and open runtime deferrals require inventory/runtime_evidence.json")
            return []
        data = json.loads(manifest.read_text(encoding="utf-8"))
        if not isinstance(data, dict) or type(data.get("schema_version")) is not int or data["schema_version"] != 1:
            raise EvidenceError("invalid runtime evidence schema_version")
        questions = data.get("questions")
        if not isinstance(questions, list):
            raise EvidenceError("runtime evidence questions must be a list")
        if not questions and not subjects and not runtime_rows and not families:
            return []
        root, project = repository_and_project(doc_root)
        tracked_file(root, project, str(manifest.relative_to(project)), "runtime manifest")
        seen, covered, covered_families = set(), set(), set()
        cases = []
        for question in questions:
            if not isinstance(question, dict):
                raise EvidenceError("each runtime question must be an object")
            subject = text(question.get("subject"), "subject")
            if subject in seen:
                raise EvidenceError(f"duplicate runtime subject: {subject}")
            seen.add(subject)
            question_text = text(question.get("question"), f"{subject}: question")
            if subject not in subjects:
                raise EvidenceError(f"{subject}: no matching open runtime deferral")
            plan, plan_fragment = tracked_file(root, project, question.get("trace_plan"), f"{subject}: trace_plan")
            if " ".join(question_text.split()) not in " ".join(plan.read_text(encoding="utf-8").split()):
                raise EvidenceError(f"{subject}: trace_plan does not state the manifest's question")
            tracked_file(root, project, question.get("runner"), f"{subject}: runner")
            analyzer, _ = tracked_file(root, project, question.get("analyzer"), f"{subject}: analyzer")
            signals = set(strings(question.get("required_signals"), f"{subject}: required_signals"))
            blobs = strings(question.get("blobs"), f"{subject}: blobs", empty=True)
            for label in blobs:
                if label not in runtime_rows:
                    raise EvidenceError(f"{subject}: blob {label} is not a runtime_gated row")
                if not links_plan(runtime_rows[label], doc_root, plan, plan_fragment):
                    raise EvidenceError(f"{subject}: blob {label} must link its trace_plan artifact")
                covered.add(label)
            for family in strings(question.get("families"), f"{subject}: families", empty=True):
                if family not in families:
                    raise EvidenceError(f"{subject}: family {family} is not a runtime_gated row")
                if not links_plan(families[family], doc_root, plan, plan_fragment):
                    raise EvidenceError(f"{subject}: family {family} must link its trace_plan artifact")
                covered_families.add(family)
            command = question.get("analyzer_command")
            if not isinstance(command, list) or not command or any(not isinstance(arg, str) or not arg for arg in command):
                raise EvidenceError(f"{subject}: analyzer_command must be an argument list")
            if not (command[0] == "{analyzer}" or (len(command) > 1 and command[:2] in
                    (["python3", "{analyzer}"], ["bash", "{analyzer}"], ["sh", "{analyzer}"]))):
                raise EvidenceError(f"{subject}: command must execute the tracked analyzer directly")
            if "{fixtures}" not in command or not any("{output}" in arg for arg in command):
                raise EvidenceError(f"{subject}: command requires {{fixtures}} and an isolated {{output}}")
            if any(re.search(r"[{}]", arg.replace("{fixtures}", "").replace("{output}", "").replace("{analyzer}", "")) for arg in command):
                raise EvidenceError(f"{subject}: unknown command placeholder")
            checks = question.get("checks")
            if not isinstance(checks, list) or not checks:
                raise EvidenceError(f"{subject}: checks must include acceptance and refusal fixtures")
            names, kinds, refused_signals = set(), set(), set()
            for check in checks:
                if not isinstance(check, dict):
                    raise EvidenceError(f"{subject}: check must be an object")
                name = text(check.get("name"), f"{subject}: check name")
                if name in names:
                    raise EvidenceError(f"{subject}: duplicate check name {name}")
                names.add(name)
                expect = check.get("expect")
                expected_exit = check.get("expected_exit")
                if expect not in {"accept", "refuse"} or type(expected_exit) is not int:
                    raise EvidenceError(f"{subject}/{name}: invalid expectation/exit")
                if (expect == "accept" and expected_exit != 0) or (expect == "refuse" and not 1 <= expected_exit <= 125):
                    raise EvidenceError(f"{subject}/{name}: acceptance requires exit0; refusal requires exit1..125")
                kinds.add(expect)
                missing = set(strings(check.get("missing_signals"), f"{subject}/{name}: missing_signals", empty=True))
                if (expect == "accept" and missing) or (expect == "refuse" and (not missing or not missing <= signals)):
                    raise EvidenceError(f"{subject}/{name}: invalid missing-signal coverage")
                if len(missing) == 1:
                    refused_signals.update(missing)
                strings(check.get("diagnostics"), f"{subject}/{name}: diagnostics")
                paths = [tracked_file(root, project, value, f"{subject}/{name}: fixture")[0]
                         for value in strings(check.get("fixtures"), f"{subject}/{name}: fixtures")]
                cases.append((subject, check, analyzer, paths, command))
            if kinds != {"accept", "refuse"} or refused_signals != signals:
                raise EvidenceError(f"{subject}: acceptance and missing-signal refusal coverage must cover every required signal")
        if seen != subjects:
            raise EvidenceError(f"open runtime deferrals missing questions: {', '.join(sorted(subjects - seen))}")
        if covered != set(runtime_rows):
            raise EvidenceError(f"runtime_gated blobs missing questions: {', '.join(sorted(set(runtime_rows) - covered))}")
        if covered_families != set(families):
            raise EvidenceError(f"runtime_gated families missing questions: {', '.join(sorted(set(families) - covered_families))}")
        if mode == "maturity":
            for arguments in cases:
                print("runtime_evidence_check:", run_case(*arguments))
        print(f"runtime_evidence_check: questions={len(seen)} runtime_blobs={len(covered)} "
              f"runtime_families={len(covered_families)} "
              f"fixtures={'executed' if mode == 'maturity' else 'not-run (process structure only)'} cases={len(cases)}; captures remain unresolved")
        return []
    except (EvidenceError, OSError, UnicodeError, json.JSONDecodeError, csv.Error) as exc:
        return [str(exc)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--doc-root", type=Path, required=True)
    parser.add_argument("--blobs", type=Path, required=True)
    parser.add_argument("--mode", choices=("process", "maturity"), default="maturity")
    args = parser.parse_args()
    try:
        with args.blobs.open(encoding="utf-8", newline="") as handle:
            rows = list(csv.DictReader(handle))
        errors = validate_runtime_evidence(args.doc_root, rows, args.mode)
    except (OSError, UnicodeError, csv.Error) as exc:
        errors = [str(exc)]
    for message in errors:
        print("runtime_evidence_check:", message, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
