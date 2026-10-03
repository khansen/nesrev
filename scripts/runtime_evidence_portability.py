#!/usr/bin/env python3
"""Run affected active runtime-analyzer contracts from a committed clean export."""

from __future__ import annotations

import argparse
import contextlib
import csv
import io
import json
import os
import posixpath
import re
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path


class PortabilityError(ValueError):
    pass


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.PIPE)


def committed_manifest(root, revision, path):
    exists = subprocess.run(["git", "-C", str(root), "cat-file", "-e", f"{revision}:{path}"],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if exists.returncode:
        return None
    data = json.loads(git(root, "show", f"{revision}:{path}"))
    if not isinstance(data, dict) or not isinstance(data.get("questions"), list):
        raise PortabilityError(f"{revision}:{path}: invalid runtime manifest")
    return data


def trigger_paths(root, project, doc_root, base, head, manifests):
    project_path = f"projects/{project}"
    inputs = {f"{project_path}/project.conf"}
    inputs.update(f"{doc_root}/inventory/{name}" for name in
                  ("runtime_evidence.json", "deferrals.csv", "data_blob_dispositions.csv", "data_format_targets.csv"))
    for manifest in manifests:
        for question in (manifest or {}).get("questions", []):
            if not isinstance(question, dict):
                raise PortabilityError("runtime question must be an object")
            paths = [question.get(key) for key in ("analyzer", "runner", "trace_plan")]
            for case in question.get("checks", []):
                if not isinstance(case, dict) or not isinstance(case.get("fixtures"), list):
                    raise PortabilityError("runtime check requires fixtures")
                paths.extend(case["fixtures"])
            for path in paths:
                if not isinstance(path, str):
                    raise PortabilityError("runtime artifact must be a path")
                inputs.add(posixpath.normpath(f"{project_path}/{path.partition('#')[0]}"))
    prefixes = ("scripts/", "tests/", "tools/", "agent_playbook/templates/trace/",
                *(f"{project_path}/{name}/" for name in ("scripts", "tools", "tests")))
    dependencies = {"Makefile", "pyproject.toml", "requirements.txt", "requirements-dev.txt"}
    changed = {path.decode() for path in git(root, "log", "--format=", "--name-only", "-z", "--no-renames",
                                            f"{base}..{head}").split(b"\0") if path}
    return sorted(path for path in changed if path in inputs or path in dependencies or path.startswith(prefixes))


def export_commit(root, head, destination, archive_path):
    with archive_path.open("wb") as output:
        subprocess.run(["git", "-C", str(root), "archive", "--format=tar", head],
                       stdout=output, stderr=subprocess.PIPE, check=True)
    with tarfile.open(archive_path) as archive:
        for member in archive:
            target = destination / member.name
            if not target.resolve().is_relative_to(destination):
                raise PortabilityError(f"export path escapes clean tree: {member.name}")
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                with archive.extractfile(member) as source, target.open("wb") as output:
                    shutil.copyfileobj(source, output)
                target.chmod(member.mode & 0o777)
            elif member.issym():
                if not (target.parent / member.linkname).resolve().is_relative_to(destination):
                    raise PortabilityError(f"export symlink escapes clean tree: {member.name}")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(member.linkname)
            else:
                raise PortabilityError(f"unsupported export entry: {member.name}")


def evaluate(root, project, doc_root, base, head):
    root = Path(root).resolve()
    result = {"schema_version": 1, "project": project, "base": base, "review_head": head,
              "status": "fail", "reason": "validation_failed", "trigger_paths": [],
              "subjects": [], "case_ids": [], "cases": [], "errors": [],
              "captures": "unresolved"}
    try:
        if not re.fullmatch(r"[a-z0-9_-]+", project):
            raise PortabilityError("invalid project")
        base = git(root, "rev-parse", "--verify", base + "^{commit}").decode().strip()
        head = git(root, "rev-parse", "--verify", head + "^{commit}").decode().strip()
        result.update(base=base, review_head=head)
        if git(root, "rev-parse", "HEAD").decode().strip() != head:
            raise PortabilityError("review head must be checked out")
        if git(root, "status", "--porcelain", "--untracked-files=no"):
            raise PortabilityError("tracked working tree must be clean")
        docs = (root / doc_root).resolve()
        if not docs.is_relative_to(root / "projects" / project):
            raise PortabilityError("documentation root must belong to the reviewed project")
        relative_docs = docs.relative_to(root).as_posix()
        manifest_path = f"{relative_docs}/inventory/runtime_evidence.json"
        current = committed_manifest(root, head, manifest_path)
        previous = committed_manifest(root, base, manifest_path)
        from runtime_evidence_check import EvidenceError, run_case, validate_runtime_evidence
        rows = []
        blobs = docs / "inventory/data_blob_dispositions.csv"
        if blobs.exists():
            with blobs.open(newline="", encoding="utf-8") as source:
                rows = list(csv.DictReader(source))
        cases = []
        with contextlib.redirect_stdout(io.StringIO()):
            errors = validate_runtime_evidence(docs, rows, cases_out=cases)
        if errors:
            raise PortabilityError("; ".join(errors))
        if current is None and previous is None:
            result.update(status="not-required", reason="no_active_manifest")
            return result
        triggers = trigger_paths(root, project, relative_docs, base, head, (current, previous))
        result["trigger_paths"] = triggers
        if not triggers:
            result.update(status="not-required", reason="no_affected_inputs")
            return result
        if not cases:
            result.update(status="not-required", reason="no_active_questions")
            return result
        result.update(reason="affected_runtime_inputs", subjects=sorted({case[0] for case in cases}))
        for subject, case, analyzer, fixtures, command in cases:
            identity = f"{subject}/{case['name']}"
            result["case_ids"].append(identity)
            result["cases"].append({"id": identity, "subject": subject, "name": case["name"], "expect": case["expect"],
                                    "expected_exit": case["expected_exit"], "exit_status": None,
                                    "declared_command": command, "command": [],
                                    "diagnostics": case["diagnostics"], "matched_diagnostics": [],
                                    "status": "not-run"})
        with tempfile.TemporaryDirectory(prefix="runtime-portability-") as directory:
            scratch = Path(directory).resolve()
            exported = scratch / "repo"
            exported.mkdir()
            export_commit(root, head, exported, scratch / "head.tar")
            env = {name: os.environ[name] for name in ("PATH", "LANG", "LC_ALL", "LC_CTYPE", "TZ")
                   if name in os.environ}
            env.update(PYTHONNOUSERSITE="1", PYTHONDONTWRITEBYTECODE="1")
            for arguments, record in zip(cases, result["cases"]):
                subject, case, analyzer, fixtures, command = arguments
                try:
                    run_case(subject, case, exported / analyzer.relative_to(root),
                             [exported / path.relative_to(root) for path in fixtures], command,
                             env=env, record=record)
                    record["status"] = "pass"
                except (EvidenceError, OSError, UnicodeError) as exc:
                    record.update(status="fail", error=str(exc))
                    result["errors"].append(str(exc))
        result["status"] = "fail" if result["errors"] else "pass"
    except (PortabilityError, OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
        result["errors"].append(str(exc))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("project", "doc-root", "base", "head"):
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args()
    root = git(Path.cwd(), "rev-parse", "--show-toplevel").decode().strip()
    result = evaluate(root, args.project, args.doc_root, args.base, args.head)
    print(json.dumps(result, indent=2))
    return int(result["status"] == "fail")


if __name__ == "__main__":
    raise SystemExit(main())
