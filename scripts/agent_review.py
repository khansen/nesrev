#!/usr/bin/env python3
"""Local project-pass review handoff state machine.

The script deliberately avoids judging pass quality. It records whose turn it
is, points both agents at the packet/review artifacts, and optionally notifies a
manually started worker loop when state changes.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


VALID_STATUSES = {
    "IMPLEMENTING",
    "READY_FOR_REVIEW",
    "CHANGES_REQUESTED",
    "READY_FOR_REREVIEW",
    "APPROVED",
    "REVIEW_ROUNDS_EXHAUSTED",
}

REVIEW_READY_STATUSES = {"READY_FOR_REVIEW", "READY_FOR_REREVIEW"}
IMPLEMENTER_TURN_STATUSES = {
    "CHANGES_REQUESTED",
    "APPROVED",
    "REVIEW_ROUNDS_EXHAUSTED",
}

REJECTED_PREFIXES = (
    ".agents/",
    "agent_playbook/",
    "scripts/",
    "tests/",
)
REJECTED_EXACT = {"AGENTS.md", "Makefile"}
RUN_ID_RE = re.compile(r"^[A-Za-z0-9._-]+$")
PROJECT_RE = re.compile(r"^[A-Za-z0-9_-]+$")
PASS_ID_RE = re.compile(r"^[0-9]+$")
PACKET_REVIEW_HEAD_RE = re.compile(
    r"(?im)^-\s*Review head SHA:\s*`?([0-9a-f]{40})`?\s*$"
)
PACKET_VERIFY_GATE_RE = re.compile(
    r"(?ms)^### Project Verify Gate\b(?P<body>.*?)(?=^### |\Z)"
)
PACKET_EXIT_STATUS_RE = re.compile(r"(?m)^Exit status:\s*`?([0-9]+)`?\s*$")
RUNTIME_EXCLUDE_PATTERNS = (
    ".agents/current.json",
    ".agents/runs/",
    ".agents/logs/",
)


class UserError(Exception):
    pass


def repo_root() -> Path:
    return Path(run_git(["rev-parse", "--show-toplevel"]).strip())


def run_git(args: list[str], *, cwd: Path | None = None) -> str:
    try:
        return subprocess.check_output(
            ["git", *args],
            cwd=str(cwd) if cwd else None,
            stderr=subprocess.PIPE,
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        msg = exc.stderr.strip() or "git command failed"
        raise UserError(msg) from exc


def git_commit(ref: str, root: Path) -> str:
    return run_git(["rev-parse", "--verify", f"{ref}^{{commit}}"], cwd=root).strip()


def state_path(root: Path) -> Path:
    return root / ".agents" / "current.json"


def git_path(root: Path, path: str) -> Path:
    out = run_git(["rev-parse", "--git-path", path], cwd=root).strip()
    result = Path(out)
    if not result.is_absolute():
        result = root / result
    return result


def rel(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def resolve_path(root: Path, value: str) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = root / path
    return path


def ensure_repo_contained(root: Path, path: Path, label: str) -> Path:
    root_resolved = root.resolve()
    path_resolved = path.resolve()
    try:
        path_resolved.relative_to(root_resolved)
    except ValueError as exc:
        raise UserError(f"{label} must stay inside repository: {path}") from exc
    return path


def script_command(root: Path) -> str:
    script = Path(sys.argv[0])
    if script.is_absolute():
        script_arg = str(script)
    elif (root / script).exists():
        script_arg = script.as_posix()
    else:
        script_arg = str(script.resolve())
    return f"python3 {shlex.quote(script_arg)}"


def read_state(root: Path) -> dict[str, Any]:
    path = state_path(root)
    if not path.exists():
        raise UserError("agent review state is not initialized; run init first")
    data = json.loads(path.read_text())
    status = data.get("status")
    if status not in VALID_STATUSES:
        raise UserError(f"invalid status in current.json: {status!r}")
    run_id = data.get("run_id")
    if not isinstance(run_id, str) or not RUN_ID_RE.fullmatch(run_id):
        raise UserError(f"invalid run_id in current.json: {run_id!r}")
    project = data.get("project")
    if project is not None and (
        not isinstance(project, str) or not PROJECT_RE.fullmatch(project)
    ):
        raise UserError(f"invalid project in current.json: {project!r}")
    return data


def write_state(root: Path, state: dict[str, Any]) -> None:
    path = state_path(root)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def ensure_runtime_excludes(root: Path) -> None:
    exclude_path = git_path(root, "info/exclude")
    exclude_path.parent.mkdir(parents=True, exist_ok=True)
    existing = exclude_path.read_text() if exclude_path.exists() else ""
    missing = [
        pattern
        for pattern in RUNTIME_EXCLUDE_PATTERNS
        if pattern not in existing.splitlines()
    ]
    if not missing:
        return
    with exclude_path.open("a") as fh:
        if existing and not existing.endswith("\n"):
            fh.write("\n")
        fh.write("\n# Local agent-review handoff runtime state\n")
        for pattern in missing:
            fh.write(f"{pattern}\n")


def run_dir(root: Path, state: dict[str, Any]) -> Path:
    return root / ".agents" / "runs" / state["run_id"]


def project_review_archive_path(root: Path, state: dict[str, Any], pass_id: str) -> Path:
    project = state.get("project")
    if not project:
        raise UserError("archive requires a project in state")
    return (
        root
        / "projects"
        / project
        / "docs"
        / "reverse_engineering"
        / "reviews"
        / f"pass-{pass_id}.md"
    )


def reject_path(path: str) -> bool:
    if path in REJECTED_EXACT:
        return True
    if "/" not in path and path.endswith("_SPEC.md"):
        return True
    return any(path.startswith(prefix) for prefix in REJECTED_PREFIXES)


def changed_paths(root: Path, base_sha: str, head_sha: str) -> list[str]:
    out = run_git(["diff", "--name-only", f"{base_sha}..{head_sha}"], cwd=root)
    return [line for line in out.splitlines() if line]


def rejected_paths_for_range(root: Path, base_sha: str, head_sha: str) -> list[str]:
    return [path for path in changed_paths(root, base_sha, head_sha) if reject_path(path)]


def ensure_project_pass_range(root: Path, base_sha: str, head_sha: str) -> None:
    rejected = rejected_paths_for_range(root, base_sha, head_sha)
    if not rejected:
        return
    lines = [
        "range touches process/tooling paths; use process review or split the range",
        *[f"  - {path}" for path in rejected],
    ]
    raise UserError("\n".join(lines))


def ensure_clean_tracked(root: Path) -> None:
    unstaged = subprocess.run(["git", "diff", "--quiet"], cwd=root)
    staged = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=root)
    if unstaged.returncode != 0 or staged.returncode != 0:
        raise UserError("tracked working tree changes would make handoff stale")


def ensure_head(root: Path, head_sha: str) -> None:
    current = run_git(["rev-parse", "HEAD"], cwd=root).strip()
    if current != head_sha:
        raise UserError(
            "review head must be checked out before handoff\n"
            f"current HEAD: {current}\nreview HEAD:  {head_sha}"
        )


def require_file(root: Path, value: str, label: str) -> str:
    path = resolve_path(root, value)
    if not path.exists():
        raise UserError(f"{label} does not exist: {value}")
    return rel(root, path)


def validate_packet_head(root: Path, packet: str, expected_head: str) -> None:
    path = resolve_path(root, packet)
    text = path.read_text()
    match = PACKET_REVIEW_HEAD_RE.search(text)
    if not match:
        raise UserError(f"packet does not declare Review head SHA: {packet}")
    packet_head = match.group(1).lower()
    if packet_head != expected_head.lower():
        raise UserError(
            "packet review head does not match state\n"
            f"packet: {packet_head}\nstate:  {expected_head}"
        )


def validate_packet_verify_gate(root: Path, packet: str) -> None:
    path = resolve_path(root, packet)
    text = path.read_text()
    section = PACKET_VERIFY_GATE_RE.search(text)
    if not section:
        raise UserError(f"packet does not contain Project Verify Gate: {packet}")
    match = PACKET_EXIT_STATUS_RE.search(section.group("body"))
    if not match:
        raise UserError(f"packet Project Verify Gate does not declare Exit status: {packet}")
    status = int(match.group(1))
    if status != 0:
        raise UserError(f"packet Project Verify Gate exit status is nonzero: {status}")


def validate_packet(root: Path, packet: str, expected_head: str) -> None:
    validate_packet_head(root, packet, expected_head)
    validate_packet_verify_gate(root, packet)


def verdict_in_file(root: Path, review_file: str, verdict: str) -> None:
    text = resolve_path(root, review_file).read_text()
    verdict_re = re.compile(rf"(?im)^Verdict:\s*{re.escape(verdict)}\s*$")
    if not verdict_re.search(text):
        raise UserError(f"review file must contain 'Verdict: {verdict}'")


def prompt_path_for(root: Path, state: dict[str, Any], role: str, status: str) -> Path:
    safe_status = status.lower().replace("_", "-")
    name = f"{int(state['round']):02d}-{safe_status}-{role}.md"
    return run_dir(root, state) / "prompts" / name


def next_actor_for(state: dict[str, Any]) -> str | None:
    status = state["status"]
    if status in REVIEW_READY_STATUSES:
        return "reviewer"
    if status in IMPLEMENTER_TURN_STATUSES:
        return "implementer"
    return None


def render_prompt(root: Path, state: dict[str, Any], role: str) -> str:
    range_text = f"{state['review_base']}..{state['review_head']}"
    packet = state.get("packet") or "(packet missing)"
    run_id = state["run_id"]
    status = state["status"]
    command = script_command(root)
    if role == "reviewer":
        review_file = f".agents/runs/{run_id}/review-{int(state['round']):02d}.md"
        command_hint = (
            f"{command} approve --review {review_file}\n"
            f"{command} request-changes --review {review_file}"
        )
        body = [
            "# Agent Review Turn",
            "",
            f"Status: {status}",
            f"Run: {run_id}",
            f"Range: {range_text}",
            f"Packet: {packet}",
            f"Implementation note: {state.get('implementation_note') or '(none)'}",
            "",
            "Before reviewing, read `AGENTS.md` and follow the",
            "`Review a committed project pass` row in its Mandatory Routing Table.",
            "Load additional routed playbooks when the changed files or subsystem require them.",
            "",
            "Review the packet and repository read-only. Write the review artifact",
            f"at `{review_file}` with `Verdict: APPROVED` or",
            "`Verdict: CHANGES_REQUESTED`, then run one of:",
            "",
            "```sh",
            command_hint,
            "```",
            "",
        ]
    else:
        if status == "APPROVED":
            body = [
                "# Agent Review Approved",
                "",
                f"Run: {run_id}",
                f"Range: {range_text}",
                f"Review: {state.get('last_review')}",
                "",
                "The reviewed range is approved. A new pass may start.",
                "",
            ]
        elif status == "REVIEW_ROUNDS_EXHAUSTED":
            body = [
                "# Agent Review Rounds Exhausted",
                "",
                f"Run: {run_id}",
                f"Range: {range_text}",
                f"Round cap: {state.get('max_rounds')}",
                "",
                "Stop the unattended loop and request a human override.",
                "",
            ]
        else:
            response_file = f".agents/runs/{run_id}/response-{int(state['round']):02d}.md"
            body = [
                "# Agent Review Changes Requested",
                "",
                f"Run: {run_id}",
                f"Range: {range_text}",
                f"Review: {state.get('last_review')}",
                "",
                "Fix or dispute each finding. Commit implementation fixes, write",
                f"`{response_file}`, then run:",
                "",
                "```sh",
                f"{command} reready \\",
                f"  --response {response_file} \\",
                "  --head HEAD \\",
                "  --generate-packet",
                "```",
                "",
            ]
    return "\n".join(body)


def write_prompt(root: Path, state: dict[str, Any], role: str) -> str:
    path = prompt_path_for(root, state, role, state["status"])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_prompt(root, state, role))
    state.setdefault("prompts", {})[role] = rel(root, path)
    return state["prompts"][role]


def ensure_packet(root: Path, state: dict[str, Any], args: argparse.Namespace) -> None:
    if getattr(args, "packet", None):
        state["packet"] = require_file(root, args.packet, "packet")
        validate_packet(root, state["packet"], state["review_head"])
        return
    if not getattr(args, "generate_packet", False):
        packet = state.get("packet")
        if packet and resolve_path(root, packet).exists():
            return
        raise UserError("packet is missing; pass --packet or --generate-packet")

    project = state.get("project")
    if not project:
        raise UserError("--generate-packet requires a project in state")
    packet_path = run_dir(root, state) / f"packet-round-{int(state['round']):02d}.md"
    packet_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "make",
        "project-pass-review-packet",
        f"PROJECT={project}",
        f"BASE={state['review_base']}",
        f"HEAD={state['review_head']}",
        f"OUT={rel(root, packet_path)}",
    ]
    env = os.environ.copy()
    if state.get("allow_unresolved_lxxxx"):
        cmd.append("ALLOW_UNRESOLVED_LXXXX=1")
    result = subprocess.run(cmd, cwd=root, env=env, text=True)
    if result.returncode != 0:
        raise UserError(f"packet generation failed with exit {result.returncode}")
    state["packet"] = rel(root, packet_path)
    validate_packet(root, state["packet"], state["review_head"])


def command_init(args: argparse.Namespace) -> int:
    root = repo_root()
    if not RUN_ID_RE.fullmatch(args.run_id):
        raise UserError("run id may contain only letters, digits, dot, underscore, and dash")
    if not PROJECT_RE.fullmatch(args.project):
        raise UserError("project may contain only letters, digits, underscore, and dash")
    base_sha = git_commit(args.base, root)
    head_sha = git_commit(args.head, root)
    rejected = rejected_paths_for_range(root, base_sha, head_sha)
    if rejected and not args.allow_process_range:
        print("error: range touches process/tooling paths; use process review or split the range", file=sys.stderr)
        for path in rejected:
            print(f"  - {path}", file=sys.stderr)
        return 2

    ensure_runtime_excludes(root)
    branch = run_git(["rev-parse", "--abbrev-ref", "HEAD"], cwd=root).strip()
    run_path = root / ".agents" / "runs" / args.run_id
    (run_path / "prompts").mkdir(parents=True, exist_ok=True)
    (run_path / "workers").mkdir(parents=True, exist_ok=True)

    state = {
        "protocol_version": 1,
        "status": "IMPLEMENTING",
        "project": args.project,
        "branch": branch,
        "review_base": base_sha,
        "review_head": head_sha,
        "implementation_commit": head_sha,
        "round": 1,
        "max_rounds": args.max_rounds,
        "review_agent": args.reviewer,
        "implementation_agent": args.implementer,
        "run_id": args.run_id,
        "packet": None,
        "implementation_note": None,
        "last_review": None,
        "last_response": None,
        "prompts": {},
        "allow_unresolved_lxxxx": bool(args.allow_unresolved_lxxxx),
    }
    write_state(root, state)
    print(f"initialized {args.run_id} for {base_sha[:10]}..{head_sha[:10]}")
    return 0


def command_ready(args: argparse.Namespace) -> int:
    root = repo_root()
    state = read_state(root)
    if state["status"] != "IMPLEMENTING":
        raise UserError(f"ready requires IMPLEMENTING, got {state['status']}")
    ensure_clean_tracked(root)
    ensure_head(root, state["review_head"])
    state["implementation_note"] = require_file(root, args.note, "implementation note")
    ensure_packet(root, state, args)
    state["status"] = "READY_FOR_REVIEW"
    write_prompt(root, state, "reviewer")
    write_state(root, state)
    print(f"READY_FOR_REVIEW {state['run_id']} round {state['round']}")
    return 0


def command_request_changes(args: argparse.Namespace) -> int:
    root = repo_root()
    state = read_state(root)
    if state["status"] not in REVIEW_READY_STATUSES:
        raise UserError(f"request-changes requires review-ready state, got {state['status']}")
    review = require_file(root, args.review, "review file")
    verdict_in_file(root, review, "CHANGES_REQUESTED")
    state["last_review"] = review
    state["status"] = "CHANGES_REQUESTED"
    write_prompt(root, state, "implementer")
    write_state(root, state)
    print(f"CHANGES_REQUESTED {state['run_id']} round {state['round']}")
    return 0


def command_approve(args: argparse.Namespace) -> int:
    root = repo_root()
    state = read_state(root)
    if state["status"] not in REVIEW_READY_STATUSES:
        raise UserError(f"approve requires review-ready state, got {state['status']}")
    review = require_file(root, args.review, "review file")
    verdict_in_file(root, review, "APPROVED")
    state["last_review"] = review
    state["status"] = "APPROVED"
    write_prompt(root, state, "implementer")
    write_state(root, state)
    print(f"APPROVED {state['run_id']} round {state['round']}")
    return 0


def command_reready(args: argparse.Namespace) -> int:
    root = repo_root()
    state = read_state(root)
    if state["status"] != "CHANGES_REQUESTED":
        raise UserError(f"reready requires CHANGES_REQUESTED, got {state['status']}")
    ensure_clean_tracked(root)
    response = require_file(root, args.response, "response file")
    head_sha = git_commit(args.head, root)
    ensure_head(root, head_sha)
    ensure_project_pass_range(root, state["review_base"], head_sha)
    state["last_response"] = response
    next_round = int(state["round"]) + 1
    if next_round > int(state["max_rounds"]):
        state["round"] = next_round
        state["review_head"] = head_sha
        state["implementation_commit"] = head_sha
        state["status"] = "REVIEW_ROUNDS_EXHAUSTED"
        write_prompt(root, state, "implementer")
        write_state(root, state)
        print("review rounds exhausted", file=sys.stderr)
        return 1

    state["round"] = next_round
    state["review_head"] = head_sha
    state["implementation_commit"] = head_sha
    if not args.packet and not args.generate_packet:
        raise UserError("reready requires --packet or --generate-packet for the updated head")
    ensure_packet(root, state, args)
    state["status"] = "READY_FOR_REREVIEW"
    write_prompt(root, state, "reviewer")
    write_state(root, state)
    print(f"READY_FOR_REREVIEW {state['run_id']} round {state['round']}")
    return 0


def command_status(args: argparse.Namespace) -> int:
    root = repo_root()
    state = read_state(root)
    if args.json:
        print(json.dumps(state, indent=2, sort_keys=True))
    else:
        actor = next_actor_for(state) or "none"
        print(f"status: {state['status']}")
        print(f"run_id: {state['run_id']}")
        print(f"round: {state['round']} / {state['max_rounds']}")
        print(f"range: {state['review_base']}..{state['review_head']}")
        print(f"next_actor: {actor}")
        if actor in state.get("prompts", {}):
            print(f"prompt: {state['prompts'][actor]}")
    return 0


def notify_token(state: dict[str, Any], role: str) -> str:
    return "|".join(
        str(state.get(key) or "")
        for key in ("status", "round", "review_head", "last_review", "last_response")
    ) + f"|{role}"


def run_notify(root: Path, args: argparse.Namespace, state: dict[str, Any], role: str, prompt: str) -> None:
    if not args.notify:
        print(resolve_path(root, prompt).read_text())
        return
    env = os.environ.copy()
    env.update(
        {
            "AGENT_REVIEW_ROLE": role,
            "AGENT_REVIEW_STATUS": state["status"],
            "AGENT_REVIEW_RUN_ID": state["run_id"],
            "AGENT_REVIEW_PROMPT_FILE": str(resolve_path(root, prompt)),
        }
    )
    result = subprocess.run(
        [args.notify, role, state["status"], str(resolve_path(root, prompt))],
        cwd=root,
        env=env,
        text=True,
    )
    if result.returncode != 0:
        raise UserError(f"notify command failed with exit {result.returncode}")


def read_run_artifacts(root: Path, state: dict[str, Any], pattern: str) -> list[tuple[str, str]]:
    artifacts: list[tuple[str, str]] = []
    for path in sorted(run_dir(root, state).glob(pattern)):
        if path.is_file():
            artifacts.append((rel(root, path), path.read_text().rstrip()))
    return artifacts


def render_archive(state: dict[str, Any], pass_id: str) -> str:
    root = repo_root()
    reviews = read_run_artifacts(root, state, "review-*.md")
    responses = read_run_artifacts(root, state, "response-*.md")
    if not reviews:
        raise UserError("archive requires at least one review artifact")

    lines = [
        f"# Pass {pass_id} External Review",
        "",
        f"Project: `{state['project']}`",
        f"Run: `{state['run_id']}`",
        f"Final status: `{state['status']}`",
        f"Range: `{state['review_base']}..{state['review_head']}`",
        f"Rounds: `{state['round']} / {state['max_rounds']}`",
        "",
        "Packets, prompts, worker state, and notification markers are intentionally",
        "not archived here; regenerate packets from the recorded range when needed.",
        "",
        "## Review Artifacts",
        "",
    ]
    for source, text in reviews:
        lines.extend([f"### {Path(source).name}", "", f"Source: `{source}`", "", text, ""])

    lines.extend(["## Implementer Responses", ""])
    if responses:
        for source, text in responses:
            lines.extend([f"### {Path(source).name}", "", f"Source: `{source}`", "", text, ""])
    else:
        lines.extend(["_None._", ""])

    return "\n".join(lines).rstrip() + "\n"


def command_archive(args: argparse.Namespace) -> int:
    root = repo_root()
    state = read_state(root)
    if state["status"] != "APPROVED":
        raise UserError(f"archive requires APPROVED, got {state['status']}")
    if not PASS_ID_RE.fullmatch(args.pass_id):
        raise UserError("pass id must be numeric")
    ensure_clean_tracked(root)

    out_path = (
        ensure_repo_contained(root, resolve_path(root, args.out), "archive output")
        if args.out
        else ensure_repo_contained(
            root,
            project_review_archive_path(root, state, args.pass_id),
            "archive output",
        )
    )
    if out_path.exists() and not args.force:
        raise UserError(f"archive already exists: {rel(root, out_path)}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(render_archive(state, args.pass_id))
    print(f"archived review artifacts to {rel(root, out_path)}")
    return 0


def command_watch(args: argparse.Namespace) -> int:
    root = repo_root()
    deadline = time.time() + args.timeout if args.timeout is not None else None
    seen_path: Path | None = None
    while True:
        try:
            state = read_state(root)
        except UserError as exc:
            if str(exc) != "agent review state is not initialized; run init first" or args.once:
                raise
            if deadline is not None and time.time() >= deadline:
                print(f"timed out waiting for {args.role} turn", file=sys.stderr)
                return 4
            time.sleep(args.interval)
            continue
        actor = next_actor_for(state)
        if actor == args.role:
            prompt = state.get("prompts", {}).get(args.role)
            if not prompt:
                raise UserError(f"state says {args.role} owns the turn but no prompt is recorded")
            seen_path = run_dir(root, state) / "workers" / f"{args.role}.seen"
            token = notify_token(state, args.role)
            previous = seen_path.read_text().strip() if seen_path.exists() else ""
            if previous != token:
                run_notify(root, args, state, args.role, prompt)
                seen_path.parent.mkdir(parents=True, exist_ok=True)
                seen_path.write_text(token + "\n")
                if args.once:
                    return 0
                time.sleep(args.interval)
                continue
            if args.once:
                print(f"no new {args.role} turn")
                return 3
        elif args.once:
            print(f"not {args.role} turn; current actor is {actor or 'none'}")
            return 3

        if deadline is not None and time.time() >= deadline:
            print(f"timed out waiting for {args.role} turn", file=sys.stderr)
            return 4
        time.sleep(args.interval)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    init = sub.add_parser("init", help="create a review run")
    init.add_argument("--project", required=True)
    init.add_argument("--base", required=True)
    init.add_argument("--head", required=True)
    init.add_argument("--run-id", required=True)
    init.add_argument("--max-rounds", type=int, default=3)
    init.add_argument("--reviewer", default="reviewer")
    init.add_argument("--implementer", default="implementer")
    init.add_argument("--allow-process-range", action="store_true")
    init.add_argument("--allow-unresolved-lxxxx", action="store_true")
    init.set_defaults(func=command_init)

    ready = sub.add_parser("ready", help="mark committed pass ready for review")
    ready.add_argument("--note", required=True)
    ready.add_argument("--packet")
    ready.add_argument("--generate-packet", action="store_true")
    ready.set_defaults(func=command_ready)

    request = sub.add_parser("request-changes", help="record requested changes")
    request.add_argument("--review", required=True)
    request.set_defaults(func=command_request_changes)

    approve = sub.add_parser("approve", help="record approval")
    approve.add_argument("--review", required=True)
    approve.set_defaults(func=command_approve)

    archive = sub.add_parser("archive", help="archive durable review artifacts")
    archive.add_argument("--pass-id", required=True)
    archive.add_argument("--out")
    archive.add_argument("--force", action="store_true")
    archive.set_defaults(func=command_archive)

    reready = sub.add_parser("reready", help="mark fixes ready for rereview")
    reready.add_argument("--response", required=True)
    reready.add_argument("--head", required=True)
    reready.add_argument("--packet")
    reready.add_argument("--generate-packet", action="store_true")
    reready.set_defaults(func=command_reready)

    status = sub.add_parser("status", help="print current state")
    status.add_argument("--json", action="store_true")
    status.set_defaults(func=command_status)

    watch = sub.add_parser("watch", help="notify when a role owns the next turn")
    watch.add_argument("--role", choices=["implementer", "reviewer"], required=True)
    watch.add_argument("--notify")
    watch.add_argument("--once", action="store_true")
    watch.add_argument("--timeout", type=float, default=None)
    watch.add_argument("--interval", type=float, default=2.0)
    watch.set_defaults(func=command_watch)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except UserError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
