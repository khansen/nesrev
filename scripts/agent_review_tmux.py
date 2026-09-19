#!/usr/bin/env python3
"""Launch the standard implementer/reviewer tmux workspace."""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import agent_review as review


SCRIPT = Path(__file__).resolve()
ROLES = ("implementer", "reviewer")


def tmux(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [os.environ.get("AGENT_REVIEW_TMUX_BIN", "tmux"), *args],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=check,
    )


def agent_command(value: str) -> list[str]:
    args = shlex.split(value)
    binary = shutil.which(args[0]) if args else None
    if not binary:
        raise review.UserError(f"agent executable not found: {args[0] if args else '(empty command)'}")
    return [str(Path(binary).absolute()), *args[1:]]


def current_state(root: Path, project: str) -> dict | None:
    if not review.state_path(root).exists():
        return None
    state = review.read_state(root)
    if state.get("project") != project and state["status"] != "APPROVED":
        raise review.UserError(
            f"unfinished review for {state.get('project')}: {state['run_id']} "
            f"({state['status']}); finish that handoff before starting {project}"
        )
    return state if state.get("project") == project else None


def bootstrap(role: str, project: str, root: Path, task_path: Path) -> str:
    ownership = (
        "You own implementation, verification, commits, and review archives. "
        f"Read {task_path} for the objective and the pass/review loop, including when resuming an existing review."
        if role == "implementer" else
        "Review tracked project files read-only. Write only review artifacts and "
        "verdict state through the review handoff tools; do not implement fixes."
    )
    return (
        f"You are the {role} for NESrev project {project} in {root}.\n"
        f"{ownership}\n"
        "Read AGENTS.md and agent_playbook/TOOLING.md#agent-review-handoff. "
        "One implementer and one reviewer share this checkout and take turns; "
        "watchers deliver the handoffs. Never push the projects branch.\n"
        "This is setup only. Do not start a pass or act on existing review state yet. "
        "Reply READY and end your turn. Wait for the launcher's next prompt."
    )


def kickoff(project: str, task: str) -> str:
    worker = shlex.join([sys.executable, str(SCRIPT.with_name("agent_review.py"))])
    return (
        f"Begin or resume implementation for {project}.\n\nObjective: {task}\n\n"
        "Follow AGENTS.md and the mandatory playbooks. Stay on the current branch; "
        "never push the projects branch. Preserve unrelated work.\n"
        "For a new or not-yet-intaken project, follow agent_playbook/NEW_PROJECT.md "
        "before semantic passes. The launcher creates the scaffold when needed. "
        f"If the reference ROM is missing, stop and ask for projects/{project}/reference/{project}.nes; "
        "do not download ROMs or reference material. Complete intake and reference "
        "preparation as the two required commits, then submit both for pass-0 review "
        f"with `{worker} start-pass --project {project} --pass-id 0`. "
        "Await approval and archive it before the first semantic pass.\n"
        "For an existing project, resume any in-progress pass first, then resume its pass cycle using project-next-pass, "
        "the working notes, and an explicitly selected corridor.\n"
        "For each coherent pass, record the pre-pass base SHA, implement, verify, "
        "close out, and commit. Then run "
        f"`{worker} start-pass --project {project} --pass-id <id> --base <pre-pass-SHA>`. "
        "After successful handoff, end your turn and wait for the reviewer. "
        "Do not edit or start another pass while review owns the turn.\n"
        "On requested changes, address each finding, commit, and use reready with "
        "a response and --generate-packet. On approval, archive the review with "
        "its pass id, commit the archive and any friction entries, then continue "
        "toward the objective. If an approved review was already archived, verify "
        "that archive is committed before continuing. Stop on exhausted review "
        "rounds or a blocker requiring the user's input."
    )


def require_live_agents(config: dict) -> None:
    for role, pane in config["panes"].items():
        dead = tmux("display-message", "-p", "-t", pane, "#{pane_dead}").stdout.strip()
        if dead != "0":
            raise review.UserError(f"{role} exited in pane {pane}; restart the workspace after fixing its command")


def run_worker(config_path: Path, role: str) -> int:
    config = json.loads(config_path.read_text())
    os.environ["AGENT_REVIEW_TMUX_BIN"] = config["tmux_bin"]
    root = Path(config["root"])
    os.chdir(root)
    ready = config_path.with_name("ready")
    if role == "implementer":
        print(
            "Finish any login/trust prompts in the agents window.\n"
            "Wait until BOTH agents say READY and have returned to their prompts.\n"
            "Use Ctrl+b, w to choose a window; Ctrl+b, arrow to choose a pane.\n",
            flush=True,
        )
        input("Press Enter here to start the passes and automatic review handoffs: ")
        require_live_agents(config)
        state = current_state(root, config["project"])
        if state is None or state["status"] == "IMPLEMENTING":
            env = dict(os.environ, AGENT_REVIEW_TMUX_IMPLEMENTER=config["panes"]["implementer"])
            subprocess.run(
                [str(SCRIPT.with_name("agent_review_tmux_notify.sh")),
                 "implementer", "IMPLEMENTING", str(config_path.with_name("task.md"))],
                env=env, check=True,
            )
        ready.touch()
        tmux("select-window", "-t", config["agents_window"])
        tmux("select-pane", "-t", config["panes"]["implementer"])
    else:
        print("Waiting for startup confirmation in the other watcher pane.", flush=True)
        while not ready.exists():
            time.sleep(0.5)

    print(f"Watching {config['project']} handoffs for {role}.", flush=True)
    env = dict(os.environ)
    env[f"AGENT_REVIEW_TMUX_{role.upper()}"] = config["panes"][role]
    command = [
        sys.executable, str(SCRIPT.with_name("agent_review.py")), "watch",
        "--role", role, "--project", config["project"],
        "--worker-id", config_path.parent.name,
        "--notify", str(SCRIPT.with_name("agent_review_tmux_notify.sh")),
    ]
    os.execve(sys.executable, command, env)
    return 0


def connect(session_id: str, name: str, no_attach: bool) -> int:
    if no_attach:
        print(f"Attach: tmux attach -t {name}")
        print(f"Inside tmux: tmux switch-client -t {name}")
        return 0
    command = "switch-client" if os.environ.get("TMUX") else "attach-session"
    return subprocess.call([os.environ.get("AGENT_REVIEW_TMUX_BIN", "tmux"), command, "-t", session_id])


def ensure_project(root: Path, project: str) -> None:
    directory = root / "projects" / project
    config = directory / "project.conf"
    if config.is_file():
        return
    if directory.exists():
        raise review.UserError(f"existing project directory has no project.conf: {directory}")
    if not re.fullmatch(r"[a-z0-9_-]+", project):
        raise review.UserError("new project slugs must contain lowercase letters, digits, underscore, or dash")
    subprocess.run(["make", "project-doctor"], cwd=root, check=True)
    subprocess.run(["make", "project-init", f"PROJECT={project}"], cwd=root, check=True)
    if not config.is_file():
        raise review.UserError(f"project-init did not create {config}")
    print(f"Scaffold ready. Supply the reference ROM at {directory / 'reference' / (project + '.nes')}.")


def launch(args: argparse.Namespace) -> int:
    root = Path(review.run_git(["rev-parse", "--show-toplevel"], cwd=args.repo).strip()).resolve()
    if not review.PROJECT_RE.fullmatch(args.project):
        raise review.UserError("invalid project slug")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.session):
        raise review.UserError("session name may contain only letters, digits, underscore, and dash")
    tmux_bin = shutil.which(os.environ.get("AGENT_REVIEW_TMUX_BIN", "tmux"))
    if not tmux_bin:
        raise review.UserError("tmux executable not found")
    sessions = tmux(
        "list-sessions", "-F",
        "#{session_id}\t#{session_name}\t#{@nesrev_review_root}\t#{@nesrev_review_project}",
        check=False,
    )
    entries = [line.split("\t") for line in sessions.stdout.splitlines() if line]
    for session_id, name, checkout, project in entries:
        if checkout == str(root) and project == args.project:
            print(f"Reconnecting to {name} for {project}; continuing its existing agents and task.")
            return connect(session_id, name, args.no_attach)
    for session_id, name, checkout, project in entries:
        if name == args.session or checkout == str(root):
            raise review.UserError(
                f"tmux session {name} already exists; use tmux attach -t {name} "
                "(or tmux switch-client -t " + name + " inside tmux)"
            )

    commands = {role: agent_command(getattr(args, f"{role}_cmd")) for role in ROLES}
    current_state(root, args.project)
    ensure_project(root, args.project)
    review.ensure_runtime_excludes(root)
    logs = root / ".agents" / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix="tmux-", dir=logs))
    config_path = run / "workspace.json"
    (run / "task.md").write_text(kickoff(args.project, args.task))
    session_id = None
    try:
        created = tmux(
            "new-session", "-d", "-s", args.session, "-n", "agents", "-c", str(root),
            "-P", "-F", "#{session_id}\t#{window_id}\t#{pane_id}",
        ).stdout.strip()
        session_id, agents_window, implementer = created.split("\t")
        tmux("set-option", "-t", session_id, "@nesrev_review_root", str(root))
        tmux("set-option", "-t", session_id, "@nesrev_review_project", args.project)
        tmux("set-option", "-w", "-t", agents_window, "remain-on-exit", "on")
        tmux("set-option", "-w", "-t", agents_window, "pane-border-status", "top")
        tmux("set-option", "-w", "-t", agents_window, "pane-border-format", " #{pane_title} ")
        reviewer = tmux(
            "split-window", "-d", "-h", "-t", implementer, "-c", str(root), "-P", "-F", "#{pane_id}",
        ).stdout.strip()
        panes = {"implementer": implementer, "reviewer": reviewer}
        config_path.write_text(json.dumps({
            "root": str(root), "project": args.project, "panes": panes,
            "agents_window": agents_window, "tmux_bin": str(Path(tmux_bin).absolute()),
        }, indent=2) + "\n")
        for role, pane in panes.items():
            tmux("select-pane", "-t", pane, "-T", role)
            command = "exec " + shlex.join([
                *commands[role], bootstrap(role, args.project, root, run / "task.md"),
            ])
            tmux("respawn-pane", "-k", "-t", pane, "-c", str(root), command)

        def worker_command(role: str) -> str:
            return "exec " + shlex.join([
                sys.executable, str(SCRIPT), "--worker", str(config_path), role,
            ])

        watcher_window, first = tmux(
            "new-window", "-d", "-t", session_id, "-n", "watchers", "-c", str(root),
            "-P", "-F", "#{window_id}\t#{pane_id}", worker_command("implementer"),
        ).stdout.strip().split("\t")
        tmux("set-option", "-w", "-t", watcher_window, "remain-on-exit", "on")
        second = tmux(
            "split-window", "-d", "-v", "-t", first, "-c", str(root),
            "-P", "-F", "#{pane_id}", worker_command("reviewer"),
        ).stdout.strip()
        tmux("select-pane", "-t", first, "-T", "startup / implementer watcher")
        tmux("select-pane", "-t", second, "-T", "reviewer watcher")
        tmux("select-window", "-t", watcher_window)
        tmux("select-pane", "-t", first)
    except BaseException:
        if session_id:
            tmux("kill-session", "-t", session_id, check=False)
        raise

    print(f"Created {args.session} for {args.project} in {root}.")
    print("Check both agents, then press Enter in the watchers window to begin.")
    return connect(session_id, args.session, args.no_attach)


def main() -> int:
    if len(sys.argv) == 4 and sys.argv[1] == "--worker" and sys.argv[3] in ROLES:
        return run_worker(Path(sys.argv[2]), sys.argv[3])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="project checkout (default: current directory)")
    parser.add_argument("--session", default="nesrev-review", help="session name when creating a new workspace")
    parser.add_argument("--implementer-cmd", default="codex", help="executable and arguments; default: codex")
    parser.add_argument("--reviewer-cmd", default="claude", help="executable and arguments; default: claude")
    parser.add_argument("--task", default=(
        "Complete any unfinished intake, then continue coherent semantic passes until further progress requires runtime "
        "traces only the user can run. End with an executable trace plan."
    ), help="implementation objective")
    parser.add_argument("--no-attach", action="store_true", help="create the workspace without attaching or switching clients")
    return launch(parser.parse_args())


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (review.UserError, OSError, ValueError, EOFError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
    except subprocess.CalledProcessError as exc:
        print(f"error: {(exc.stderr or str(exc)).strip()}", file=sys.stderr)
        raise SystemExit(exc.returncode)
