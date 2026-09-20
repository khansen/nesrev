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
from reference_tools import project_reference_files, reference_files, reference_tool_issues


SCRIPT = Path(__file__).resolve()
ROLES = ("implementer", "reviewer")
MANUAL_WAIVER = "continue without a manual"
MANUAL_WARNING = (
    "Without a manual, the final disassembly's terminology and semantic precision "
    "will likely be lower than they could have been."
)


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


def role_command(args: argparse.Namespace, role: str) -> list[str]:
    value = getattr(args, f"{role}_cmd")
    if role == "reviewer" and value is None:
        value = "claude" if shutil.which("claude") else "codex"
        if value == "codex":
            print("Claude is not installed; using a separate Codex session as reviewer.")
    command = agent_command(value)
    model = getattr(args, f"{role}_model", None)
    effort = getattr(args, f"{role}_effort", None)
    if model is None and effort is None:
        return command

    # Use the invoked name; installed CLIs may resolve to versioned binaries.
    agent = Path(shlex.split(value)[0]).name
    if agent not in {"codex", "claude"}:
        raise review.UserError(
            f"--{role}-model/--{role}-effort require a codex or claude executable; "
            f"for a custom wrapper, put its native options in --{role}-cmd"
        )
    if "--" in command[1:]:
        raise review.UserError(f"remove the -- argument terminator from --{role}-cmd when using model/effort options")
    for setting, selected in (("model", model), ("effort", effort)):
        if selected is None:
            continue
        if not selected.strip() or selected.startswith("-"):
            raise review.UserError(f"--{role}-{setting} requires a nonempty value, not an option")
        native = [f"--{setting}"]
        if agent == "codex" and setting == "model":
            native.append("-m")
        key = "model" if setting == "model" else "model_reasoning_effort"
        if any(
            token == flag or token.startswith(flag + "=")
            or (flag == "-m" and token.startswith("-m"))
            for token in command[1:] for flag in native
        ) or (agent == "codex" and any(
            re.match(rf'(?:--config=|-c)?"?{key}"?\s*=', token)
            for token in command[1:]
        )):
            raise review.UserError(f"set {role} {setting} either in --{role}-{setting} or --{role}-cmd, not both")
    if model is not None:
        command.extend(["--model", model])
    if effort is not None:
        if agent == "codex":
            command.extend(["--config", "model_reasoning_effort=" + json.dumps(effort)])
        else:
            command.extend(["--effort", effort])
    return command


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
        "verdict state through the review handoff tools; do not implement fixes. "
        "Intake approval requires processing supplied references or documenting the user's explicit "
        "manual waiver; an empty folder alone does not justify skipping references. "
        "For runtime gaps, review agent capture attempts, scenario validation, and any human review batch "
        "against agent_playbook/RUNTIME_EVIDENCE.md; a pending capture is not a completed semantic result."
    )
    return (
        f"You are the {role} for NESrev project {project} in {root}.\n"
        f"{ownership}\n"
        "Read AGENTS.md and agent_playbook/TOOLING.md#agent-review-handoff. "
        "One implementer and one reviewer share this checkout and take turns; "
        "watchers deliver the handoffs. Never push the projects branch.\n"
        f"Before acting on a handoff, read .agents/reference_intake/{project}.json for the user's "
        "reference choice. The launcher records it at startup after your READY reply. "
        "Only a manual_decision of waived authorizes proceeding without a manual.\n"
        "This is setup only. Do not start a pass or act on existing review state yet. "
        "Reply READY and end your turn. Wait for the launcher's next prompt."
    )


def kickoff(project: str, task: str) -> str:
    worker = shlex.join([sys.executable, str(SCRIPT.with_name("agent_review.py"))])
    return (
        f"Begin or resume implementation for {project}.\n\nObjective: {task}\n\n"
        "Follow AGENTS.md and the mandatory playbooks. Stay on the current branch; "
        "never push the projects branch. Preserve unrelated work.\n"
        f"Before semantic analysis, read the user-supplied manual in projects/{project}/docs/game_reference/manuals/ "
        f"and any optional FAQs in projects/{project}/docs/game_reference/faqs/. "
        "Extract vocabulary into MANUAL_TERMS.md and seed TERMINOLOGY_CROSSWALK.md before naming. "
        f"The user's startup decision is in .agents/reference_intake/{project}.json. "
        "If manual_decision is waived, record that explicit user request and its semantic-quality "
        "limitation in the crosswalk, and still process any supplied FAQs. Otherwise, "
        "if the manual is absent or unreadable, stop with NEEDS INPUT and ask the user for it; "
        "never infer that an empty directory means the user declined to supply references. "
        "Repair any earlier no-reference preparation before continuing, even if intake was already approved.\n"
        "For a new or not-yet-intaken project, follow agent_playbook/NEW_PROJECT.md "
        "before semantic passes. The launcher creates the scaffold when needed. "
        f"If the reference ROM is missing, stop and ask for projects/{project}/reference/{project}.nes; "
        "do not download ROMs, manuals, or FAQs. TASVideos input movies are allowed under "
        "the runtime workflow below. Complete intake and reference "
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
        "rounds or a blocker requiring the user's input.\n"
        "When the objective is gold standard, use the complete checklist in "
        "agent_playbook/QUALITY_REVIEW.md#gold-standard-assessment and its linked "
        "project-wide audits. Green KPI gates alone are not completion. Submit "
        "the final closeout pass with the same start-pass command plus --gold. "
        "This requests a whole-project reviewer assessment and strict CI. "
        "After final approval, archive and commit the review, then stop with "
        "GOLD STANDARD APPROVED, the archive path, and the reviewed head.\n"
        "Runtime analysis is implementer-owned. Read agent_playbook/RUNTIME_EVIDENCE.md#agent-capture "
        "and attempt bounded emulator captures yourself before asking the user to play or trace. "
        "Reuse or adapt Lua input drivers, frame polling, movie replay, and screenshots; inspect "
        "visible objects against the supplied references and trace their owning slots. You may "
        "download TASVideos .fm2 input movies, keeping them untracked; validate ROM/revision, "
        "timing, replay synchronization, and scenario milestones before using the result. "
        "FCEUX is optional; missing it does not block intake or static work. Try available "
        "capture tooling and explain any actual installation, display, or permission blocker.\n"
        "Batch independent questions that truly need human judgment (for example ambiguous audio) "
        "using agent_playbook/RUNTIME_EVIDENCE.md#human-review-batch. Prepare short clips or "
        "screenshots, exact replay commands, stable question IDs, and a simple answer format; "
        "continue useful independent work while collecting the batch. Do not stop at each runtime gap. "
        "Do not delay a blocking permission or missing artifact just to fill a batch.\n"
        "When progress requires the user, stop with NEEDS INPUT, give the specific missing file, "
        "permission, or answer and exact next action. For human runtime review, link the prepared "
        "batch and executable trace plans, including what you tried and why it needs a human. "
        "Do not call unresolved evidence gold or done. "
        "When the user supplies it, resume this objective and the review cycle."
    )


def require_live_agents(config: dict) -> None:
    for role, pane in config["panes"].items():
        dead = tmux("display-message", "-p", "-t", pane, "#{pane_dead}").stdout.strip()
        if dead != "0":
            raise review.UserError(f"{role} exited in pane {pane}; restart the workspace after fixing its command")


def confirm_references(root: Path, project: str) -> None:
    references = root / "projects" / project / "docs" / "game_reference"
    record = root / ".agents" / "reference_intake" / f"{project}.json"
    previous = json.loads(record.read_text()) if record.exists() else {}
    if record.exists() and (
        not isinstance(previous, dict) or previous.get("project") != project
        or previous.get("manual_decision") not in {"provided", "waived"}
    ):
        raise review.UserError(f"invalid reference intake record: {record}")
    waived = previous.get("manual_decision") == "waived"
    print(
        "Before work starts, choose the references you want the agents to use.\n"
        f"Manual (PDF, scans, or text): {references / 'manuals'}\n"
        f"Optional FAQs/guides: {references / 'faqs'}\n"
        "Keep these source files in those ignored folders; the agents do not obtain them for you.\n",
        flush=True,
    )
    if waived:
        print("Your earlier explicit choice to continue without a manual is recorded; Enter keeps that choice.", flush=True)
    while True:
        if not reference_files(references / "manuals"):
            print(f"WARNING: {MANUAL_WARNING}", flush=True)
        answer = input(
            "When BOTH agents say READY and your reference set is ready, press Enter; "
            f"if you cannot supply a manual, type '{MANUAL_WAIVER}': "
        ).strip().lower()
        if answer not in {"", MANUAL_WAIVER}:
            print("Unrecognized choice. Press Enter to check the files or type the full skip phrase.", flush=True)
            continue
        manuals = reference_files(references / "manuals")
        if not manuals and not (waived or answer == MANUAL_WAIVER):
            print(
                f"NEEDS INPUT: add the manual to {references / 'manuals'}, then press Enter again.\n"
                f"Or explicitly choose '{MANUAL_WAIVER}'. FAQs are optional. Work has not started.", flush=True,
            )
            continue
        faqs = reference_files(references / "faqs")
        decision = "provided" if manuals else "waived"
        review.atomic_write(record, json.dumps({
            "project": project,
            "manual_decision": decision,
            "manual_files": [str(path.relative_to(root)) for path in manuals],
            "faq_files": [str(path.relative_to(root)) for path in faqs],
            "warning": MANUAL_WARNING if decision == "waived" else None,
        }, indent=2) + "\n")
        waived = decision == "waived"
        issues = reference_tool_issues(manuals + faqs)
        if issues:
            print("NEEDS INPUT: reference extraction tools are not ready:\n" + "\n".join(issues), flush=True)
            print("Install or repair the listed tools, then press Enter again. Work has not started.", flush=True)
            continue
        print(f"Manual: {decision}; optional FAQs/guides: {len(faqs)} file(s).", flush=True)
        return


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
        confirm_references(root, config["project"])
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
        startup_pane = config.get("startup_pane")
        if not startup_pane:
            raise review.UserError("startup pane is not recorded; restart the workspace")
        while not ready.exists():
            startup = tmux("display-message", "-p", "-t", startup_pane, "#{pane_dead}", check=False)
            if (startup.returncode != 0 or startup.stdout.strip() != "0") and not ready.exists():
                raise review.UserError(
                    "startup watcher exited before confirmation completed; "
                    "inspect the startup pane in watchers, then restart the workspace "
                    "using the README recovery instructions"
                )
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
    print(f"Supply the manual at {directory / 'docs/game_reference/manuals'}; FAQs in docs/game_reference/faqs are optional.")


def launch(args: argparse.Namespace) -> int:
    root = Path(review.run_git(["rev-parse", "--show-toplevel"], cwd=args.repo).strip()).resolve()
    if not review.PROJECT_RE.fullmatch(args.project):
        raise review.UserError("invalid project slug")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.session):
        raise review.UserError("session name may contain only letters, digits, underscore, and dash")
    tmux_bin = shutil.which(os.environ.get("AGENT_REVIEW_TMUX_BIN", "tmux"))
    if not tmux_bin:
        raise review.UserError("tmux executable not found")
    if args.check:
        for role in ROLES:
            command = role_command(args, role)
            print(f"{role}: {shlex.join(command)}")
        subprocess.run(["make", "project-doctor", f"PROJECT={args.project}"], cwd=root, check=True)
        issues = reference_tool_issues(project_reference_files(root, args.project))
        if issues:
            raise review.UserError("reference extraction tools are not ready:\n" + "\n".join(issues))
        for identity in ("GIT_AUTHOR_IDENT", "GIT_COMMITTER_IDENT"):
            review.run_git(["var", identity], cwd=root)
        current_state(root, args.project)
        directory = root / "projects" / args.project
        if directory.exists() and not (directory / "project.conf").is_file():
            raise review.UserError(f"existing project directory has no project.conf: {directory}")
        print(f"Setup check passed for {args.project}. No project or tmux session was created.")
        print("Agent login, permissions, and available usage must still be checked at startup.")
        print("Model and effort availability are validated by the chosen agents at startup.")
        return 0
    sessions = tmux(
        "list-sessions", "-F",
        "#{session_id}\t#{session_name}\t#{@nesrev_review_root}\t#{@nesrev_review_project}",
        check=False,
    )
    entries = [line.split("\t") for line in sessions.stdout.splitlines() if line]
    for session_id, name, checkout, project in entries:
        if checkout == str(root) and project == args.project:
            print(f"Reconnecting to {name} for {project}; keeping its existing agents, models, effort, and task.")
            return connect(session_id, name, args.no_attach)
    for session_id, name, checkout, project in entries:
        if name == args.session or checkout == str(root):
            raise review.UserError(
                f"tmux session {name} already exists; use tmux attach -t {name} "
                "(or tmux switch-client -t " + name + " inside tmux)"
            )

    commands = {role: role_command(args, role) for role in ROLES}
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
        config = {
            "root": str(root), "project": args.project, "panes": panes,
            "agents_window": agents_window, "tmux_bin": str(Path(tmux_bin).absolute()),
        }
        review.atomic_write(config_path, json.dumps(config, indent=2) + "\n")
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
        config["startup_pane"] = first
        review.atomic_write(config_path, json.dumps(config, indent=2) + "\n")
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
    print("Check both agents, then choose your manual and optional FAQs in watchers before work begins.")
    return connect(session_id, args.session, args.no_attach)


def main() -> int:
    if len(sys.argv) == 4 and sys.argv[1] == "--worker" and sys.argv[3] in ROLES:
        return run_worker(Path(sys.argv[2]), sys.argv[3])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="project checkout (default: current directory)")
    parser.add_argument("--session", default="nesrev-review", help="session name when creating a new workspace")
    parser.add_argument("--implementer-cmd", default="codex", help="executable and arguments; default: codex")
    parser.add_argument("--reviewer-cmd", help="executable and arguments; default: claude if installed, otherwise codex")
    for role in ROLES:
        parser.add_argument(f"--{role}-model", help=f"model for the {role}; omit to use the agent's default")
        parser.add_argument(
            f"--{role}-effort", f"--{role}-reasoning-effort", dest=f"{role}_effort",
            help=f"inference/reasoning level for the {role} (e.g. low, medium, high); omit to use the agent's default",
        )
    parser.add_argument("--task", default=(
        "Complete any unfinished intake, then continue coherent semantic passes to reviewed gold standard. "
        "Stop only after final gold approval or when specific user input is needed."
    ), help="implementation objective")
    parser.add_argument("--check", action="store_true", help="check tools and Git identity without creating a project or starting agents")
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
