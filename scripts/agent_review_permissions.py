"""Preview and install checkout-local grants for the tmux pass cycle."""

from __future__ import annotations

import hashlib
import json
import shlex
import subprocess
from dataclasses import dataclass
from pathlib import Path

import agent_review as review


DIRECTORY = ".agents/permissions"
RULES = ".codex/rules/nesrev-pass-cycle.rules"
RECEIPT = f"{DIRECTORY}/receipt.json"
GUIDE = f"{DIRECTORY}/commands.md"
ASK_GIT = ("add", "commit", "reset", "restore", "checkout", "switch", "rebase", "merge", "clean", "config", "worktree", "branch")


def option_values(command: list[str], flag: str) -> list[str]:
    return [
        arg.split("=", 1)[1] if arg.startswith(flag + "=") else command[index + 1]
        for index, arg in enumerate(command)
        if arg.startswith(flag + "=") or (arg == flag and index + 1 < len(command))
    ]


def claude_project_files(root: Path) -> dict[str, str]:
    """Reject ambient project configuration, including Git-ignored files."""
    directory = root / ".claude"
    if directory.is_symlink() or (directory.exists() and not directory.is_dir()):
        raise review.UserError("Claude project configuration must be a regular .claude directory")
    tracked = set(review.run_git(["ls-files", "-z", "--", ".claude/"], cwd=root).split("\0")) - {""}
    tree = subprocess.run(["git", "ls-tree", "-r", "--name-only", "-z", "HEAD", "--", ".claude/"],
                          cwd=root, text=True, capture_output=True)
    committed_names = set(tree.stdout.split("\0")) - {""}
    present = {str(path.relative_to(root)) for path in directory.rglob("*")
               if path.is_symlink() or not path.is_dir()}
    hashes = {}
    for name in sorted((tracked | committed_names | present) - {".claude/settings.local.json"}):
        path = root / name
        if name not in tracked or path.resolve() != path or not path.is_file():
            raise review.UserError(f"Claude project input must be committed, unchanged and non-symlinked: {name}")
        committed = subprocess.run(["git", "show", f"HEAD:{name}"], cwd=root, capture_output=True)
        staged = subprocess.run(["git", "diff", "--cached", "--quiet", "HEAD", "--", name], cwd=root)
        content = path.read_bytes()
        if committed.returncode or staged.returncode or committed.stdout != content:
            raise review.UserError(f"Claude project input must be committed, unchanged and non-symlinked: {name}")
        hashes[name] = hashlib.sha256(content).hexdigest()
    return hashes


def launch_configuration(commands: dict[str, list[str]], profile: str, root: Path) -> dict:
    """Describe requested configuration; only the live client can attest loading."""
    records = {}
    for role, command in commands.items():
        agent = Path(command[0]).name
        record = {"profile": profile, "agent": agent}
        if agent == "claude":
            record.update({
                "model_arguments": option_values(command, "--model"),
                "effort_arguments": option_values(command, "--effort"),
                "permission_mode_arguments": option_values(command, "--permission-mode"),
                "setting_sources_arguments": option_values(command, "--setting-sources"),
                "settings_arguments": option_values(command, "--settings"),
                "observed_setting_sources": None,
            })
            if profile == "pass-cycle":
                record.update({
                    "excluded_settings_sources": ["user", "local"],
                    "project_files": claude_project_files(root),
                    "repository_instructions": {
                        "source": "project", "observed_loading": None,
                        "AGENTS.md_sha256": hashlib.sha256((root / "AGENTS.md").read_bytes()).hexdigest()
                        if (root / "AGENTS.md").is_file() else None,
                    },
                    "plugins_from_excluded_settings": "not loaded from those settings",
                    "remaining_ambient_inputs": ["managed policy", "environment", "auto-memory", "account connectors", "ancestor instructions"],
                })
        records[role] = record
    return records


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def native_agent(command: list[str], profile: str = "pass-cycle") -> str:
    agent = Path(command[0]).name
    if agent == "agy" and profile == "pass-cycle":
        raise review.UserError(
            "agy has no managed pass-cycle permission profile; use --permissions inherit "
            "with your agy settings, or explicitly select --permissions bypass. "
            "--sandbox alone does not install scoped grants."
        )
    if agent not in {"codex", "claude", "agy"}:
        supported = "codex or claude" if profile == "pass-cycle" else "codex, claude, or agy"
        raise review.UserError(f"{profile} permissions require {supported}; use --permissions inherit for wrappers")
    # Permission options must come from this profile. Model/effort are independent.
    allowed = {
        "codex": {"--model", "-m", "--config", "-c"},
        "claude": {"--model", "--effort"},
        "agy": {"--model", "-model", "--effort", "-effort"},
    }[agent]
    options = command[1:]
    while options:
        option = options.pop(0)
        flag, equal, value = option.partition("=")
        if flag not in allowed or (not equal and not options):
            raise review.UserError(f"{profile} permissions accept only model/effort agent options; use --permissions inherit for custom options")
        if not equal:
            value = options.pop(0)
        if not value.strip() or value.startswith("-"):
            raise review.UserError("agent options require a nonempty value, not an option")
        if flag in {"--config", "-c"} and not value.startswith("model_reasoning_effort="):
            raise review.UserError(f"{profile} permissions accept only model_reasoning_effort config overrides")
        if "\n" in value or "\r" in value:
            raise review.UserError("agent options must be single-line values")
    return agent


def grants(root: Path, project: str, role: str) -> list[list[str]]:
    tool = review.script_argv(root)
    common = [tool + ["status"]]
    if role == "implementer":
        return common + [
            tool + ["stage-project", project, "--"],
            tool + ["commit-project", project],
            tool + ["start-pass", "--project", project],
            tool + ["ready"], tool + ["reready"], tool + ["archive"],
            tool + ["import-artifact", "--kind", "response"],
            tool + ["checkout-status"],
            tool + ["find-project-symbols", project],
            tool + ["trace-project", project],
            tool + ["analyze-project", project],
        ]
    return common + [
        tool + ["approve"], tool + ["request-changes"],
        tool + ["import-artifact", "--kind", "review"],
        tool + ["checkout-status"],
        tool + ["find-project-symbols", project],
        tool + ["trace-project", project],
        tool + ["analyze-project", project],
    ]


def restrictions(root: Path) -> list[tuple[list[str], str]]:
    result = []
    for git in (["git"], ["git", "-C", str(root)]):
        result.append((git + ["push"], "forbidden"))
        result.extend((git + [action], "prompt") for action in ASK_GIT)
    return result


def claude_reviewer_wrapper_rules(project: str) -> list[str]:
    if not review.PROJECT_RE.fullmatch(project):
        raise review.UserError("invalid project slug for reviewer wrapper grants")
    regenerate = f"make project-regenerate-check PROJECT={project}"
    return [f"Bash({command})" for command in (
        regenerate,
        f"{regenerate} ALLOW_TRAILING_BYTES=1 REGENERATE_DIFF_MAX_LINES=4000",
        f"{regenerate} ALLOW_TRAILING_BYTES=1 REGENERATE_DIFF_MAX_LINES=100000",
        f"make project-hidden-code-scan PROJECT={project}",
    )]


def command_guide(root: Path, project: str) -> str:
    tool = review.script_command(root)
    add, commit = (shlex.join(cmd) for cmd in grants(root, project, "implementer")[1:3])
    return (
        "# Pass-cycle commands\n\n"
        "Use these exact command prefixes, each as a standalone command. Do not wrap them in "
        "another interpreter, environment assignment, shell script, or output redirection. "
        "For Codex, request sandbox escalation when needed; the installed rules can approve the matching command.\n\n"
        f"{review.checkout_status_guidance(root)}\n\n"
        f"{review.project_operations_guidance(root, project)}\n\n"
        "The trace and analysis grants trust the selected project's changing Python tools and their dependencies, "
        "including desktop access outside the Codex sandbox. Both roles receive them; they are not a sandbox "
        "around that code. Capture drivers must use the supervised run_fceux_trace.py lifecycle and bounded scenarios.\n\n"
        f"Write the commit message using the file-edit tool at `projects/{project}/tmp/commit-message.txt`. "
        "Stage only reviewed, explicit project file paths, including deleted files, then commit the staged changes. "
        "Staging rejects directories, pathspec patterns, symlinks, and paths outside this project; "
        "commit refuses unrelated staged files and accepts no path or Git-option suffix:\n\n"
        f"```sh\n{add} <path> <path>\n{commit}\n```\n\n"
        "Use the handoff commands in each watcher prompt. For an approved pass:\n\n"
        f"```sh\n{tool} archive --pass-id <id>\n```\n\n"
        f"{review.reviewer_scratch_guidance(project)}\n\n"
        "Reviewers write Markdown drafts in the project's tmp directory and use import-artifact "
        "to publish them into the current review round. The same applies to implementer responses. "
        "Do not write directly into protected .agents paths.\n\n"
        "These permissions trust the named handoff tool, repository code it runs, and Git hooks. "
        "They are not isolation between agents. Never push projects. Do not change these settings "
        "or switch command forms to evade a prompt or refusal; ask the user if an action needs additional permission.\n"
    )


@dataclass
class Plan:
    root: Path
    project: str
    commands: dict[str, list[str]]
    files: dict[str, str]

    def receipt(self) -> dict:
        return {
            "version": 2, "root": str(self.root), "project": self.project,
            "commands": self.commands,
            "files": {name: digest(text) for name, text in self.files.items()},
            "launch_configuration": launch_configuration(self.commands, "pass-cycle", self.root),
        }

    def preview(self) -> None:
        print("Pass-cycle permissions (checkout-local; no global settings changed):")
        print("Validated project-file staging/commits for the implementer, named review handoffs, live checkout inspection, and scoped Claude file edits.")
        print("Both roles can search project symbols read-only and execute the selected project's tools/trace/run_*.py drivers and analyze_*.py analyzers with desktop access.")
        print("Trace grants trust those changing drivers and their dependencies outside the sandbox, including drivers the agent writes during the pass; they do not constrain what the driver itself can do.")
        print("Analysis grants also execute trusted project code, including analyzers written during the pass; they are not read-only or restricted to the supplied input/output paths.")
        print("Codex keeps workspace-write / on-request. Claude's permission mode, model and effort are explicit below.")
        print("Direct and checkout-scoped git push are blocked; raw add/commit and listed history/destructive Git commands ask.")
        print("Claude retains the project source for repository instructions, including AGENTS.md; user/local settings and their grants and plugins are excluded.")
        print("Project .claude inputs must match committed files (settings.local.json is excluded); their hashes are recorded. Managed policy still applies.")
        print("This records requested sources, not observed loading. Auto-memory, account connectors and environment remain outside this control.")
        print("Existing Codex user/admin grants still apply and may allow more; this is not a security boundary.")
        print("Codex project rules are shared by Codex sessions in this trusted checkout, including the reviewer.")
        print("The approved tool runs repository code and Git hooks. No blanket shell, Python, Git, or make grant is added.")
        if f"{DIRECTORY}/reviewer.json" in self.files:
            print("Claude reviewer Make grants are four exact project-scoped forms, with no argument suffix. They execute trusted repository code and can write derived outputs; trailer overrides still require an audited intake decision.")
        for role, command in self.commands.items():
            print(f"{role} launch: {shlex.join(command)}")
        for name, content in self.files.items():
            if name != GUIDE:
                print(f"\n{name}:\n{content.rstrip()}")
        print(f"Command guide: {GUIDE}; consent record: {RECEIPT}")

    def owned_path(self, name: str) -> Path:
        path = self.root / name
        if path.resolve() != path or not path.is_relative_to(self.root):
            raise review.UserError(f"permission file must not use symlinks or leave the checkout: {path}")
        if path.exists() and not path.is_file():
            raise review.UserError(f"permission path is not a file: {path}")
        return path

    def previous(self) -> dict | None:
        path = self.owned_path(RECEIPT)
        previous = json.loads(path.read_text()) if path.exists() else None
        allowed = {RULES, GUIDE, f"{DIRECTORY}/implementer.json", f"{DIRECTORY}/reviewer.json"}
        if previous is not None and (
            not isinstance(previous, dict) or previous.get("version") not in {1, 2}
            or previous.get("root") != str(self.root)
            or not isinstance(previous.get("files"), dict)
            or not set(previous["files"]).issubset(allowed)
        ):
            raise review.UserError(f"invalid permission receipt: {path}")
        old_files = previous["files"] if previous else {}
        for name in set(old_files) | set(self.files):
            target = self.owned_path(name)
            if target.exists() and (name not in old_files or digest(target.read_text()) != old_files[name]):
                raise review.UserError(f"permission file is unowned or edited; inspect and move it before setup: {target}")
        return previous

    def apply(self) -> None:
        previous = self.previous()
        receipt = self.receipt()
        if previous == receipt and all(self.owned_path(name).exists() for name in self.files):
            print("Reusing the previously approved pass-cycle permissions.")
            return
        self.preview()
        answer = input("Install these pass-cycle permissions for this checkout? Type yes to approve: ").strip().lower()
        if answer != "yes":
            raise review.UserError("permission setup declined; no agents started (use --permissions inherit to keep existing settings)")
        # Recheck after the human pause, before writing any configuration.
        if self.previous() != previous:
            raise review.UserError("permission receipt changed during confirmation; rerun setup")
        if self.receipt() != receipt:
            raise review.UserError("Claude project inputs changed during confirmation; rerun setup")
        review.ensure_runtime_excludes(self.root)
        for name, content in self.files.items():
            review.atomic_write(self.owned_path(name), content)
        for name in set(previous["files"] if previous else {}) - set(self.files):
            self.owned_path(name).unlink(missing_ok=True)
        review.atomic_write(self.owned_path(RECEIPT), json.dumps(receipt, indent=2) + "\n")


def build_plan(root: Path, project: str, commands: dict[str, list[str]],
               claude_permission_mode: str = "default") -> Plan:
    if claude_permission_mode not in {"default", "dontAsk"}:
        raise review.UserError("managed Claude permission mode must be default or dontAsk")
    root = root.resolve()
    files = {GUIDE: command_guide(root, project)}
    configured = {}
    codex_grants = []
    for role, command in commands.items():
        agent = native_agent(command)
        allowed = grants(root, project, role)
        if agent == "codex":
            codex_grants.extend(allowed)
            configured[role] = command + [
                "--sandbox", "workspace-write", "--ask-for-approval", "on-request",
                "--config", 'approval_reviewer="user"',
            ]
        elif agent == "claude":
            for flag in ("--model", "--effort"):
                if len(option_values(command, flag)) != 1:
                    raise review.UserError(
                        f"pass-cycle Claude {role} requires exactly one explicit {flag}; "
                        f"set --{role}-{flag[2:]} or the native option in --{role}-cmd"
                    )
            # These characters are patterns in Claude rules, even inside shell quotes.
            for value in [str(root), *review.script_argv(root)]:
                if any(char in value for char in "*?[]{}\n\r\\"):
                    raise review.UserError("Claude permission paths cannot contain pattern characters; use --permissions inherit")
            settings = f"{DIRECTORY}/{role}.json"
            edits = root / "projects" / project
            if role == "reviewer":
                edits /= "tmp"
            permissions = {
                "allow": [f"Bash({shlex.join(argv)} *)" for argv in allowed]
                + [f"Edit(/{edits}/**)", f"Write(/{edits}/**)"],
                "ask": [f"Bash({shlex.join(argv)} *)" for argv, decision in restrictions(root) if decision == "prompt"],
                "deny": [f"Bash({shlex.join(argv)} *)" for argv, decision in restrictions(root) if decision == "forbidden"],
            }
            if role == "implementer":
                permissions["allow"].append(f"Bash({shlex.join(allowed[2])})")
            elif role == "reviewer":
                permissions["allow"].extend(claude_reviewer_wrapper_rules(project))
            files[settings] = json.dumps({"permissions": permissions}, indent=2) + "\n"
            configured[role] = command + [
                "--permission-mode", claude_permission_mode, "--setting-sources", "project",
                "--settings", str(root / settings),
            ]
    if codex_grants:
        entries = [(argv, "allow") for argv in codex_grants] + restrictions(root)
        files[RULES] = "# Managed by the NESrev launcher after explicit user consent.\n" + "".join(dict.fromkeys(
            f"prefix_rule(pattern={json.dumps(argv)}, decision={json.dumps(decision)})\n"
            for argv, decision in entries
        ))
    plan = Plan(root, project, configured, files)
    plan.receipt()
    return plan
