"""Preview and install checkout-local grants for the tmux pass cycle."""

from __future__ import annotations

import hashlib
import json
import shlex
from dataclasses import dataclass
from pathlib import Path

import agent_review as review


DIRECTORY = ".agents/permissions"
RULES = ".codex/rules/nesrev-pass-cycle.rules"
RECEIPT = f"{DIRECTORY}/receipt.json"
GUIDE = f"{DIRECTORY}/commands.md"
ASK_GIT = ("reset", "restore", "checkout", "switch", "rebase", "merge", "clean", "config", "worktree", "branch")


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def native_agent(command: list[str]) -> str:
    agent = Path(command[0]).name
    if agent not in {"codex", "claude"}:
        raise review.UserError("pass-cycle permissions require codex or claude; use --permissions inherit for wrappers")
    # Permission options must come from this profile. Model/effort are independent.
    options = command[1:]
    while options:
        option = options.pop(0)
        flag, equal, value = option.partition("=")
        allowed = {"--model", "-m", "--config", "-c"} if agent == "codex" else {"--model", "--effort"}
        if flag not in allowed or (not equal and not options):
            raise review.UserError("pass-cycle permissions accept only model/effort agent options; use --permissions inherit for custom options")
        if not equal:
            value = options.pop(0)
        if flag in {"--config", "-c"} and not value.startswith("model_reasoning_effort="):
            raise review.UserError("pass-cycle permissions accept only model_reasoning_effort config overrides")
        if "\n" in value or "\r" in value:
            raise review.UserError("agent options must be single-line values")
    return agent


def grants(root: Path, project: str, role: str) -> list[list[str]]:
    tool = review.script_argv(root)
    common = [tool + ["status"]]
    if role == "implementer":
        return common + [
            ["git", "-C", str(root), "add", "--"],
            ["git", "-C", str(root), "commit", "--file", f"projects/{project}/tmp/commit-message.txt", "--"],
            tool + ["start-pass", "--project", project],
            tool + ["reready"], tool + ["archive"],
            tool + ["import-artifact", "--kind", "response"],
        ]
    return common + [
        tool + ["approve"], tool + ["request-changes"],
        tool + ["import-artifact", "--kind", "review"],
    ]


def restrictions(root: Path) -> list[tuple[list[str], str]]:
    result = []
    for git in (["git"], ["git", "-C", str(root)]):
        result.append((git + ["push"], "forbidden"))
        result.extend((git + [action], "prompt") for action in ASK_GIT)
    return result


def command_guide(root: Path, project: str) -> str:
    tool = review.script_command(root)
    add, commit = (shlex.join(cmd) for cmd in grants(root, project, "implementer")[1:3])
    return (
        "# Pass-cycle commands\n\n"
        "Use these exact command prefixes, each as a standalone command. Do not wrap them in "
        "another interpreter, environment assignment, shell script, or output redirection. "
        "For Codex, request sandbox escalation when needed; the installed rules can approve the matching command.\n\n"
        f"Write the commit message using the file-edit tool at `projects/{project}/tmp/commit-message.txt`. "
        "Stage only reviewed, explicit paths, including deleted paths, then commit the staged changes:\n\n"
        f"```sh\n{add} <path> <path>\n{commit}\n```\n\n"
        "Use the handoff commands in each watcher prompt. For an approved pass:\n\n"
        f"```sh\n{tool} archive --pass-id <id>\n```\n\n"
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
            "version": 1, "root": str(self.root), "project": self.project,
            "commands": self.commands,
            "files": {name: digest(text) for name, text in self.files.items()},
        }

    def preview(self) -> None:
        print("Pass-cycle permissions (checkout-local; no global settings changed):")
        print("Local staging/commits for the implementer, named review handoffs, and scoped Claude file edits.")
        print("Codex keeps workspace-write / on-request; Claude keeps manual approval for unlisted actions.")
        print("Direct and checkout-scoped git push are blocked; listed history/destructive Git commands ask.")
        print("Existing user/admin grants still apply and may allow more; this is not a permissions reset or a security boundary.")
        print("Codex project rules are shared by Codex sessions in this trusted checkout, including the reviewer.")
        print("The approved tool runs repository code and Git hooks. No blanket shell, Python, Git, or make grant is added.")
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
            not isinstance(previous, dict) or previous.get("version") != 1
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
        review.ensure_runtime_excludes(self.root)
        for name, content in self.files.items():
            review.atomic_write(self.owned_path(name), content)
        for name in set(previous["files"] if previous else {}) - set(self.files):
            self.owned_path(name).unlink(missing_ok=True)
        review.atomic_write(self.owned_path(RECEIPT), json.dumps(receipt, indent=2) + "\n")


def build_plan(root: Path, project: str, commands: dict[str, list[str]]) -> Plan:
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
        else:
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
            files[settings] = json.dumps({"permissions": permissions}, indent=2) + "\n"
            configured[role] = command + ["--permission-mode", "default", "--settings", str(root / settings)]
    if codex_grants:
        entries = [(argv, "allow") for argv in codex_grants] + restrictions(root)
        files[RULES] = "# Managed by the NESrev launcher after explicit user consent.\n" + "".join(dict.fromkeys(
            f"prefix_rule(pattern={json.dumps(argv)}, decision={json.dumps(decision)})\n"
            for argv, decision in entries
        ))
    return Plan(root, project, configured, files)
