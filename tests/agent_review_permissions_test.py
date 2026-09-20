#!/usr/bin/env python3
"""Permission setup consent, scope, and native Codex rule evaluation."""

import contextlib
import io
import json
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
import agent_review as review
import agent_review_permissions as permissions


class PermissionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / "checkout ' with $spaces"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def plan(self, implementer="codex", reviewer="claude", project="demo"):
        return permissions.build_plan(self.root, project, {
            "implementer": [f"/test/{implementer}"], "reviewer": [f"/test/{reviewer}"],
        })

    def apply(self, plan, answer="yes"):
        with patch("builtins.input", return_value=answer) as prompt, contextlib.redirect_stdout(io.StringIO()):
            plan.apply()
        return prompt

    def test_preview_creates_nothing_and_shows_exact_rules_and_limits(self):
        before = list(self.root.rglob("*"))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.plan().preview()
        self.assertEqual(before, list(self.root.rglob("*")))
        for text in ("Existing user/admin grants", "shared by Codex sessions", "--repo", "--kind", "no global settings"):
            self.assertIn(text, out.getvalue())

    def test_all_role_combinations_keep_native_models_and_scope_claude_grants(self):
        for implementer in ("codex", "claude"):
            for reviewer in ("codex", "claude"):
                with self.subTest(implementer=implementer, reviewer=reviewer):
                    plan = self.plan(implementer, reviewer)
                    for role, agent in (("implementer", implementer), ("reviewer", reviewer)):
                        command = plan.commands[role]
                        self.assertNotIn("--model", command)
                        self.assertFalse(any("model_reasoning_effort" in arg for arg in command))
                        if agent == "codex":
                            self.assertEqual(command[1:5], ["--sandbox", "workspace-write", "--ask-for-approval", "on-request"])
                            self.assertIn('approval_reviewer="user"', command)
                        else:
                            settings = json.loads(plan.files[f"{permissions.DIRECTORY}/{role}.json"])["permissions"]
                            edit = f"Edit(/{self.root}/projects/demo" + ("/tmp" if role == "reviewer" else "") + "/**)"
                            self.assertIn(edit, settings["allow"])
                            for rule in settings["allow"]:
                                self.assertNotIn("Bash(git *)", rule)
                                if role == "reviewer":
                                    self.assertNotIn(" commit ", rule)
                                    self.assertNotIn("start-pass", rule)

    def test_model_options_survive_and_permission_overrides_are_refused(self):
        plan = permissions.build_plan(self.root, "demo", {
            "implementer": ["codex", "--model", "chosen", "--config", 'model_reasoning_effort="high"'],
            "reviewer": ["claude", "--effort", "medium"],
        })
        self.assertIn("chosen", plan.commands["implementer"])
        self.assertIn("medium", plan.commands["reviewer"])
        for options in (["--dangerously-bypass-approvals-and-sandbox"], ["--approve-for-me"],
                        ["--sandbox", "danger-full-access"], ["--config", "approval_policy=\"never\""],
                        ["--config", "model_reasoning_effort=\"high\"\napproval_policy=\"never\""],
                        ["--settings", "evil.json"], ["--permission-mode", "bypassPermissions"]):
            with self.subTest(options=options), self.assertRaises(review.UserError):
                permissions.build_plan(self.root, "demo", {"implementer": ["codex", *options]})

    def test_decline_and_eof_do_not_install_anything(self):
        for answer in ("", "no", "y"):
            with self.assertRaisesRegex(review.UserError, "declined"):
                self.apply(self.plan(), answer)
        with patch("builtins.input", side_effect=EOFError), contextlib.redirect_stdout(io.StringIO()), self.assertRaises(EOFError):
            self.plan().apply()
        self.assertFalse((self.root / ".agents").exists())
        self.assertFalse((self.root / ".codex").exists())

    def test_install_is_local_ignored_and_reused_without_another_prompt(self):
        plan = self.plan()
        self.assertEqual(self.apply(plan).call_count, 1)
        self.assertEqual(self.apply(plan).call_count, 0)
        for name in [*plan.files, permissions.RECEIPT]:
            subprocess.run(["git", "check-ignore", "-q", name], cwd=self.root, check=True)
        self.assertEqual(json.loads((self.root / permissions.RECEIPT).read_text()), plan.receipt())

    def test_documented_git_commands_create_a_local_commit_from_another_cwd(self):
        for key, value in (("user.name", "Test"), ("user.email", "test@example.invalid"), ("commit.gpgsign", "false")):
            subprocess.run(["git", "-C", str(self.root), "config", key, value], check=True)
        source = self.root / "projects/demo/source.asm"
        source.parent.mkdir(parents=True)
        source.write_text("RunGame:\n  RTS\n")
        message = self.root / "projects/demo/tmp/commit-message.txt"
        message.parent.mkdir()
        message.write_text("Describe game entry point\n")
        add, commit = permissions.grants(self.root, "demo", "implementer")[1:3]
        subprocess.run([*add, "projects/demo/source.asm"], cwd=Path(self.temp.name), check=True)
        subprocess.run(commit, cwd=Path(self.temp.name), check=True, capture_output=True)
        subject = subprocess.check_output(["git", "-C", str(self.root), "log", "-1", "--format=%s"], text=True)
        self.assertEqual(subject.strip(), "Describe game entry point")

    def test_project_or_role_change_requires_fresh_consent_and_removes_old_owned_rules(self):
        self.apply(self.plan())
        changed = self.plan("claude", "claude", project="another")
        self.assertEqual(self.apply(changed).call_count, 1)
        self.assertFalse((self.root / permissions.RULES).exists())
        self.assertIn("another", (self.root / permissions.GUIDE).read_text())

    def test_missing_file_requires_reconfirmation(self):
        plan = self.plan()
        self.apply(plan)
        (self.root / permissions.RULES).unlink()
        self.assertEqual(self.apply(plan).call_count, 1)

    def test_unowned_and_edited_files_are_not_overwritten(self):
        path = self.root / permissions.RULES
        path.parent.mkdir(parents=True)
        path.write_text("user configuration")
        with self.assertRaisesRegex(review.UserError, "unowned or edited"):
            self.apply(self.plan())
        path.unlink()
        self.apply(self.plan())
        path.write_text("user modification")
        with self.assertRaisesRegex(review.UserError, "unowned or edited"):
            self.apply(self.plan())
        self.assertEqual(path.read_text(), "user modification")

    def test_symlinks_and_receipt_path_injection_are_refused(self):
        outside = Path(self.temp.name) / "outside"
        outside.mkdir()
        (self.root / ".codex").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(review.UserError, "symlinks"):
            self.apply(self.plan())
        self.assertFalse(list(outside.iterdir()))
        (self.root / ".codex").unlink()
        self.apply(self.plan())
        receipt = self.root / permissions.RECEIPT
        value = json.loads(receipt.read_text())
        value["files"]["../../outside"] = "fake"
        receipt.write_text(json.dumps(value))
        with self.assertRaisesRegex(review.UserError, "invalid permission receipt"):
            self.apply(self.plan())

    def test_file_changed_during_confirmation_is_not_overwritten(self):
        plan = self.plan()
        def change(_):
            target = self.root / permissions.RULES
            target.parent.mkdir(parents=True)
            target.write_text("concurrent configuration")
            return "yes"
        with patch("builtins.input", side_effect=change), contextlib.redirect_stdout(io.StringIO()), self.assertRaises(review.UserError):
            plan.apply()
        self.assertFalse((self.root / permissions.RECEIPT).exists())

    def test_claude_wildcard_paths_are_not_treated_as_literal(self):
        for char in "*?[]\\":
            with self.subTest(char=char), self.assertRaisesRegex(review.UserError, "pattern characters"):
                permissions.build_plan(self.root / f"bad{char}path", "demo", {"reviewer": ["claude"]})

    @unittest.skipUnless(shutil.which("codex"), "Codex CLI not installed")
    def test_native_codex_policy_allows_exact_handoffs_but_not_generic_execution(self):
        plan = self.plan("codex", "codex")
        rules = Path(self.temp.name) / "generated.rules"
        rules.write_text(plan.files[permissions.RULES])
        def decision(argv, extra=()):
            command = [shutil.which("codex"), "execpolicy", "check", "--rules", str(rules)]
            for file in extra:
                command.extend(["--rules", str(file)])
            result = subprocess.run([*command, "--", *argv], text=True, capture_output=True, check=True)
            return json.loads(result.stdout).get("decision")
        for role in ("implementer", "reviewer"):
            for argv in permissions.grants(self.root, "demo", role):
                with self.subTest(argv=argv):
                    self.assertEqual(decision(argv), "allow")
                    self.assertEqual(shlex.split(shlex.join(argv)), argv)
        unsafe = ([sys.executable, "-c", "print('unrelated')"], ["bash", "-c", "echo unrelated"],
                  ["git", "-C", str(self.root), "commit", "--amend"], ["make", "arbitrary-target"],
                  review.script_argv(self.root) + ["watch", "--notify", "arbitrary-command"],
                  review.script_argv(self.root / "other") + ["approve"],
                  ["git", "-C", str(self.root / "other"), "add", "--", "."])
        for argv in unsafe:
            with self.subTest(argv=argv):
                self.assertNotEqual(decision(argv), "allow")
        inherited = Path(self.temp.name) / "inherited.rules"
        inherited.write_text('prefix_rule(pattern=["git"], decision="allow")\n')
        self.assertEqual(decision(["git", "push"], [inherited]), "forbidden")
        self.assertEqual(decision(["git", "-C", str(self.root), "reset", "--hard"], [inherited]), "prompt")


if __name__ == "__main__":
    unittest.main()
