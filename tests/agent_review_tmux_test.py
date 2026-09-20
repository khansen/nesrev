#!/usr/bin/env python3
"""Launcher preflight, transport setup, and startup ordering tests."""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
import agent_review_tmux as launcher
import agent_review as review
import reference_tools as refs


class LauncherTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = (Path(self.temp.name) / "checkout with spaces ' and $dollars").resolve()
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "projects/demo").mkdir(parents=True)
        (self.root / "projects/demo/project.conf").write_text('PROJECT="demo"\n')
        self.references = self.root / "projects/demo/docs/game_reference"
        self.manual = self.references / "manuals/manual.txt"
        self.manual.parent.mkdir(parents=True)
        self.manual.write_text("User-supplied manual text.\n")
        self.log = Path(self.temp.name) / "tmux.jsonl"
        self.stub = Path(self.temp.name) / "tmux-stub"
        self.stub.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            f"with open({str(self.log)!r}, 'a') as f: f.write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "cmd = sys.argv[1]\n"
            "if cmd == os.environ.get('TMUX_FAIL_COMMAND'):\n"
            "    print('simulated tmux failure', file=sys.stderr); sys.exit(1)\n"
            "if cmd == 'list-sessions': print(os.environ.get('TMUX_SESSIONS', ''))\n"
            "elif cmd == 'new-session': print('$1\\t@10\\t%20')\n"
            "elif cmd == 'new-window': print('@11\\t%22')\n"
            "elif cmd == 'split-window': print('%21' if '-h' in sys.argv else '%23')\n"
            "elif cmd == 'display-message': print('0')\n"
        )
        self.stub.chmod(0o755)
        self.agent_log = Path(self.temp.name) / "agent.json"
        self.agent = Path(self.temp.name) / "agent with spaces"
        self.agent.write_text(
            f"#!{sys.executable}\nimport json, sys\n"
            f"with open({str(self.agent_log)!r}, 'w') as f: json.dump(sys.argv[1:], f)\n"
        )
        self.agent.chmod(0o755)
        self.env = patch.dict(os.environ, {
            "AGENT_REVIEW_TMUX_BIN": str(self.stub), "TMUX_SESSIONS": "", "TMUX_FAIL_COMMAND": "",
        })
        self.env.start()
        self.addCleanup(self.env.stop)
        self.args = argparse.Namespace(
            repo=self.root, project="demo", session="review-test",
            implementer_cmd=shlex.quote(str(self.agent)),
            reviewer_cmd=shlex.quote(str(self.agent)), task="Continue demo passes.", no_attach=True, check=False,
        )

    def launch(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return launcher.launch(self.args)

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def config(self):
        return next((self.root / ".agents/logs").glob("tmux-*/workspace.json"))

    def scaffold_tools(self, doctor_fails=False):
        self.root.joinpath("Makefile").write_text(
            "project-doctor:\n\t@echo doctor >> scaffold.log\n"
            + ("\t@exit 1\n" if doctor_fails else "")
            + "project-init:\n\t@echo init >> scaffold.log\n\t@bash "
            + shlex.quote(str(REPO / "scripts/new_project.sh"))
            + ' "$(PROJECT)" > scaffold.out\n'
        )

    def state(self, project="demo", status="READY_FOR_REVIEW"):
        state = {
            "project": project, "status": status, "run_id": "demo-pass-1", "round": 1,
            "review_head": "deadbeef", "prompts": {"reviewer": ".agents/prompt.md"},
        }
        review.write_state(self.root, state)
        (self.root / ".agents/prompt.md").write_text("Review the committed pass.\n")
        return state

    def test_creates_two_agents_and_two_watchers_without_pasting_before_confirmation(self):
        self.assertEqual(self.launch(), 0)
        calls = self.calls()
        self.assertEqual(sum(c[0] == "respawn-pane" for c in calls), 2)
        self.assertEqual(sum(c[0] == "split-window" for c in calls), 2)
        self.assertFalse(any(c[0] in {"send-keys", "load-buffer", "paste-buffer"} for c in calls))
        config = json.loads(self.config().read_text())
        self.assertEqual(config["panes"], {"implementer": "%20", "reviewer": "%21"})
        self.assertEqual(config["root"], str(self.root))
        self.assertIn("never push the projects branch", self.config().with_name("task.md").read_text())
        self.assertFalse(self.config().with_name("ready").exists())

    def test_agent_arguments_and_prompt_survive_shell_without_expansion(self):
        marker = Path(self.temp.name) / "must-not-exist"
        literal = f"$(touch {shlex.quote(str(marker))}) `touch {shlex.quote(str(marker))}` $HOME ; newline\n'quoted'"
        self.args.implementer_cmd += " " + shlex.quote(literal)
        self.launch()
        command = next(c[-1] for c in self.calls() if c[0] == "respawn-pane")
        subprocess.run(["/bin/sh", "-c", command], check=True, cwd=self.root)
        args = json.loads(self.agent_log.read_text())
        self.assertEqual(args[0], literal)
        self.assertIn("You are the implementer", args[1])
        self.assertIn(str(self.root), args[1])
        self.assertFalse(marker.exists())

    def test_missing_executable_fails_before_creating_any_tmux_resources(self):
        self.args.reviewer_cmd = "/nonexistent/agent"
        with self.assertRaisesRegex(review.UserError, "agent executable not found"):
            self.launch()
        self.assertTrue(all(c[0] == "list-sessions" for c in self.calls()))

    def test_incomplete_existing_directory_is_not_overwritten(self):
        self.args.project = "partial"
        directory = self.root / "projects/partial"
        directory.mkdir()
        sentinel = directory / "notes.txt"
        sentinel.write_text("user work")
        with self.assertRaisesRegex(review.UserError, "has no project.conf"):
            self.launch()
        self.assertEqual(sentinel.read_text(), "user work")
        self.assertTrue(all(c[0] == "list-sessions" for c in self.calls()))

    def test_new_project_uses_canonical_scaffold_and_routes_intake_before_passes(self):
        self.scaffold_tools()
        self.args.project = "new_game"
        self.launch()
        project = self.root / "projects/new_game"
        self.assertTrue((project / "project.conf").is_file())
        self.assertTrue((project / "reference").is_dir())
        self.assertFalse((project / "reference/new_game.nes").exists())
        self.assertEqual((self.root / "scaffold.log").read_text().splitlines(), ["doctor", "init"])
        task = self.config().with_name("task.md").read_text()
        self.assertIn("NEW_PROJECT.md", task)
        self.assertIn("--pass-id 0", task)
        self.assertIn("two required commits", task)
        self.assertIn("resume its pass cycle", task)

    def test_missing_toolchain_does_not_create_project_or_agents(self):
        self.scaffold_tools(doctor_fails=True)
        self.args.project = "new_game"
        with self.assertRaises(subprocess.CalledProcessError):
            self.launch()
        self.assertFalse((self.root / "projects/new_game").exists())
        self.assertEqual((self.root / "scaffold.log").read_text().splitlines(), ["doctor"])
        self.assertTrue(all(c[0] == "list-sessions" for c in self.calls()))

    def test_setup_check_does_not_create_project_or_agents(self):
        self.scaffold_tools()
        subprocess.run(["git", "config", "user.name", "Test"], cwd=self.root, check=True)
        subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=self.root, check=True)
        self.args.project = "new_game"
        self.args.check = True
        self.assertEqual(self.launch(), 0)
        self.assertFalse((self.root / "projects/new_game").exists())
        self.assertFalse((self.root / ".agents").exists())
        self.assertEqual((self.root / "scaffold.log").read_text().splitlines(), ["doctor"])
        self.assertEqual(self.calls(), [])

    def test_setup_check_reports_missing_toolchain_without_launching(self):
        self.scaffold_tools(doctor_fails=True)
        self.args.check = True
        with self.assertRaises(subprocess.CalledProcessError):
            self.launch()
        self.assertFalse((self.root / ".agents").exists())

    def test_setup_check_rejects_missing_tools_for_supplied_pdf_without_launching(self):
        self.scaffold_tools()
        self.args.check = True
        self.manual.with_suffix(".pdf").write_text("PDF fixture")
        with patch.object(refs, "tool_status", return_value=(False, "install reference tool")):
            with self.assertRaisesRegex(review.UserError, "reference extraction tools"):
                self.launch()
        self.assertFalse((self.root / ".agents").exists())
        self.assertEqual(self.calls(), [])
        self.assertEqual(self.calls(), [])

    def test_default_reviewer_falls_back_to_codex_when_claude_is_absent(self):
        self.args.reviewer_cmd = None
        which = launcher.shutil.which
        def installed(value):
            return None if value == "claude" else str(self.agent) if value == "codex" else which(value)
        with patch.object(launcher.shutil, "which", side_effect=installed):
            self.launch()
        commands = [c[-1] for c in self.calls() if c[0] == "respawn-pane"]
        self.assertEqual(len(commands), 2)
        for command in commands:
            self.assertEqual(shlex.split(command)[1], str(self.agent))
        self.assertIn("You are the reviewer", commands[1])

    def test_default_reviewer_prefers_installed_claude(self):
        self.args.reviewer_cmd = None
        which = launcher.shutil.which
        def installed(value):
            if value == "claude":
                return str(self.agent)
            if value == "codex":
                raise AssertionError("should use installed Claude")
            return which(value)
        with patch.object(launcher.shutil, "which", side_effect=installed):
            self.launch()
        command = [c[-1] for c in self.calls() if c[0] == "respawn-pane"][1]
        self.assertEqual(shlex.split(command)[1], str(self.agent))

    def test_explicit_missing_reviewer_does_not_silently_fallback(self):
        self.args.reviewer_cmd = "/missing/chosen-reviewer"
        with self.assertRaisesRegex(review.UserError, "agent executable not found"):
            self.launch()
        self.assertFalse(any(c[0] == "new-session" for c in self.calls()))

    def test_claude_implementer_and_codex_reviewer_receive_their_own_roles(self):
        self.args.implementer_cmd = "claude --model chosen-implementer"
        self.args.reviewer_cmd = "codex --model chosen-reviewer"
        which = launcher.shutil.which
        def installed(value):
            return f"/agents/{value}" if value in ("claude", "codex") else which(value)
        with patch.object(launcher.shutil, "which", side_effect=installed):
            self.launch()
        commands = [shlex.split(c[-1]) for c in self.calls() if c[0] == "respawn-pane"]
        self.assertEqual(commands[0][1:4], ["/agents/claude", "--model", "chosen-implementer"])
        self.assertIn("You are the implementer", commands[0][4])
        self.assertEqual(commands[1][1:4], ["/agents/codex", "--model", "chosen-reviewer"])
        self.assertIn("You are the reviewer", commands[1][4])

    def test_existing_project_is_not_rescaffolded(self):
        config = self.root / "projects/demo/project.conf"
        original = config.read_bytes()
        self.launch()
        self.assertEqual(config.read_bytes(), original)
        self.assertFalse((self.root / "scaffold.log").exists())

    def test_existing_session_and_other_session_for_same_checkout_are_preserved(self):
        for sessions in ("$5\treview-test\t/other/checkout\tdemo", f"$5\tanother-name\t{self.root}\tother"):
            with self.subTest(sessions=sessions), patch.dict(os.environ, {"TMUX_SESSIONS": sessions}):
                with self.assertRaisesRegex(review.UserError, "already exists"):
                    self.launch()
        self.assertTrue(all(c[0] == "list-sessions" for c in self.calls()))

    def test_repeated_launch_reconnects_without_restarting_agents_or_wiping_state(self):
        self.state()
        before = review.state_path(self.root).read_bytes()
        self.args.no_attach = False
        self.args.reviewer_cmd = "/not/needed/when/reconnecting"
        with patch.dict(os.environ, {"TMUX": "live", "TMUX_SESSIONS": f"$5\texisting-name\t{self.root}\tdemo"}):
            self.launch()
        self.assertEqual([c[0] for c in self.calls()], ["list-sessions", "switch-client"])
        self.assertEqual(self.calls()[-1], ["switch-client", "-t", "$5"])
        self.assertEqual(review.state_path(self.root).read_bytes(), before)
        self.assertFalse((self.root / ".agents/logs").exists())

    def test_repeated_detached_launch_does_not_attach_or_create_agents(self):
        with patch.dict(os.environ, {"TMUX_SESSIONS": f"$5\texisting-name\t{self.root}\tdemo"}):
            self.launch()
        self.assertEqual([c[0] for c in self.calls()], ["list-sessions"])

    def test_setup_failure_removes_only_the_session_it_created(self):
        with patch.dict(os.environ, {"TMUX_FAIL_COMMAND": "new-window"}):
            with self.assertRaises(subprocess.CalledProcessError):
                self.launch()
        self.assertEqual(self.calls()[-1], ["kill-session", "-t", "$1"])

    def test_failed_session_creation_does_not_kill_an_existing_session(self):
        with patch.dict(os.environ, {"TMUX_FAIL_COMMAND": "new-session"}):
            with self.assertRaises(subprocess.CalledProcessError):
                self.launch()
        self.assertFalse(any(c[0] == "kill-session" for c in self.calls()))

    def test_unfinished_other_project_review_blocks_launch_without_changing_state(self):
        self.state(project="other")
        before = review.state_path(self.root).read_bytes()
        with self.assertRaisesRegex(review.UserError, "unfinished review for other"):
            self.launch()
        self.assertEqual(before, review.state_path(self.root).read_bytes())
        self.assertTrue(all(c[0] == "list-sessions" for c in self.calls()))

    def test_completed_other_project_review_is_preserved(self):
        self.state(project="other", status="APPROVED")
        before = review.state_path(self.root).read_bytes()
        self.launch()
        self.assertEqual(before, review.state_path(self.root).read_bytes())

    def test_inside_tmux_switches_client_instead_of_nesting_an_attachment(self):
        self.args.no_attach = False
        with patch.dict(os.environ, {"TMUX": "existing-session"}):
            self.launch()
        self.assertEqual(self.calls()[-1], ["switch-client", "-t", "$1"])

    def test_outside_tmux_attaches(self):
        self.args.no_attach = False
        with patch.dict(os.environ, {"TMUX": ""}):
            self.launch()
        self.assertEqual(self.calls()[-1], ["attach-session", "-t", "$1"])

    def run_worker(self, answer="", notify=None, role="implementer", output=None):
        previous = Path.cwd()
        self.addCleanup(os.chdir, previous)
        answers = [answer] if isinstance(answer, str) else answer
        with patch("builtins.input", side_effect=answers), \
             patch.object(launcher.os, "execve") as execute, \
             contextlib.redirect_stdout(output if output is not None else io.StringIO()):
            if notify is None:
                result = launcher.run_worker(self.config(), role)
            else:
                with patch.object(launcher.subprocess, "run", side_effect=notify):
                    result = launcher.run_worker(self.config(), role)
        return result, execute

    def test_startup_eof_does_not_arm_watchers_or_send_a_task(self):
        self.launch()
        with self.assertRaises(EOFError):
            self.run_worker(answer=EOFError)
        self.assertFalse(self.config().with_name("ready").exists())
        self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))

    def test_missing_manual_never_starts_on_enter_even_after_intake_approval(self):
        self.manual.unlink()
        self.manual.with_name(".gitkeep").write_text("placeholder")
        self.manual.with_name("empty.pdf").touch()
        hidden = self.manual.parent / ".cache"
        hidden.mkdir()
        (hidden / "manual.txt").write_text("not an input")
        (self.references / "faqs").mkdir()
        (self.references / "faqs/guide.txt").write_text("Optional guide is not a manual.")
        self.launch()
        for status in (None, "IMPLEMENTING", "READY_FOR_REVIEW", "CHANGES_REQUESTED", "APPROVED"):
            with self.subTest(status=status):
                if status:
                    self.state(status=status)
                before = review.state_path(self.root).read_bytes() if status else None
                output = io.StringIO()
                with self.assertRaises(EOFError):
                    self.run_worker(answer=["", "", EOFError], output=output)
                self.assertIn("NEEDS INPUT", output.getvalue())
                self.assertFalse(self.config().with_name("ready").exists())
                self.assertFalse((self.root / ".agents/reference_intake/demo.json").exists())
                self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))
                if status:
                    self.assertEqual(review.state_path(self.root).read_bytes(), before)

    def test_user_can_supply_manual_and_optional_faq_while_startup_waits(self):
        self.manual.unlink()
        self.launch()
        prompts = []
        output = io.StringIO()
        def answer(prompt):
            prompts.append(prompt)
            self.assertFalse(self.config().with_name("ready").exists())
            self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))
            self.assertIn(str(self.manual.parent), output.getvalue())
            self.assertIn(str(self.references / "faqs"), output.getvalue())
            if len(prompts) == 2:
                self.manual.write_text("Supplied after the first prompt.")
                (self.references / "faqs").mkdir()
                (self.references / "faqs/guide.txt").write_text("Optional FAQ.")
            self.assertLessEqual(len(prompts), 2)
            return ""
        self.run_worker(answer=answer, output=output)
        self.assertEqual(len(prompts), 2)
        record = json.loads((self.root / ".agents/reference_intake/demo.json").read_text())
        self.assertEqual(record["manual_decision"], "provided")
        self.assertEqual(record["manual_files"], ["projects/demo/docs/game_reference/manuals/manual.txt"])
        self.assertEqual(record["faq_files"], ["projects/demo/docs/game_reference/faqs/guide.txt"])
        self.assertTrue(self.config().with_name("ready").exists())

    def test_explicit_manual_waiver_warns_before_choice_and_persists_for_restart(self):
        self.manual.unlink()
        (self.references / "faqs").mkdir()
        (self.references / "faqs/guide.txt").write_text("Still process the FAQ after a manual waiver.")
        self.launch()
        output = io.StringIO()
        def waive(prompt):
            self.assertIn(launcher.MANUAL_WARNING, output.getvalue())
            self.assertIn("continue without a manual", prompt)
            return "continue without a manual"
        self.run_worker(answer=waive, output=output)
        record_path = self.root / ".agents/reference_intake/demo.json"
        record = json.loads(record_path.read_text())
        self.assertEqual(record["manual_decision"], "waived")
        self.assertEqual(record["warning"], launcher.MANUAL_WARNING)
        self.assertEqual(record["faq_files"], ["projects/demo/docs/game_reference/faqs/guide.txt"])
        self.assertTrue(self.config().with_name("ready").exists())
        with patch("builtins.input", side_effect=[""]) as answer, contextlib.redirect_stdout(output):
            launcher.confirm_references(self.root, "demo")
        answer.assert_called_once()
        self.assertIn("earlier explicit choice", output.getvalue())
        self.assertEqual(json.loads(record_path.read_text()), record)

    def test_ambiguous_answers_do_not_waive_a_missing_manual(self):
        self.manual.unlink()
        self.launch()
        with self.assertRaises(EOFError):
            self.run_worker(answer=["yes", "skip", "no references available", EOFError])
        self.assertFalse(self.config().with_name("ready").exists())
        self.assertFalse((self.root / ".agents/reference_intake/demo.json").exists())
        self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))

    def test_newly_supplied_manual_replaces_previous_waiver(self):
        record_path = self.root / ".agents/reference_intake/demo.json"
        review.atomic_write(record_path, json.dumps({"project": "demo", "manual_decision": "waived"}))
        with patch("builtins.input", return_value=""), contextlib.redirect_stdout(io.StringIO()):
            launcher.confirm_references(self.root, "demo")
        self.assertEqual(json.loads(record_path.read_text())["manual_decision"], "provided")
        self.manual.unlink()
        self.launch()
        with self.assertRaises(EOFError):
            self.run_worker(answer=["", EOFError])
        self.assertFalse(self.config().with_name("ready").exists())

    def test_missing_ocr_for_optional_faq_blocks_startup_and_pending_approval(self):
        (self.references / "faqs").mkdir()
        (self.references / "faqs/scan.pdf").write_text("PDF FAQ fixture")
        self.state(status="APPROVED")
        before = review.state_path(self.root).read_bytes()
        self.launch()
        output = io.StringIO()
        with patch.object(refs, "tool_status", return_value=(False, "install OCR tools")):
            with self.assertRaises(EOFError):
                self.run_worker(answer=["", EOFError], output=output)
        self.assertIn("NEEDS INPUT: reference extraction tools", output.getvalue())
        self.assertIn("Install or repair", output.getvalue())
        self.assertFalse(self.config().with_name("ready").exists())
        self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))
        self.assertEqual(review.state_path(self.root).read_bytes(), before)

    def test_fixing_ocr_tools_resumes_startup_without_repeating_manual_waiver(self):
        self.manual.unlink()
        (self.references / "faqs").mkdir()
        (self.references / "faqs/scan.png").write_text("Scanned FAQ fixture")
        self.launch()
        prompts = []
        repaired = False
        def answer(prompt):
            nonlocal repaired
            prompts.append(prompt)
            self.assertFalse(self.config().with_name("ready").exists())
            self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))
            if len(prompts) == 1:
                return "continue without a manual"
            self.assertEqual(len(prompts), 2)
            repaired = True
            return ""
        with patch.object(refs, "tool_status", side_effect=lambda _: (repaired, "OCR tool fixture")):
            self.run_worker(answer=answer)
        self.assertTrue(self.config().with_name("ready").exists())
        self.assertTrue(any(c[0] == "paste-buffer" for c in self.calls()))
        record = json.loads((self.root / ".agents/reference_intake/demo.json").read_text())
        self.assertEqual(record["manual_decision"], "waived")
        self.assertEqual(record["faq_files"], ["projects/demo/docs/game_reference/faqs/scan.png"])

    def test_invalid_or_other_project_reference_record_cannot_waive_manual(self):
        self.manual.unlink()
        self.launch()
        record_path = self.root / ".agents/reference_intake/demo.json"
        for record in ([], {}, {"project": "other", "manual_decision": "waived"},
                       {"project": "demo", "manual_decision": "unknown"}):
            with self.subTest(record=record):
                review.atomic_write(record_path, json.dumps(record))
                with self.assertRaisesRegex(review.UserError, "invalid reference intake record"):
                    self.run_worker()
                self.assertFalse(self.config().with_name("ready").exists())
                self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))

    def test_startup_confirmation_sends_task_and_executes_filtered_watcher(self):
        self.launch()
        result, execute = self.run_worker()
        self.assertEqual(result, 0)
        self.assertTrue(self.config().with_name("ready").exists())
        self.assertTrue(any(c[0] == "paste-buffer" for c in self.calls()))
        argv = execute.call_args.args[1]
        self.assertEqual(argv[argv.index("--project") + 1], "demo")
        self.assertEqual(argv[argv.index("--worker-id") + 1], self.config().parent.name)
        self.assertEqual(execute.call_args.args[2]["AGENT_REVIEW_TMUX_IMPLEMENTER"], "%20")
        ignored = subprocess.run(
            ["git", "-c", "core.excludesFile=/dev/null", "check-ignore", "-q", "--no-index",
             ".agents/reference_intake/demo.json"], cwd=self.root,
        )
        self.assertEqual(ignored.returncode, 0, "reference choice must stay ignored even in an older checkout")

    def test_pending_review_resumes_via_watcher_without_starting_another_pass(self):
        self.state()
        self.launch()
        self.run_worker()
        self.assertTrue(self.config().with_name("ready").exists())
        self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))

    def test_dead_agent_prevents_startup(self):
        self.launch()
        with patch.object(launcher, "tmux", return_value=subprocess.CompletedProcess([], 0, "1\n", "")):
            with self.assertRaisesRegex(review.UserError, "implementer exited"):
                self.run_worker()
        self.assertFalse(self.config().with_name("ready").exists())

    def test_failed_kickoff_does_not_arm_watchers(self):
        self.launch()
        with patch.dict(os.environ, {"TMUX_FAIL_COMMAND": "paste-buffer"}):
            with self.assertRaises(subprocess.CalledProcessError):
                self.run_worker()
        self.assertFalse(self.config().with_name("ready").exists())

    def test_reviewer_reports_dead_or_missing_startup_pane_without_arming(self):
        self.state()
        self.launch()
        before = review.state_path(self.root).read_bytes()
        for result in (subprocess.CompletedProcess([], 0, "1\n", ""),
                       subprocess.CompletedProcess([], 1, "", "pane not found")):
            with self.subTest(returncode=result.returncode), \
                 patch.object(launcher, "tmux", return_value=result) as transport, \
                 patch.object(launcher.time, "sleep", side_effect=AssertionError("reviewer kept waiting after startup died")), \
                 patch.object(launcher.os, "execve") as execute:
                with self.assertRaisesRegex(review.UserError, "startup watcher exited before confirmation completed"):
                    self.run_worker(role="reviewer")
                execute.assert_not_called()
                transport.assert_called_once_with("display-message", "-p", "-t", "%22", "#{pane_dead}", check=False)
                self.assertFalse(self.config().with_name("ready").exists())
                self.assertEqual(review.state_path(self.root).read_bytes(), before)

    def test_reviewer_waits_for_live_startup_then_runs_after_confirmation(self):
        self.launch()
        ready = self.config().with_name("ready")
        with patch.object(launcher.time, "sleep", side_effect=lambda _: ready.touch()) as wait:
            result, execute = self.run_worker(role="reviewer")
        self.assertEqual(result, 0)
        wait.assert_called_once_with(0.5)
        argv = execute.call_args.args[1]
        self.assertEqual(argv[argv.index("--role") + 1], "reviewer")
        self.assertFalse(any(c[0] == "paste-buffer" for c in self.calls()))

    def test_reviewer_handles_confirmation_arriving_during_liveness_check(self):
        self.launch()
        def finished(*args, **kwargs):
            self.config().with_name("ready").touch()
            return subprocess.CompletedProcess([], 0, "1\n", "")
        with patch.object(launcher, "tmux", side_effect=finished), patch.object(launcher.time, "sleep"):
            result, execute = self.run_worker(role="reviewer")
        self.assertEqual(result, 0)
        execute.assert_called_once()

    def test_worker_id_cannot_escape_notification_directory(self):
        args = argparse.Namespace(worker_id="../../escape", project="demo")
        with patch.object(review, "repo_root", return_value=self.root):
            with self.assertRaisesRegex(review.UserError, "worker id"):
                review.command_watch(args)

    def test_project_filter_does_not_deliver_another_projects_prompt(self):
        self.state(project="other")
        args = argparse.Namespace(
            role="reviewer", project="demo", worker_id="launch-1", once=True,
            timeout=None, interval=0, notify=None,
        )
        with patch.object(review, "repo_root", return_value=self.root), \
             patch.object(review, "run_notify") as notify, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(review.command_watch(args), 3)
            notify.assert_not_called()
        self.assertFalse((self.root / ".agents/runs").exists())

    def test_new_workers_receive_pending_turn_once_despite_old_delivery_markers(self):
        state = self.state()
        args = argparse.Namespace(
            role="reviewer", project="demo", worker_id=None, once=True,
            timeout=None, interval=0, notify=None,
        )
        with patch.object(review, "repo_root", return_value=self.root), \
             patch.object(review, "run_notify") as notify, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(review.command_watch(args), 0)
            args.worker_id = "launch-1"
            self.assertEqual(review.command_watch(args), 0)
            self.assertEqual(review.command_watch(args), 3)
            self.assertEqual(notify.call_count, 2)
        self.assertTrue((review.run_dir(self.root, state) / "workers/launch-1-reviewer.seen").exists())


if __name__ == "__main__":
    unittest.main()
