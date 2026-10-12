#!/usr/bin/env python3
"""Protected review artifact publication from writable project drafts."""

import contextlib
import io
import json
import re
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
import agent_review as review
from review_packet_fixture import packet


class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / "checkout with spaces"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.state = {
            "project": "demo", "run_id": "demo-pass-2", "round": 1,
            "status": "READY_FOR_REVIEW", "review_base": "base", "review_head": "head",
        }
        review.write_state(self.root, self.state)
        self.draft = self.root / "projects/demo/tmp/draft.md"
        self.draft.parent.mkdir(parents=True)
        self.draft.write_text("Verdict: APPROVED\n\n## Learning Candidates\n_None._\n")
        self.destination = self.root / ".agents/runs/demo-pass-2/review-01.md"

    def command(self, *args, expected=0):
        result = subprocess.run([*review.script_argv(self.root), *args], cwd=Path(self.temp.name),
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def publish(self, kind="review", source=None, expected=0):
        return self.command("import-artifact", "--kind", kind, "--source", str(source or self.draft), expected=expected)

    def test_external_tool_anchors_checkout_and_publishes_without_changing_state(self):
        before = (self.root / ".agents/current.json").read_bytes()
        self.publish()
        self.assertEqual(self.destination.read_bytes(), self.draft.read_bytes())
        self.assertEqual((self.root / ".agents/current.json").read_bytes(), before)
        self.publish()
        self.draft.write_text("Corrected review before verdict.\n")
        self.publish()
        self.assertEqual(self.destination.read_text(), "Corrected review before verdict.\n")

    def test_wrong_turn_cannot_replace_a_published_review(self):
        self.publish()
        original = self.destination.read_bytes()
        for status in ("APPROVED", "CHANGES_REQUESTED", "IMPLEMENTING", "REVIEW_ROUNDS_EXHAUSTED"):
            self.state["status"] = status
            review.write_state(self.root, self.state)
            self.publish(expected=2)
            self.assertEqual(self.destination.read_bytes(), original)

    def test_responses_are_scoped_to_changes_requested_and_current_round(self):
        self.publish(kind="response", expected=2)
        self.state.update(status="CHANGES_REQUESTED", round=2)
        review.write_state(self.root, self.state)
        self.publish(kind="response")
        self.assertEqual(self.destination.with_name("response-02.md").read_bytes(), self.draft.read_bytes())
        self.assertFalse(self.destination.exists())

    def test_empty_non_markdown_and_outside_sources_are_refused(self):
        outside = self.root / "outside.md"
        outside.write_text("outside")
        for source in (outside, self.draft.with_suffix(".txt"), Path(self.temp.name) / "outside.md"):
            source.write_text("text")
            self.publish(source=source, expected=2)
        self.draft.write_text(" \n")
        self.publish(expected=2)
        self.assertFalse(self.destination.exists())

    def test_symlink_source_escape_and_destination_escape_are_refused(self):
        outside = Path(self.temp.name) / "outside.md"
        outside.write_text("unrelated file")
        self.draft.unlink()
        self.draft.symlink_to(outside)
        self.publish(expected=2)
        self.draft.unlink()
        self.draft.write_text("draft")
        self.destination.parent.mkdir(parents=True)
        self.destination.symlink_to(outside)
        self.publish(expected=2)
        self.assertEqual(outside.read_text(), "unrelated file")

    def test_repo_option_rejects_a_subdirectory(self):
        result = subprocess.run([sys.executable, str(REPO / "scripts/agent_review.py"),
                                 "--repo", str(self.draft.parent), "status"], text=True, capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("checkout root", result.stderr)

    def test_prompts_publish_drafts_before_verdict_and_use_the_same_command_prefix(self):
        prompt = review.render_prompt(self.root, self.state, "reviewer")
        command = review.script_command(self.root)
        self.assertIn(f"{command} import-artifact --kind review", prompt)
        self.assertLess(prompt.index("import-artifact"), prompt.index("approve --review"))
        self.assertIn("projects/demo/tmp/", prompt)
        self.assertIn("without\nshell redirection", prompt)
        self.state["status"] = "CHANGES_REQUESTED"
        prompt = review.render_prompt(self.root, self.state, "implementer")
        self.assertIn(f"{command} import-artifact --kind response", prompt)
        self.assertIn(f"{command} reready", prompt)


class CheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / "checkout with spaces"
        self.root.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.source = self.root / "projects/demo/source.asm"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("Entry:\n  RTS\n")
        self.git("add", ".")
        self.git("commit", "-qm", "Initial fixture")
        self.base = self.git("rev-parse", "HEAD").strip()
        self.source.write_text("RunDemo:\n  RTS\n")
        self.git("commit", "-qam", "Pass fixture")
        self.head = self.git("rev-parse", "HEAD").strip()
        self.command("init", "--project", "demo", "--base", self.base, "--head", self.head,
                     "--run-id", "demo-pass-1")
        self.run = self.root / ".agents/runs/demo-pass-1"
        self.note = self.run / "implementation.md"
        self.note.write_text("Implemented pass 1. Operator instruction: stop after pass 1.\n")
        self.packet = self.run / "packet.md"
        self.packet.write_text(packet(self.head))
        self.command("ready", "--note", str(self.note), "--packet", str(self.packet))

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def command(self, *args, expected=0):
        result = subprocess.run([*review.script_argv(self.root), *args], cwd=self.root,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def current(self):
        return json.loads(review.state_path(self.root).read_text())

    def publish_checkpoint_from_prompt(self):
        state = self.current()
        prompt = (self.root / state["prompts"]["reviewer"]).read_text()
        self.assertIn("## Unfinished review", prompt)
        unfinished = prompt.split("## Unfinished review\n", 1)[1].split("## Completed review\n", 1)[0]
        self.assertNotIn("Verdict:", unfinished)
        self.assertNotIn("Gold assessment: APPROVED", unfinished)
        self.assertIn("without a\nverdict or gold approval marker", unfinished)
        self.assertIn("unchecked work, next steps", unfinished)
        self.assertIn("A usage-limit warning alone decides neither verdict.", unfinished)
        self.assertIn("Packet admission does not establish semantic correctness or review completeness.", prompt)
        self.assertIn(f"Leave `{state['status']}` pending with reviewer ownership", unfinished)
        blocks = re.findall(r"```sh\n(.*?)\n```", unfinished, re.DOTALL)
        self.assertEqual(len(blocks), 1)
        argv = shlex.split(blocks[0])
        self.assertEqual(argv[:-2], [*review.script_argv(self.root), "import-artifact", "--kind", "review"])
        self.assertEqual(argv[-2], "--source")
        self.draft = self.root / argv[-1]
        self.draft.parent.mkdir(parents=True, exist_ok=True)
        self.draft.write_text(
            f"Review checkpoint at {self.head}.\nInspected: admitted packet.\n"
            "Unchecked: consumer boundary. Next: inspect its caller.\n"
            "Operator instruction: stop after pass 1.\n"
        )
        before = review.state_path(self.root).read_bytes()
        result = subprocess.run(argv, cwd=self.root, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.saved = self.run / f"review-{state['round']:02d}.md"
        self.assertEqual(self.saved.read_bytes(), self.draft.read_bytes())
        self.assertEqual(review.state_path(self.root).read_bytes(), before)
        return prompt

    def reready(self):
        self.draft.write_text("Verdict: CHANGES_REQUESTED\n\nF1: correct the boundary.\n")
        self.command("import-artifact", "--kind", "review", "--source", str(self.draft))
        self.command("request-changes", "--review", str(self.saved))
        self.source.write_text("RunDemo:\n  NOP\n  RTS\n")
        self.git("commit", "-qam", "Fix fixture")
        self.head = self.git("rev-parse", "HEAD").strip()
        self.packet.write_text(packet(self.head))
        response = self.run / "response-01.md"
        response.write_text("F1 fixed. Operator instruction: stop after pass 1.\n")
        self.command("reready", "--response", str(response), "--head", self.head, "--packet", str(self.packet))

    def test_generated_checkpoint_command_keeps_both_review_states_pending(self):
        for round_number in (1, 2):
            with self.subTest(round=round_number):
                prompt = self.publish_checkpoint_from_prompt()
                self.assertIn("read any\nexisting draft", prompt)
                self.assertIn("imported checkpoint", prompt)
                before = review.state_path(self.root).read_bytes()
                for verb, verdict in (("approve", "APPROVED"), ("request-changes", "CHANGES_REQUESTED")):
                    result = self.command(verb, "--review", str(self.saved), expected=2)
                    self.assertIn(f"review file must contain 'Verdict: {verdict}'", result.stderr)
                result = self.command("archive", "--pass-id", "1", expected=2)
                self.assertIn("archive requires APPROVED", result.stderr)
                result = self.command("watch", "--role", "implementer", "--once", expected=3)
                self.assertIn("current actor is reviewer", result.stdout)
                self.assertEqual(review.state_path(self.root).read_bytes(), before)
                if round_number == 1:
                    self.reready()

    def test_completed_review_archives_disclosures_and_authored_limit(self):
        prompt = self.publish_checkpoint_from_prompt()
        for guidance in ("checks skipped with reasons in the submitted review, not only chat",
                         "missing, stale, contradictory or insufficient",
                         "specifically required by the review route or user"):
            self.assertIn(guidance, " ".join(prompt.split()))
        self.assertIn("exactly one of approve or request-changes", prompt)
        text = (
            f"Verdict: APPROVED\n\nReviewed head: {self.head}\n"
            "Inspected: source and consumer boundary. Required work remaining: none.\n"
            "Supplied evidence: successful packet gates at this head.\n"
            "Not rerun: duplicate scratch build; the packet covers parity.\n"
            "Operator instruction: stop after pass 1.\n"
        )
        self.draft.write_text(text)
        self.command("import-artifact", "--kind", "review", "--source", str(self.draft))
        self.command("approve", "--review", str(self.saved))
        approved_prompt = (self.root / self.current()["prompts"]["implementer"]).read_text()
        self.assertIn("stop if that limit is reached", approved_prompt)
        self.assertIn("No command enforces a pass count", approved_prompt)
        self.assertIn("dated amendments in existing review/evidence artifacts", " ".join(approved_prompt.split()))
        self.command("archive", "--pass-id", "1")
        archive = self.root / "projects/demo/docs/reverse_engineering/reviews/pass-1.md"
        self.assertIn(text, archive.read_text())
        self.command("import-artifact", "--kind", "review", "--source", str(self.draft), expected=2)
        self.assertEqual(self.saved.read_text(), text)

    def test_restart_delivers_frozen_prompt_and_preserves_checkpoint(self):
        for round_number in (1, 2):
            with self.subTest(round=round_number):
                self.publish_checkpoint_from_prompt()
                original = self.root / self.current()["prompts"]["reviewer"]
                legacy = "Saved pre-clarification prompt.\nOperator instruction: stop after pass 1.\n"
                original.write_text(legacy)
                state_before = review.state_path(self.root).read_bytes()
                checkpoint_before = self.saved.read_bytes()
                with patch.object(review, "repo_root", return_value=self.root), \
                     patch.object(review, "render_prompt", side_effect=AssertionError("must not regenerate frozen prompt")), \
                     patch.object(review, "run_notify") as notify, contextlib.redirect_stdout(io.StringIO()):
                    for worker in ("original-session", "restarted-session"):
                        args = review.build_parser().parse_args([
                            "watch", "--role", "reviewer", "--worker-id", worker, "--once",
                        ])
                        self.assertEqual(review.command_watch(args), 0)
                        self.assertEqual(review.command_watch(args), 3)
                    self.assertEqual(notify.call_count, 2)
                    for call in notify.call_args_list:
                        self.assertEqual((self.root / call.args[-1]).read_text(), legacy)
                self.assertEqual(original.read_text(), legacy)
                self.assertEqual(self.saved.read_bytes(), checkpoint_before)
                self.assertEqual(review.state_path(self.root).read_bytes(), state_before)
                if round_number == 1:
                    self.reready()


if __name__ == "__main__":
    unittest.main()
