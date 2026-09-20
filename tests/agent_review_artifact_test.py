#!/usr/bin/env python3
"""Protected review artifact publication from writable project drafts."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
import agent_review as review


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


if __name__ == "__main__":
    unittest.main()
