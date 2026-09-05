"""Synthetic receipt migration, pruning, and ingestion regression fixtures."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import agent_review
import process_friction as friction


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="friction-fixture-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / "projects/demo").mkdir(parents=True)
        (self.root / "PLAN.md").write_text("# Accepted work\n")
        self.queue, self.receipts = friction.project_paths(self.root, "demo")
        self.a = "- Validate the selected manifest members."
        self.b = "- Include shared paths in the review bundle."
        self.c = "- Preserve immutable intake measurements."
        self.state = {"project": "demo", "run_id": "demo-first", "review_head": "a" * 40}
        self.archive = "projects/demo/docs/reverse_engineering/reviews/pass-1.md"

    def write_queue(self, body=None):
        body = body if body is not None else self.a + "\n" + self.b
        block = agent_review.render_learning_block(
            self.state, "1", self.archive,
            [(f".agents/runs/{self.state['run_id']}/implementation.md", body)],
        )
        self.queue.write_text("# Process Friction\n\n" + friction.BOILERPLATE[0] + "\n\n## Agent Review Learning Candidates\n\n" + friction.BOILERPLATE[1] + "\n\n" + block)

    def decision(self, content, **changes):
        return {"id": friction.candidate_id(content), "disposition": "accepted", "destinations": ["PLAN.md"], "rationale": "Accepted into the named implementation plan.", **changes}

    def ingest(self, body, *, run="demo-first", head="a" * 40):
        note = self.root / ".agents/runs" / run / "implementation.md"
        note.parent.mkdir(parents=True, exist_ok=True)
        note.write_text("## Learning Candidates\n\n" + body + "\n")
        state = {**self.state, "run_id": run, "review_head": head, "implementation_note": str(note.relative_to(self.root))}
        return agent_review.update_process_friction(self.root, state, "1", self.archive)

    def candidates(self):
        return friction.queue_candidates(self.queue.read_text(), "projects/demo/PROCESS_FRICTION.md") if self.queue.exists() else {}

    def test_backfill_precedes_pruning_and_preserves_unique_note_content(self):
        self.write_queue()
        before = self.queue.read_text()
        friction.triage(self.root, "demo", [self.decision(self.a)])
        self.assertEqual(self.queue.read_text(), before)
        saved = friction.read_receipts(self.root, "demo")[friction.candidate_id(self.a)]
        self.assertEqual(saved["content"], self.a)
        self.assertEqual(saved["sources"], [".agents/runs/demo-first/implementation.md"])
        self.assertEqual(friction.prune(self.root, "demo"), 1)
        self.assertEqual(set(self.candidates()), {friction.candidate_id(self.b)})

    def test_deleted_queue_stays_absent_after_rearchive(self):
        self.write_queue()
        friction.triage(self.root, "demo", [self.decision(self.a), self.decision(self.b)], True)
        self.assertFalse(self.queue.exists())
        self.assertIsNone(self.ingest(self.a + "\n" + self.b))
        self.assertFalse(self.queue.exists())

    def test_rebased_sha_and_new_run_do_not_reopen_triaged_candidates(self):
        self.write_queue()
        friction.triage(self.root, "demo", [self.decision(self.a), self.decision(self.b)], True)
        self.ingest(self.a + "\n" + self.b, run="demo-new-run", head="b" * 40)
        self.assertFalse(self.queue.exists())
        self.ingest(self.a + "\n" + self.b + "\n" + self.c, run="demo-next-run", head="c" * 40)
        self.assertEqual(set(self.candidates()), {friction.candidate_id(self.c)})

    def test_partial_block_and_new_candidate_do_not_reopen_a(self):
        self.write_queue()
        friction.triage(self.root, "demo", [self.decision(self.a)], True)
        self.ingest(self.a + "\n" + self.b + "\n" + self.c)
        self.assertEqual(set(self.candidates()), {friction.candidate_id(self.b), friction.candidate_id(self.c)})
        self.assertNotIn(self.a, self.queue.read_text())

    def test_receipt_persistence_failure_never_prunes(self):
        self.write_queue()
        before = self.queue.read_text()
        with patch.object(friction.os, "replace", side_effect=OSError("simulated receipt persistence failure")):
            with self.assertRaisesRegex(OSError, "persistence failure"):
                friction.triage(self.root, "demo", [self.decision(self.a)], True)
        self.assertEqual(self.queue.read_text(), before)
        self.assertFalse(self.receipts.exists())
        self.assertEqual(list(self.receipts.parent.glob(".process_friction_receipts.json.*")), [])
        friction.triage(self.root, "demo", [self.decision(self.a)], True)
        self.assertEqual(set(self.candidates()), {friction.candidate_id(self.b)})

    def test_queue_write_failure_leaves_saved_receipt_for_retry(self):
        self.write_queue()
        before = self.queue.read_text()
        original_write = friction.atomic_write

        def fail_queue(path, text):
            if path == self.queue:
                raise OSError("simulated queue write failure")
            return original_write(path, text)

        with patch.object(friction, "atomic_write", side_effect=fail_queue):
            with self.assertRaisesRegex(OSError, "queue write failure"):
                friction.triage(self.root, "demo", [self.decision(self.a)], True)
        self.assertEqual(self.queue.read_text(), before)
        self.assertIn(friction.candidate_id(self.a), friction.read_receipts(self.root, "demo"))
        friction.prune(self.root, "demo")
        self.assertEqual(set(self.candidates()), {friction.candidate_id(self.b)})

    def test_missing_receipts_refuse_pruning(self):
        self.write_queue()
        before = self.queue.read_text()
        with self.assertRaisesRegex(friction.FrictionError, "backfill"):
            friction.prune(self.root, "demo")
        self.assertEqual(self.queue.read_text(), before)

    def test_invalid_or_incomplete_decisions_do_not_partially_persist(self):
        invalid = [
            {"id": "unknown"}, self.decision(self.b, disposition="pending"),
            self.decision(self.b, destinations=[]), self.decision(self.b, rationale=""),
            self.decision(self.b, destinations=["missing.md"]), self.decision(self.b, destinations=["../outside.md"]),
        ]
        for decision in invalid:
            with self.subTest(decision=decision):
                self.write_queue()
                before = self.queue.read_text()
                with self.assertRaises(friction.FrictionError):
                    friction.triage(self.root, "demo", [self.decision(self.a), decision], True)
                self.assertFalse(self.receipts.exists())
                self.assertEqual(self.queue.read_text(), before)

    def test_manual_queue_and_implementation_note_have_durable_receipts(self):
        self.write_queue()
        manual = "- A manual observation that exists nowhere else."
        self.queue.write_text(self.queue.read_text() + "\n" + manual + "\n")
        friction.triage(self.root, "demo", [self.decision(manual, disposition="discarded", destinations=[], rationale="One-off observation; no reusable defect.")], True)
        saved = friction.read_receipts(self.root, "demo")[friction.candidate_id(manual)]
        self.assertEqual(saved["content"], manual)
        self.assertEqual(saved["sources"], ["projects/demo/PROCESS_FRICTION.md"])
        self.assertNotIn(manual, self.queue.read_text())

    def test_corrupt_receipts_refuse_ingestion_and_pruning(self):
        self.write_queue()
        before = self.queue.read_text()
        self.receipts.parent.mkdir(parents=True)
        self.receipts.write_text("{broken")
        with self.assertRaises(friction.FrictionError):
            friction.prune(self.root, "demo")
        with self.assertRaises(agent_review.UserError):
            self.ingest(self.a)
        self.assertEqual(self.queue.read_text(), before)

    def test_receipt_identity_is_verified(self):
        self.write_queue()
        friction.triage(self.root, "demo", [self.decision(self.a)])
        data = json.loads(self.receipts.read_text())
        data["receipts"][0]["content"] = self.b
        self.receipts.write_text(json.dumps(data))
        with self.assertRaisesRegex(friction.FrictionError, "does not match"):
            friction.read_receipts(self.root, "demo")

    def test_malformed_legacy_marker_is_not_pruned(self):
        self.write_queue()
        self.queue.write_text(self.queue.read_text().replace(":end -->", ":wrong -->"))
        before = self.queue.read_text()
        with self.assertRaisesRegex(friction.FrictionError, "unmatched learning marker"):
            friction.triage(self.root, "demo", [self.decision(self.a)], True)
        self.assertEqual(self.queue.read_text(), before)

    def test_nested_lists_and_fences_remain_with_their_candidate(self):
        body = "- Candidate with details.\n  - Nested evidence.\n\n```text\n- Not another candidate.\n### Not another heading\n```\n"
        chunks = [chunk for chunk in friction.candidate_chunks(body + self.b) if not friction.empty_candidate(chunk)]
        self.assertEqual(len(chunks), 2)
        self.assertEqual(friction.normalized(chunks[0]), friction.normalized(body))

    def test_empty_sections_do_not_create_queue_work(self):
        for text in ("", "_None._", "- _None._", "### Details\n\n_None._", "No actionable learning candidates."):
            with self.subTest(text=text):
                self.assertIsNone(self.ingest(text))
                self.assertFalse(self.queue.exists())

    def test_heading_only_observation_is_not_silently_lost(self):
        self.ingest("### Investigate missing packet terminators")
        self.assertEqual(len(self.candidates()), 1)

    def test_same_text_in_multiple_sources_has_one_identity(self):
        self.write_queue(self.a)
        second = agent_review.render_learning_block({**self.state, "run_id": "second"}, "2", self.archive, [("review-01.md", self.a)])
        self.queue.write_text(self.queue.read_text() + "\n" + second)
        self.assertEqual(len(self.candidates()), 1)
        friction.triage(self.root, "demo", [self.decision(self.a)], True)
        self.assertFalse(self.queue.exists())
        self.assertEqual(len(friction.read_receipts(self.root, "demo")[friction.candidate_id(self.a)]["sources"]), 2)

    def test_project_and_symlink_boundaries(self):
        with self.assertRaises(friction.FrictionError):
            friction.project_paths(self.root, "../demo")
        outside = self.root / "outside.md"
        outside.write_text("Do not overwrite me.")
        self.queue.symlink_to(outside)
        with self.assertRaises(friction.FrictionError):
            friction.project_paths(self.root, "demo")
        self.assertEqual(outside.read_text(), "Do not overwrite me.")

    def test_cli_backfill_and_prune_are_separate_from_handoff_state(self):
        self.write_queue()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        script = Path(friction.__file__).resolve()
        command = [sys.executable, str(script)]
        listed = subprocess.run(command + ["list", "--project", "demo"], cwd=self.root, text=True, capture_output=True, check=True)
        self.assertEqual(len(json.loads(listed.stdout)), 2)
        decisions = self.root / "decisions.json"
        decisions.write_text(json.dumps([self.decision(self.a), self.decision(self.b)]))
        subprocess.run(command + ["triage", "--project", "demo", "--decisions", str(decisions)], cwd=self.root, capture_output=True, check=True)
        self.assertTrue(self.queue.exists())
        subprocess.run(command + ["prune", "--project", "demo"], cwd=self.root, capture_output=True, check=True)
        self.assertFalse(self.queue.exists())
        self.assertFalse((self.root / ".agents/current.json").exists())


if __name__ == "__main__":
    unittest.main()
