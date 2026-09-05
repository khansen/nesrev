import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import intake_baseline as baseline


HEADER = "| pass_id | focus | labels_remaining | verify | docs_check | rework_items | notes |\n|---|---|---|---|---|---|---|\n"
FRESH = baseline.PENDING + "\n\n" + HEADER + "| 0 | Intake baseline | | | | | |\n"
HISTORY = HEADER + "| 0 | Initial snapshot | 80 / 100 | pass | pass | 0 | Original measurement |\n| 1 | First corridor | 50 / 70 | pass | pass | 0 | Existing history |\n"
LEGACY = HEADER + "| 1 | First corridor | 50 / 70 | pass | pass | 0 | Existing history |\n"


class IntakeTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix="intake-history-")
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.scorecard = self.root / "PROGRESS_SCORECARD.md"
        self.receipt = self.root / "inventory/intake_history.json"
        self.snapshot = self.root / "inventory/intake_snapshot.json"
        self.source, self.reference = self.root / "Demo.asm", self.root / "demo.nes"
        self.source.write_text("L1000:\n RTS\n")
        self.reference.write_bytes(b"synthetic reference")
        self.metrics = {"labels_remaining": "1 / 1", "raw_rom_calls_remaining": "0",
                        "raw_indirect_operands_remaining": "0", "hardcoded_counter_sites_remaining": "0"}

    def state(self):
        return baseline.preflight(self.scorecard, self.receipt)

    def publish(self, expected=None):
        return baseline.publish(self.scorecard, self.receipt, self.snapshot, expected or self.state(),
                                self.metrics, self.source, self.reference)

    def test_fresh_capture_happens_once_and_rerun_is_idempotent(self):
        self.scorecard.write_text(FRESH)
        self.assertEqual(self.publish(), "capture-scaffold")
        saved, snapshot = self.scorecard.read_bytes(), self.snapshot.read_bytes()
        self.assertNotIn(baseline.PENDING.encode(), saved)
        self.assertIn(b"1 / 1 | pass (intake-relaxed) | pass | 0", saved)
        self.assertEqual(self.publish(), "preserve-history")
        self.assertEqual(saved, self.scorecard.read_bytes())
        self.assertEqual(snapshot, self.snapshot.read_bytes())

    def test_changed_current_measurements_never_replace_original_baseline(self):
        self.scorecard.write_text(HISTORY)
        saved = self.scorecard.read_bytes()
        self.publish()
        self.source.write_text("RunDemo:\n RTS\n")
        self.metrics["labels_remaining"] = "0 / 0"
        self.publish()
        self.assertEqual(saved, self.scorecard.read_bytes())
        snapshot = json.loads(self.snapshot.read_text())
        self.assertEqual(snapshot["metrics"]["labels_remaining"], "0 / 0")
        self.assertEqual(snapshot["source_sha256"], baseline.digest(self.source.read_bytes()))
        self.assertEqual(snapshot["gates"]["project-verify"], {"exit_status": 0, "mode": "intake-relaxed"})

    def test_existing_incomplete_baseline_is_not_filled_from_today(self):
        self.scorecard.write_text(FRESH.replace(baseline.PENDING, ""))
        saved = self.scorecard.read_bytes()
        self.publish()
        self.assertEqual(saved, self.scorecard.read_bytes())

    def test_legacy_missing_baseline_requires_explicit_migration(self):
        self.scorecard.write_text(LEGACY)
        with self.assertRaisesRegex(ValueError, "project-intake-migrate"):
            self.state()
        self.assertFalse(self.receipt.exists())
        self.assertFalse(self.snapshot.exists())

    def test_legacy_migration_is_idempotent_and_never_invents_pass_zero(self):
        self.scorecard.write_text(LEGACY)
        saved = self.scorecard.read_bytes()
        self.assertTrue(baseline.migrate(self.scorecard, self.receipt))
        receipt = self.receipt.read_bytes()
        self.assertFalse(baseline.migrate(self.scorecard, self.receipt))
        self.assertEqual(receipt, self.receipt.read_bytes())
        self.publish()
        self.assertEqual(saved, self.scorecard.read_bytes())
        self.assertIn(b"not recorded; not reconstructed", receipt)
        self.assertNotIn(b"metrics", receipt)

    def test_legacy_migration_does_not_require_source_or_fixtures(self):
        self.scorecard.write_text(LEGACY)
        self.source.unlink()
        self.reference.unlink()
        baseline.migrate(self.scorecard, self.receipt)
        self.assertEqual(self.state()["mode"], "preserve-history")

    def test_migration_does_not_apply_to_fresh_or_existing_baseline(self):
        for text in (FRESH, HISTORY):
            self.scorecard.write_text(text)
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "only to scorecards without pass zero"):
                baseline.migrate(self.scorecard, self.receipt)

    def test_invalid_receipt_is_not_silently_repaired(self):
        self.scorecard.write_text(LEGACY)
        self.receipt.parent.mkdir()
        self.receipt.write_text('{"schema_version": true}')
        with self.assertRaisesRegex(ValueError, "invalid legacy"):
            self.state()
        with self.assertRaisesRegex(ValueError, "invalid legacy"):
            baseline.migrate(self.scorecard, self.receipt)

    def test_pending_marker_cannot_overwrite_human_values(self):
        self.scorecard.write_text(FRESH.replace("| | | | | |", "| 99 / 99 | pass | pass | 0 | old |"))
        with self.assertRaisesRegex(ValueError, "historical values"):
            self.state()

    def test_pending_marker_cannot_capture_after_semantic_pass(self):
        self.scorecard.write_text(baseline.PENDING + "\n" + HISTORY)
        with self.assertRaisesRegex(ValueError, "sole scaffold"):
            self.state()

    def test_duplicate_or_out_of_order_passes_are_refused(self):
        for text in (HISTORY + "| 1 | Duplicate | 0 | pass | pass | 0 | old |\n",
                     HISTORY.replace("| 0 |", "| 2 |")):
            self.scorecard.write_text(text)
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "unique increasing"):
                self.state()

    def test_malformed_scorecard_is_refused_before_measurements(self):
        for text in ("missing table", HEADER, HISTORY.replace("Original measurement", "raw | pipe"),
                     HISTORY.replace("| notes |", "| verify |")):
            self.scorecard.write_text(text)
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.state()

    def test_fenced_examples_do_not_create_baselines_or_duplicate_rows(self):
        self.scorecard.write_text("```markdown\n" + FRESH + "```\n" + LEGACY)
        with self.assertRaisesRegex(ValueError, "legacy scorecard has no pass 0"):
            self.state()
        baseline.migrate(self.scorecard, self.receipt)
        self.assertEqual(self.state()["mode"], "preserve-history")

    def test_fresh_capture_removes_only_the_structural_pending_marker(self):
        example = "```markdown\n" + FRESH + "```\n"
        self.scorecard.write_text(FRESH + "\n" + example)
        self.publish()
        self.assertIn(example, self.scorecard.read_text())
        self.assertEqual(baseline.pending_count(self.scorecard.read_text()), 0)

    def test_repeated_identical_headers_preserve_chunked_history(self):
        text = HISTORY.replace("| 1 |", HEADER + "| 1 |")
        self.scorecard.write_text(text)
        self.publish()
        self.assertEqual(self.scorecard.read_text(), text)

    def test_retrospective_row_does_not_become_an_original_pass_zero(self):
        text = LEGACY + "| retro-0 | Backfilled baseline | 0 | pass | pass | 0 | Retrospective measurement |\n"
        self.scorecard.write_text(text)
        with self.assertRaisesRegex(ValueError, "legacy scorecard has no pass 0"):
            self.state()
        baseline.migrate(self.scorecard, self.receipt)
        self.publish()
        self.assertEqual(self.scorecard.read_text(), text)

    def test_changed_scorecard_after_preflight_prevents_publication(self):
        self.scorecard.write_text(FRESH)
        expected = self.state()
        self.scorecard.write_text(HISTORY)
        with self.assertRaisesRegex(ValueError, "changed after intake preflight"):
            self.publish(expected)
        self.assertFalse(self.snapshot.exists())

    def test_snapshot_failure_leaves_fresh_baseline_unmodified(self):
        self.scorecard.write_text(FRESH)
        with patch.object(baseline, "atomic_bytes", side_effect=OSError("snapshot disk failure")):
            with self.assertRaisesRegex(OSError, "disk failure"):
                self.publish()
        self.assertEqual(self.scorecard.read_text(), FRESH)

    def test_baseline_failure_restores_previous_snapshot_or_absence(self):
        real_write = baseline.atomic_bytes
        def fail_scorecard(path, value):
            if path == self.scorecard:
                raise OSError("scorecard disk failure")
            real_write(path, value)
        for previous in (None, b"previous snapshot\n"):
            self.scorecard.write_text(FRESH)
            if previous is not None:
                real_write(self.snapshot, previous)
            with patch.object(baseline, "atomic_bytes", side_effect=fail_scorecard):
                with self.assertRaisesRegex(OSError, "scorecard disk failure"):
                    self.publish()
            self.assertEqual(self.scorecard.read_text(), FRESH)
            self.assertEqual(self.snapshot.read_bytes() if self.snapshot.exists() else None, previous)


if __name__ == "__main__":
    unittest.main()
