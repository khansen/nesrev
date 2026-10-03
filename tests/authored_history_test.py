import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from authored_history import AuthoredHistory, document_symbols
from process_friction import candidate_id


HEADER = "| pass_id | focus | verify | docs_check | rework_items | notes |\n|---|---|---|---|---|---|\n"
OLD = "| 1 | Named OldEntry | pass | pass | 0 | Introduced `OldEntry`. |\n"
CURRENT = "| 2 | Rename | pending | pending | pending | Uses `NewEntry`. |\n"


class AuthoredHistoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.docs = self.root / "projects/demo/docs/reverse_engineering"
        (self.docs / "inventory").mkdir(parents=True)
        self.scorecard = self.docs / "PROGRESS_SCORECARD.md"
        self.scorecard.write_text(HEADER + OLD + CURRENT)
        self.receipts = self.docs / "inventory/process_friction_receipts.json"

    def history(self, pass_id=None):
        return AuthoredHistory(self.scorecard, pass_id, root=self.root, project="demo")

    def receipt_data(self):
        content = "Historical `OldEntry` blocked a rename."
        return {"schema_version": 1, "project": "demo", "receipts": [{
            "id": candidate_id(content), "content": content,
            "disposition": "discarded", "sources": ["reviews/pass-1.md"],
            "destinations": [], "rationale": "Preserved observation.",
        }]}

    def test_historical_rows_omitted_but_current_and_surrounding_prose_keep_coordinates(self):
        self.scorecard.write_text("# Progress\n\n" + HEADER + OLD + CURRENT + "\nLive `StaleEntry`.\n")
        original = self.scorecard.read_bytes()
        history = self.history()
        self.assertEqual(history.pass_id, 2)
        self.assertEqual(document_symbols(history, [self.scorecard]), ["NewEntry", "StaleEntry"])
        self.assertIn((8, "Live `StaleEntry`."), history.lines(self.scorecard))
        self.assertEqual(self.scorecard.read_bytes(), original)

    def test_older_recheck_keeps_selected_and_later_rows_current(self):
        history = self.history(1)
        self.assertEqual(document_symbols(history, [self.scorecard]), ["NewEntry", "OldEntry"])
        with self.assertRaisesRegex(ValueError, "pass 9 not found"):
            self.history(9)

    def test_closed_latest_row_is_still_current(self):
        self.scorecard.write_text(HEADER + OLD + CURRENT.replace("pending", "pass"))
        self.assertEqual(document_symbols(self.history(), [self.scorecard]), ["NewEntry"])
        self.scorecard.write_text(HEADER + OLD + CURRENT.replace("NewEntry", "OldEntry"))
        self.assertEqual(document_symbols(self.history(), [self.scorecard]), ["OldEntry"])

    def test_only_canonical_valid_receipts_are_omitted_without_rewriting(self):
        self.receipts.write_text(json.dumps(self.receipt_data(), indent=4) + "\n")
        original = self.receipts.read_bytes()
        history = self.history()
        self.assertEqual(history.lines(self.receipts), [])
        duplicate = self.docs / "process_friction_receipts.json"
        duplicate.write_bytes(original)
        self.assertIn("OldEntry", document_symbols(history, [duplicate]))
        self.assertEqual(self.receipts.read_bytes(), original)

    def test_invalid_receipts_never_get_exempted(self):
        for field, value in (("schema_version", 2), ("project", "another"), ("receipts", {})):
            with self.subTest(field=field):
                data = self.receipt_data()
                data[field] = value
                self.receipts.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError, "receipts"):
                    self.history()
        data = self.receipt_data()
        data["receipts"][0]["content"] += " edited"
        self.receipts.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "id does not match"):
            self.history()
        self.receipts.write_text("{")
        with self.assertRaisesRegex(ValueError, "cannot read receipts"):
            self.history()

    def test_duplicate_receipts_refused(self):
        data = self.receipt_data()
        data["receipts"].append(copy.deepcopy(data["receipts"][0]))
        self.receipts.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "duplicate receipt"):
            self.history()

    def test_invalid_scorecard_cannot_hide_old_references(self):
        variants = {
            "duplicate pass_id": HEADER + OLD + OLD + CURRENT,
            "out of order": HEADER + CURRENT.replace("pending", "pass") + OLD,
            "non-latest pass": HEADER + OLD.replace("| pass |", "| pending |", 1) + CURRENT,
            "raw.*not allowed": HEADER + OLD.replace("Named OldEntry", "Named | OldEntry") + CURRENT,
            "conflicting scorecard header": HEADER + OLD + HEADER.replace("focus", "topic") + CURRENT,
            "invalid scorecard header": HEADER.replace("verify", "focus") + OLD + CURRENT,
            "no scorecard pass rows": HEADER,
        }
        for diagnostic, text in variants.items():
            with self.subTest(diagnostic=diagnostic):
                self.scorecard.write_text(text)
                with self.assertRaisesRegex(ValueError, diagnostic):
                    self.history()

    def test_missing_scorecard_refused(self):
        self.scorecard.unlink()
        with self.assertRaises(OSError):
            self.history()

    def test_nonnumeric_legacy_rows_remain_checked_text(self):
        for value in ("retro-0", "false", "-1"):
            self.scorecard.write_text(HEADER + OLD.replace("| 1 |", f"| {value} |") + CURRENT)
            self.assertIn("OldEntry", document_symbols(self.history(), [self.scorecard]))

    def test_fenced_rows_do_not_acquire_historical_status(self):
        self.scorecard.write_text(HEADER + OLD + CURRENT + "\n```md\n" + HEADER + OLD + "```\n")
        self.assertIn("OldEntry", document_symbols(self.history(), [self.scorecard]))

    def test_current_files_and_lookalike_scorecards_are_not_filtered(self):
        for relative in ("MEMORY_MAP.md", "inventory/active.json", "inventory/PROGRESS_SCORECARD.md"):
            path = self.docs / relative
            path.write_text(HEADER + OLD + CURRENT)
            self.assertIn("OldEntry", document_symbols(self.history(), [path]))

    def test_header_order_and_extra_columns_preserved(self):
        self.scorecard.write_text(
            "| notes | docs_check | pass_id | rework_items | extra | verify |\n"
            "|---|---|---|---|---|---|\n"
            "| `OldEntry` | pass | 1 | 0 | keep | pass |\n"
            "| `NewEntry` | pending | 2 | pending | keep | pending |\n")
        original = self.scorecard.read_bytes()
        self.assertEqual(document_symbols(self.history(), [self.scorecard]), ["NewEntry"])
        self.assertEqual(self.scorecard.read_bytes(), original)

    def test_identical_header_can_continue_the_same_pass_log(self):
        self.scorecard.write_text(HEADER + OLD + "\n" + HEADER + CURRENT)
        self.assertEqual(document_symbols(self.history(), [self.scorecard]), ["NewEntry"])


if __name__ == "__main__":
    unittest.main()
