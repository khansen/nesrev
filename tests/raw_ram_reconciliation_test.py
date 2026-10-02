import csv
import io
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import raw_ram_reconciliation as reconciliation


FIELDS = ["addr_hex", "status", "proposed_symbol", "notes", "last_pass_reviewed",
          *reconciliation.FACT_FIELDS]
CURRENT = dict(zip(FIELDS, ["0x0010", "deferred", "ZP_Cursor", "keep this judgment", "7",
                           "yes", "2", "1", "1", "1", "FrameEntry:1", "FrameEntry:1"]))


class ReconciliationTests(unittest.TestCase):
    def test_every_factual_field_and_missing_rows_are_checked(self):
        for field in reconciliation.FACT_FIELDS:
            with self.subTest(field=field):
                actual = {"0x0010": {**CURRENT, field: "stale"}}
                result = reconciliation.compare("queue.csv", actual, [CURRENT])
                self.assertEqual(result["status"], "stale")
                self.assertEqual(set(result["changes"][0]["fields"]), {field})
        result = reconciliation.compare("queue.csv", {}, [CURRENT])
        self.assertTrue(result["changes"][0]["missing_row"])

    def test_authored_decisions_are_not_inferred_or_rewritten(self):
        row = {**CURRENT, "status": "revisit", "notes": "authored reason"}
        result = reconciliation.compare("queue.csv", {"0x0010": row}, [CURRENT])
        self.assertEqual(result["status"], "pass")
        self.assertEqual(row["notes"], "authored reason")

    def test_no_candidates_needs_no_ledger(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "absent.csv"
            rows = reconciliation.read_review(path, FIELDS)
            self.assertEqual(reconciliation.compare(path, rows, [])["status"], "pass")
            self.assertFalse(path.exists())

    def test_invalid_ledgers_are_not_silently_collapsed(self):
        output = io.StringIO()
        writer = csv.DictWriter(output, fieldnames=FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerow(CURRENT)
        valid = output.getvalue()
        bad_inputs = [valid + valid.splitlines()[1] + "\n",
                      valid.replace("addr_hex,", "wrong_column,"),
                      valid.rstrip() + ",surplus\n",
                      valid.replace("0x0010,", ","),
                      valid.replace(",FrameEntry:1,FrameEntry:1", ",FrameEntry:1")]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "queue.csv"
            path.write_text(valid)
            before = path.read_bytes()
            self.assertEqual(reconciliation.read_review(path, FIELDS), {"0x0010": CURRENT})
            self.assertEqual(path.read_bytes(), before)
            for value in bad_inputs:
                with self.subTest(value=value):
                    path.write_text(value)
                    with self.assertRaises((ValueError, csv.Error)):
                        reconciliation.read_review(path, FIELDS)


if __name__ == "__main__":
    unittest.main()
