import csv
import io
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import raw_ram_reconciliation as reconciliation


FACT_FIELDS = ("active", "operand_count", "distinct_owner_count", "read_count",
               "write_count", "top_readers", "top_writers")
FIELDS = ["addr_hex", "status", "proposed_symbol", "notes", "last_pass_reviewed", *FACT_FIELDS]
CURRENT = dict(zip(FIELDS, ["0x0010", "deferred", "ZP_Cursor", "keep this judgment", "7",
                           "yes", "2", "1", "1", "1", "FrameEntry:1", "FrameEntry:1"]))


class ReconciliationTests(unittest.TestCase):
    def compare(self, actual, expected, raw=None):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "queue.csv"
            if raw is None:
                output = io.StringIO(newline="")
                writer = csv.DictWriter(output, fieldnames=FIELDS, lineterminator="\n")
                writer.writeheader()
                writer.writerows(actual.values())
                raw = output.getvalue().encode("utf-8")
            path.write_bytes(raw)
            result = reconciliation.compare(path, actual, expected, FIELDS)
            self.assertEqual(path.read_bytes(), raw)
            return result

    def test_every_factual_field_and_missing_rows_are_checked(self):
        for field in FACT_FIELDS:
            with self.subTest(field=field):
                actual = {"0x0010": {**CURRENT, field: "stale"}}
                result = self.compare(actual, [CURRENT])
                self.assertEqual(result["status"], "stale")
                self.assertEqual(set(result["changes"][0]["fields"]), {field})
        result = self.compare({}, [CURRENT])
        self.assertTrue(result["changes"][0]["missing_row"])

    def test_authored_decisions_are_not_inferred_or_rewritten(self):
        row = {**CURRENT, "status": "revisit", "notes": "authored reason"}
        result = self.compare({"0x0010": row}, [row])
        self.assertEqual(result["status"], "pass")
        self.assertEqual(row["notes"], "authored reason")

    def test_no_candidates_needs_no_ledger(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "absent.csv"
            rows = reconciliation.read_review(path, FIELDS)
            self.assertEqual(reconciliation.compare(path, rows, [], FIELDS)["status"], "pass")
            self.assertFalse(path.exists())
            self.assertEqual(reconciliation.compare(path, rows, [CURRENT], FIELDS)["status"], "stale")
            self.assertFalse(path.exists())

    def test_blank_status_normalization_is_reported(self):
        row = {**CURRENT, "status": ""}
        result = self.compare({"0x0010": row}, [{**row, "status": "unreviewed"}])
        self.assertEqual(result["status"], "stale")
        self.assertEqual(result["changes"][0]["fields"],
                         {"status": {"actual": "", "expected": "unreviewed"}})
        self.assertFalse(result["serialization_changed"])

    def test_csv_serialization_drift_is_stale_even_when_fields_match(self):
        for fields, ending, quoting in (
            (list(reversed(FIELDS)), "\n", csv.QUOTE_MINIMAL),
            (FIELDS, "\r\n", csv.QUOTE_MINIMAL),
            (FIELDS, "\n", csv.QUOTE_ALL),
        ):
            with self.subTest(fields=fields, ending=ending, quoting=quoting):
                output = io.StringIO(newline="")
                writer = csv.DictWriter(output, fieldnames=fields, lineterminator=ending, quoting=quoting)
                writer.writeheader()
                writer.writerow(CURRENT)
                result = self.compare({"0x0010": CURRENT}, [CURRENT], output.getvalue().encode())
                self.assertEqual(result["status"], "stale")
                self.assertTrue(result["serialization_changed"])
                self.assertEqual(result["changes"], [])

    def test_renderer_preserves_quoted_multiline_unicode_notes(self):
        row = {"name": "entry", "notes": 'keep, "résumé"\nsecond line'}
        rendered = reconciliation.render_review([row], ["name", "notes"])
        self.assertEqual(rendered, 'name,notes\nentry,"keep, ""résumé""\nsecond line"\n'.encode())

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
