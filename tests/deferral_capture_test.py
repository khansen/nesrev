import contextlib
import csv
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import deferral_capture as capture


class DeferralCaptureTests(unittest.TestCase):
    def test_kind_keyword_cannot_be_the_condition(self):
        for kind in ("static", "runtime", "STATIC", "RunTime"):
            for ending in ("", " :: runtime", " :: static"):
                with self.subTest(kind=kind, ending=ending):
                    with self.assertRaisesRegex(ValueError, "subject :: revisit condition :: kind"):
                        capture.explicit_entries(f"cue identity ::  {kind}  {ending}")

    def test_real_conditions_and_explicit_kinds_keep_their_meaning(self):
        entries = capture.explicit_entries(
            "cue identity :: static caller analysis; timing :: runtime capture :: runtime"
        )
        self.assertEqual(entries, [
            {"deferral":"cue identity", "revisit_condition":"static caller analysis", "kind":"static"},
            {"deferral":"timing", "revisit_condition":"runtime capture", "kind":"runtime"},
        ])
        self.assertEqual(capture.explicit_entries("cue identity")[0]["revisit_condition"], "")

    def test_invalid_batch_leaves_existing_or_absent_ledger_untouched(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "deferrals.csv"
            for existing in (False, True):
                if existing:
                    path.write_bytes(b"authored ledger bytes\r\n")
                before = path.read_bytes() if path.exists() else None
                with self.subTest(existing=existing), contextlib.redirect_stderr(io.StringIO()):
                    rc = capture.main([str(path), "--pass-id", "1", "--explicit",
                                       "valid cue :: compare callers; invalid gap :: runtime"])
                    self.assertEqual(rc, 2)
                    self.assertEqual(path.read_bytes() if path.exists() else None, before)

    def test_matching_plan_accepts_numeric_and_string_pass_id(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plan.json"
            for pass_id in (7, "7"):
                path.write_text(json.dumps({"project":"fixture", "intended_pass_id":pass_id,
                                            "corridor_objective":{"selected_corridor":"  Saved corridor  "}}))
                with self.subTest(pass_id=pass_id), contextlib.redirect_stderr(io.StringIO()) as err:
                    self.assertEqual(capture.capture_corridor(" \t", path, "fixture", "7"), "Saved corridor")
                    self.assertEqual(err.getvalue(), "")

    def test_explicit_corridor_wins_without_reading_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plan.json"
            path.write_text("malformed")
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(capture.capture_corridor("  Explicit corridor  ", path, "fixture", "7"),
                                 "Explicit corridor")
                self.assertEqual(err.getvalue(), "")

    def test_missing_invalid_legacy_or_mismatched_context_warns_without_guessing(self):
        matching = {"project":"fixture", "intended_pass_id":7,
                    "corridor_objective":{"selected_corridor":"Unrelated corridor"}}
        cases = {
            "missing": None,
            "malformed": "{",
            "non_object": "[]",
            "other_project": json.dumps({**matching, "project":"another_project"}),
            "other_pass": json.dumps({**matching, "intended_pass_id":8}),
            "boolean_pass": json.dumps({**matching, "intended_pass_id":True}),
            "float_pass": json.dumps({**matching, "intended_pass_id":7.0}),
            "non_decimal_pass": json.dumps({**matching, "intended_pass_id":"²"}),
            "missing_identity": json.dumps({"corridor_objective":matching["corridor_objective"]}),
            "legacy": json.dumps({"project":"fixture", "intended_pass_id":7,
                                   "selected_cluster":"Generated cluster", "anchor_target":"Anchor"}),
            "bad_objective": json.dumps({**matching, "corridor_objective":[]}),
            "bad_corridor": json.dumps({**matching, "corridor_objective":{"selected_corridor":42}}),
            "empty_corridor": json.dumps({**matching, "corridor_objective":{"selected_corridor":" \t"}}),
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plan.json"
            for name, text in cases.items():
                path.unlink(missing_ok=True)
                if text is not None:
                    path.write_text(text)
                with self.subTest(name=name), contextlib.redirect_stderr(io.StringIO()) as err:
                    self.assertEqual(capture.capture_corridor("", path, "fixture", "1" if name == "boolean_pass" else "7"), "")
                    self.assertIn("corridor unavailable", err.getvalue())
                    self.assertIn("FOCUS=<corridor>", err.getvalue())

    def test_empty_or_duplicate_capture_needs_no_context_and_preserves_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "deferrals.csv"
            args = [str(path), "--pass-id", "7", "--plan", str(path.parent / "missing.json"),
                    "--project", "fixture"]
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(capture.main(args), 0)
                self.assertFalse(path.exists())
                self.assertEqual(err.getvalue(), "")
            path.write_text('pass_id,corridor,subject,kind,deferral,revisit_condition,status\n'
                            '7,Authored corridor,curated-key,runtime,cue identities,Read both callers,resolved\n')
            before = path.read_bytes()
            with contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(capture.main(args + ["--explicit", "cue identities :: compare callers"]), 0)
                self.assertEqual(path.read_bytes(), before)
                self.assertEqual(err.getvalue(), "")

    def test_tagged_notes_get_saved_corridor_without_runtime_inference(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "deferrals.csv"
            plan = path.parent / "plan.json"
            plan.write_text(json.dumps({"project":"fixture", "intended_pass_id":7,
                                        "corridor_objective":{"selected_corridor":"Saved corridor"}}))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(capture.main([str(path), "--pass-id", "7", "--plan", str(plan),
                                               "--project", "fixture", "--notes",
                                               "Deferred: dynamic feature identities."]), 0)
            with path.open(newline="") as handle:
                rows = list(csv.DictReader(handle))
            self.assertEqual(len(rows), 1)
            self.assertEqual(rows[0]["corridor"], "Saved corridor")
            self.assertEqual(rows[0]["kind"], "static")
            self.assertEqual(rows[0]["revisit_condition"], "")


if __name__ == "__main__":
    unittest.main()
