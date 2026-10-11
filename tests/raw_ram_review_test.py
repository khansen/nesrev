"""Exercise address admission through the real review and documentation wrappers."""

import csv
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from raw_ram_review import FIELDS, read_review


def ledger(*rows):
    output = io.StringIO(newline="")
    writer = csv.DictWriter(output, fieldnames=FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return output.getvalue().encode()


def row(address, **values):
    return {**dict.fromkeys(FIELDS, ""), "addr_hex": address,
            "status": "revisit", "active": "yes", **values}


class ReviewInputs(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="nesrev-ram-review-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.project = self.root / "projects/sample"
        self.project.mkdir(parents=True)
        self.docs = self.project / "docs"
        self.queue = self.docs / "inventory/raw_ram_review.csv"
        (self.root / "scripts").symlink_to(ROOT / "scripts", target_is_directory=True)
        (self.project / "project.conf").write_text('''ASM_FILE="projects/sample/input.asm"
REF_NES="unused.nes"
DOC_ROOT="projects/sample/docs"
SYSTEMS_DOC="projects/sample/docs/Systems.md"
WARN_BASELINE_FILE="projects/sample/docs/warnings.txt"
NESREV_RECOVERY_STATUS="none"
''')

    def write(self, content):
        self.queue.parent.mkdir(parents=True, exist_ok=True)
        self.queue.write_bytes(content)

    def review(self, address, *, make=False, notes="", symbol="", status="revisit"):
        command = (["make", "--no-print-directory", "-f", str(ROOT / "Makefile"),
                    "project-raw-ram-review", "PROJECT=sample", f"ADDR={address}",
                    f"STATUS={status}", f"SYMBOL={symbol}", f"NOTES={notes}", "PASS=8"]
                   if make else ["bash", str(ROOT / "scripts/project_raw_ram_review.sh"),
                                 "sample", address, status, symbol, notes, "8"])
        return subprocess.run(command, cwd=self.root, capture_output=True, text=True)

    def test_supported_boundaries_and_input_spellings_through_both_wrappers(self):
        addresses = {"0": "0x0000", "$FF": "0x00ff", "0100": "0x0100",
                     "0X07FF": "0x07ff", "0800": "0x0800", "$0CA0": "0x0ca0",
                     "0fff": "0x0fff", "1000": "0x1000", "$1FFF": "0x1fff",
                     "6000": "0x6000", "$6B20": "0x6b20", "0x7FFF": "0x7fff"}
        for make in (False, True):
            self.write(ledger())
            for given, expected in addresses.items():
                with self.subTest(make=make, address=given):
                    result = self.review(given, make=make)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn(expected, read_review(self.queue))
            self.assertEqual(list(read_review(self.queue)), list(addresses.values()))

    def test_rejected_input_never_creates_or_changes_a_ledger(self):
        for make in (False, True):
            for address in ("0x2000", "$4016", "5fff", "$8000", "0xFFFF",
                            "10000", "-1", "0x", "nope", "$20+1", ""):
                for existing in (False, True):
                    with self.subTest(make=make, address=address, existing=existing):
                        before = ledger(row("0x0010", notes="untouched")) if existing else None
                        if existing:
                            self.write(before)
                        else:
                            self.queue.unlink(missing_ok=True)
                        result = self.review(address, make=make)
                        self.assertNotEqual(result.returncode, 0, result.stdout)
                        if address:
                            self.assertIn("raw-RAM address", result.stderr)
                        self.assertEqual(self.queue.read_bytes() if self.queue.exists() else None, before)

    def test_rejection_does_not_create_inventory_directory(self):
        result = self.review("0x8000")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.docs.exists())

    def test_review_preserves_mirrors_overlays_history_and_quoted_notes(self):
        original = [row("0x04a0", status="symbolized", active="no", notes="old judgment"),
                    row("0x0ca0", status="symbolized", active="no", notes='keep, "résumé"\nsecond line'),
                    row("0x6b20", proposed_symbol="RAM_SceneOverlay", operand_count="3")]
        self.write(ledger(*original))
        notes = "scene's $20 bits; $(touch must-not-exist) `touch also-must-not-exist`"
        result = self.review("$6B20", make=True, notes=notes)
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = read_review(self.queue)
        self.assertEqual(list(rows), [r["addr_hex"] for r in original])
        self.assertEqual(list(rows.values())[:2], original[:2])
        self.assertEqual(rows["0x6b20"], {**original[2], "notes": notes, "last_pass_reviewed": "8"})
        self.assertFalse((self.root / "must-not-exist").exists())
        self.assertFalse((self.root / "also-must-not-exist").exists())

    def test_existing_invalid_rows_block_review_before_any_write(self):
        valid = row("0x0010", notes="do not update")
        for active in ("yes", "no", ""):
            for address in ("0x2000", "0x8000", "0xffff", "", "0x10000", "$0010"):
                with self.subTest(address=address, active=active):
                    before = ledger(valid, row(address, active=active))
                    self.write(before)
                    result = self.review("0x0010", notes="must not land")
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("raw_ram_review.csv:3: invalid raw-RAM address" if address in
                                  ("", "0x10000", "$0010") else
                                  "raw_ram_review.csv:3: raw-RAM address", result.stderr)
                    self.assertEqual(self.queue.read_bytes(), before)

    def test_duplicate_and_malformed_rows_are_not_lost_during_updates(self):
        valid = ledger(row("0x0010"))
        for before in (ledger(row("0x0010"), row("0X0010", active="no")),
                       valid.replace(b"addr_hex,", b"wrong,"),
                       valid.rstrip(b"\n") + b",extra\n",
                       valid.replace(b"yes,,,,,,", b"yes,,,,,")):
            with self.subTest(before=before):
                self.write(before)
                result = self.review("0x0020")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertEqual(self.queue.read_bytes(), before)

    def test_reordered_columns_are_refused_before_review_writes(self):
        original = row("0x0010", notes="preserve this judgment")
        output = io.StringIO(newline="")
        reordered_fields = [FIELDS[1], FIELDS[0], *FIELDS[2:]]
        writer = csv.DictWriter(output, fieldnames=reordered_fields, lineterminator="\n")
        writer.writeheader()
        writer.writerow(original)
        before = output.getvalue().encode()
        for make in (False, True):
            with self.subTest(make=make):
                self.write(before)
                self.assertEqual(read_review(self.queue), {"0x0010": original})
                result = self.review("0x0010", make=make, notes="must not land")
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("invalid raw-RAM ledger columns", result.stderr)
                self.assertEqual(self.queue.read_bytes(), before)

    def prepare_docs(self):
        self.docs.mkdir(exist_ok=True)
        (self.project / "input.asm").write_text(".ORG $C000\nReset:\n RTS\n")
        for name in ("Systems.md", "warnings.txt", "QUICK_REFERENCE.md"):
            (self.docs / name).write_text("")
        (self.docs / "SEMANTIC_CLAIMS.md").write_text("# Semantic Claims\n")
        (self.docs / "PROGRESS_SCORECARD.md").write_text(
            "| pass_id | verify | docs_check | rework_items | notes |\n"
            "|---|---|---|---|---|\n| 0 | pass | pass | 0 | Synthetic fixture. |\n")
        (self.queue.parent / "renames.csv").write_text("old_name,new_name,reason,confidence,pass_id\n")

    def docs_check(self):
        return subprocess.run(["bash", str(ROOT / "scripts/project_docs_check.sh"), "sample"],
                              cwd=self.root, capture_output=True, text=True)

    def test_docs_wrapper_validates_inactive_rows_and_accepts_mirror_overlay_controls(self):
        self.write(ledger(row("0x0ca0", active="no"), row("0x6b20")))
        self.prepare_docs()
        result = self.docs_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for address, diagnostic in (("0x8000", "outside supported RAM windows"),
                                    ("garbage", "invalid raw-RAM address"),
                                    ("0X0010", "duplicate raw-RAM address")):
            for active in ("yes", "no"):
                with self.subTest(address=address, active=active):
                    before = ledger(row("0x0010"), row(address, active=active))
                    self.write(before)
                    result = self.docs_check()
                    self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                    self.assertIn(diagnostic, result.stderr)
                    self.assertIn("raw_ram_review.csv:3:", result.stderr)
                    self.assertEqual(self.queue.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
