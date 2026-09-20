#!/usr/bin/env python3
"""PDF/OCR dependency checks, without requiring those tools on the test host."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import reference_tools as refs


class ReferenceToolsTests(unittest.TestCase):
    def test_plain_text_html_and_empty_reference_set_need_no_ocr(self):
        with patch.object(refs, "tool_status") as probe:
            for files in ([], [Path("manual.txt"), Path("faq.HTML"), Path("notes.md")]):
                self.assertEqual(refs.reference_tool_issues(files), [])
            probe.assert_not_called()

    def test_pdf_requires_both_extraction_and_scan_fallback(self):
        with patch.object(refs.shutil, "which", return_value=None):
            issues = refs.reference_tool_issues([Path("Manual.PDF")])
        self.assertEqual(len(issues), 3)
        self.assertTrue(any("pdftotext:" in issue and "poppler" in issue for issue in issues))
        self.assertTrue(any("pdftoppm:" in issue for issue in issues))
        self.assertTrue(any("tesseract:" in issue for issue in issues))

    def test_image_reference_requires_ocr_without_poppler(self):
        with patch.object(refs.shutil, "which", return_value=None):
            issues = refs.reference_tool_issues([Path("manual.txt"), Path("faq/page.TIFF")])
        self.assertEqual(len(issues), 1)
        self.assertTrue(issues[0].startswith("tesseract:"))

    def test_project_collection_includes_faq_scans_but_not_markers_or_empty_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manual = root / "projects/demo/docs/game_reference/manuals"
            faq = manual.parent / "faqs/pages"
            manual.mkdir(parents=True)
            faq.mkdir(parents=True)
            (manual / ".gitkeep").write_text("marker")
            (manual / "empty.pdf").touch()
            (manual / "manual.txt").write_text("manual")
            (faq / "page.png").write_text("scan fixture")
            files = refs.project_reference_files(root, "demo")
            self.assertEqual(files, [manual / "manual.txt", faq / "page.png"])
            self.assertEqual(refs.required_tools(files), {"tesseract"})

    def test_poppler_uses_its_real_version_flag_and_stderr_banner(self):
        with patch.object(refs.shutil, "which", return_value="/tools/pdftotext"), \
             patch.object(refs.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "pdftotext version fixture\n")) as run:
            self.assertEqual(refs.tool_status("pdftotext"), (True, "pdftotext version fixture"))
        self.assertEqual(run.call_args.args[0], ["/tools/pdftotext", "-v"])

    def test_broken_or_hanging_binary_is_not_ready(self):
        results = [subprocess.CompletedProcess([], 1, "", "broken"),
                   subprocess.TimeoutExpired("pdftoppm", 10), OSError("cannot execute")]
        for result in results:
            with self.subTest(result=result), patch.object(refs.shutil, "which", return_value="/tools/pdftoppm"), \
                 patch.object(refs.subprocess, "run", side_effect=[result]):
                ok, message = refs.tool_status("pdftoppm")
                self.assertFalse(ok)
                self.assertIn("pdftoppm", message)

    def test_ocr_engine_without_recognition_language_data_is_not_ready(self):
        for output, code in (("List of available languages (0):\n", 0),
                             ("List of available languages (1):\nosd\n", 0),
                             ("eng\n", 1)):
            with self.subTest(output=output, code=code), patch.object(refs.shutil, "which", return_value="/tools/tesseract"), \
                 patch.object(refs.subprocess, "run", side_effect=[
                     subprocess.CompletedProcess([], 0, "tesseract fixture\n", ""),
                     subprocess.CompletedProcess([], code, output, ""),
                 ]):
                ok, message = refs.tool_status("tesseract")
                self.assertFalse(ok)
                self.assertIn("language data", message)

    def test_non_english_recognition_language_is_usable(self):
        with patch.object(refs.shutil, "which", return_value="/tools/tesseract"), \
             patch.object(refs.subprocess, "run", side_effect=[
                 subprocess.CompletedProcess([], 0, "tesseract fixture\n", ""),
                 subprocess.CompletedProcess([], 0, "List of available languages (2):\njpn\nosd\n", ""),
             ]):
            self.assertEqual(refs.tool_status("tesseract"), (True, "tesseract fixture; 1 recognition language(s) available"))


if __name__ == "__main__":
    unittest.main()
