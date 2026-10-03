"""Committed analyzer contracts must work without the checkout's private inputs."""
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import runtime_evidence_test as fixtures

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import runtime_evidence_check as runtime
import runtime_evidence_portability as portability


class PortabilityTests(unittest.TestCase):
    save = fixtures.RuntimeTests.save
    track = fixtures.RuntimeTests.track

    def setUp(self):
        fixtures.RuntimeTests.setUp(self)
        self.git("config", "user.name", "Tests")
        self.git("config", "user.email", "tests@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("commit", "--allow-empty", "-qm", "Before runtime contract", "--only")
        self.base = self.git("rev-parse", "HEAD")
        (self.docs / "inventory/data_blob_dispositions.csv").write_text(
            "label,disposition,artifact\nDemoBlob,runtime_gated,TRACE_PLAN.md\n")
        self.commit()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], text=True).strip()

    def commit(self):
        self.track()
        self.git("commit", "-qm", "Runtime fixture")
        self.head = self.git("rev-parse", "HEAD")

    def evaluate(self):
        return portability.evaluate(self.root, "demo", str(self.docs.relative_to(self.root)), self.base, self.head)

    def evaluate_with_tmpdir(self, directory):
        command = [sys.executable, "-B", portability.__file__, "--project", "demo",
                   "--doc-root", str(self.docs.relative_to(self.root)),
                   "--base", self.base, "--head", self.head]
        run = subprocess.run(command, cwd=self.root, capture_output=True, text=True,
                             env={**os.environ, "TMPDIR": str(directory)})
        result = json.loads(run.stdout)
        self.assertEqual(run.returncode, int(result["status"] == "fail"), run.stderr)
        return result

    def test_positive_and_isolated_missing_signals_use_committed_export(self):
        result = self.evaluate()
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual([case["exit_status"] for case in result["cases"]], [0, 1, 1])
        self.assertEqual(result["captures"], "unresolved")
        for case in result["cases"]:
            self.assertEqual(case["matched_diagnostics"], case["diagnostics"])
            self.assertNotIn(str(self.root), " ".join(case["command"]))
            self.assertIn("runtime-portability-", " ".join(case["command"]))
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_live_maturity_pass_does_not_hide_ignored_capture_dependency(self):
        capture = self.project / "tmp/private-capture.json"
        capture.parent.mkdir()
        capture.write_text("{}")
        (self.root / ".gitignore").write_text("projects/*/tmp/\n")
        self.analyzer.write_text('from pathlib import Path\nPath(__file__).resolve().parents[1].joinpath("tmp/private-capture.json").read_text()\n' + self.analyzer.read_text())
        self.commit()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(runtime.validate_runtime_evidence(self.docs, self.rows, "maturity"), [])
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("private-capture.json", " ".join(result["errors"]))
        self.assertEqual(capture.read_text(), "{}")

    def test_repository_local_tmpdir_cannot_recover_ignored_capture_via_git(self):
        capture = self.project / "tmp/private-capture.json"
        capture.parent.mkdir()
        capture.write_text("{}")
        (self.root / ".gitignore").write_text("projects/*/tmp/\n/tmp/\n")
        local_tmp = self.root / "tmp"
        local_tmp.mkdir()
        self.analyzer.write_text(
            'import subprocess\nfrom pathlib import Path\n'
            'root = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()\n'
            'Path(root, "projects/demo/tmp/private-capture.json").read_text()\n' + self.analyzer.read_text())
        self.commit()
        with tempfile.TemporaryDirectory(prefix="portability-outside-") as outside:
            self.assertEqual(self.evaluate_with_tmpdir(outside)["status"], "fail")
            alias = Path(outside) / "inside-link"
            alias.symlink_to(local_tmp)
            for directory in (self.root, local_tmp, alias):
                with self.subTest(directory=directory):
                    result = self.evaluate_with_tmpdir(directory)
                    self.assertEqual(result["status"], "fail", result)
                    self.assertIn("temporary directory must be outside", " ".join(result["errors"]))
                    self.assertIn("TMPDIR", " ".join(result["errors"]))
                    self.assertTrue(all(case["status"] == "not-run" for case in result["cases"]))
        self.assertEqual(capture.read_text(), "{}")
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), "")

    def test_cases_and_export_cannot_discover_git_above_external_scratch(self):
        self.analyzer.write_text(
            'import subprocess\nfrom pathlib import Path\n'
            'for directory in (Path.cwd(), Path(__file__).resolve().parent):\n'
            '    found = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=directory, capture_output=True)\n'
            '    if found.returncode == 0:\n'
            '        raise SystemExit("unexpected enclosing repository")\n' + self.analyzer.read_text())
        self.commit()
        with tempfile.TemporaryDirectory(prefix="portability-enclosing-repo-") as outer:
            subprocess.run(["git", "init", "-q", outer], check=True)
            directory = Path(outer) / "scratch"
            directory.mkdir()
            result = self.evaluate_with_tmpdir(directory)
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual([case["exit_status"] for case in result["cases"]], [0, 1, 1])

    def test_failing_case_records_actual_exit_and_does_not_hide_other_cases(self):
        self.analyzer.write_text("raise SystemExit(7)\n")
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertEqual([case["exit_status"] for case in result["cases"]], [7, 7, 7])
        self.assertIn("expected exit 0, got 7", result["errors"][0])

    def test_refusal_case_that_no_longer_omits_signal_is_a_failure(self):
        (self.project / "tools/trace/fixtures/no_entry.json").write_text('{"entered":true,"result":1}')
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("entry_missing: expected exit 1, got 0", " ".join(result["errors"]))

    def test_wrong_failure_diagnostic_cannot_count_as_a_refusal(self):
        (self.project / "tools/trace/fixtures/no_entry.json").write_text("malformed JSON")
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("missing diagnostic 'missing entered'", " ".join(result["errors"]))

    def test_missing_declared_acceptance_or_refusal_is_refused(self):
        self.question["checks"] = self.question["checks"][:1]
        self.save()
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("missing-signal refusal coverage", " ".join(result["errors"]))

    def test_local_pythonpath_cannot_supply_ignored_dependencies(self):
        helpers = self.project / "tmp"
        helpers.mkdir()
        (helpers / "private_helper.py").write_text("value = 1\n")
        (self.root / ".gitignore").write_text("projects/*/tmp/\n")
        self.analyzer.write_text("import private_helper\n" + self.analyzer.read_text())
        self.commit()
        with patch.dict(os.environ, {"PYTHONPATH": str(helpers)}):
            result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("private_helper", " ".join(result["errors"]))

    def test_unrelated_document_change_is_explicitly_out_of_scope(self):
        self.base = self.head
        (self.project / "README.md").write_text("Unrelated onboarding clarification.\n")
        self.commit()
        with patch.object(portability, "export_commit", side_effect=AssertionError("unexpected export")):
            result = self.evaluate()
        self.assertEqual(result["status"], "not-required", result)
        self.assertEqual(result["reason"], "no_affected_inputs")
        self.assertEqual(result["cases"], [])

    def test_helper_change_runs_existing_declared_contract(self):
        self.base = self.head
        (self.root / "scripts").mkdir()
        (self.root / "scripts/shared_runtime.py").write_text("VALUE = 1\n")
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["trigger_paths"], ["scripts/shared_runtime.py"])

    def test_export_keeps_shared_helpers_but_excludes_other_projects(self):
        (self.root / "scripts").mkdir()
        (self.root / "scripts/shared_runtime.py").write_text("VALUE = 7\n")
        other = self.root / "projects/other/scripts"
        other.mkdir(parents=True)
        (other / "helper.py").write_text("VALUE = 9\n")
        self.analyzer.write_text(
            'import sys\nfrom pathlib import Path\n'
            'root = Path(__file__).resolve().parents[3]\n'
            'sys.path.insert(0, str(root / "scripts"))\n'
            'from shared_runtime import VALUE\n'
            'assert VALUE == 7\n'
            'assert not (root / "projects/other").exists()\n' + self.analyzer.read_text())
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "pass", result)

    def test_reverted_analyzer_change_is_still_in_review_range(self):
        self.base = self.head
        original = self.analyzer.read_text()
        self.analyzer.write_text(original + "\n# temporary edit\n")
        self.commit()
        self.analyzer.write_text(original)
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "pass", result)
        self.assertIn("projects/demo/scripts/analyze_trace.py", result["trigger_paths"])

    def test_no_runtime_manifest_does_not_require_export_or_fixtures(self):
        self.manifest.unlink()
        self.deferrals.write_text(",".join(runtime.DEFERRAL_FIELDS) + "\n")
        (self.docs / "inventory/data_blob_dispositions.csv").write_text("label,disposition,artifact\n")
        self.commit()
        self.base = self.head
        with patch.object(portability, "export_commit", side_effect=AssertionError("unexpected export")):
            result = self.evaluate()
        self.assertEqual(result["status"], "not-required", result)
        self.assertEqual(result["reason"], "no_active_manifest")

    def test_legacy_runtime_debt_without_manifest_is_refused(self):
        self.manifest.unlink()
        self.commit()
        self.base = self.head
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("require inventory/runtime_evidence.json", " ".join(result["errors"]))

    def test_resolved_questions_can_remove_manifest_and_runtime_debt(self):
        self.base = self.head
        self.manifest.unlink()
        self.deferrals.write_text(",".join(runtime.DEFERRAL_FIELDS) + "\n")
        (self.docs / "inventory/data_blob_dispositions.csv").write_text("label,disposition,artifact\n")
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "not-required", result)
        self.assertEqual(result["reason"], "no_active_questions")

    def test_review_can_repair_a_malformed_historical_manifest(self):
        for malformed in ('not JSON', '{"questions":[{"checks":null}]}'):
            with self.subTest(malformed=malformed):
                self.manifest.write_text(malformed)
                self.commit()
                self.base = self.head
                self.save()
                self.commit()
                result = self.evaluate()
                self.assertEqual(result["status"], "pass", result)

    def test_removing_required_manifest_cannot_hide_tests(self):
        self.base = self.head
        self.manifest.unlink()
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("require inventory/runtime_evidence.json", " ".join(result["errors"]))

    def test_dirty_or_different_checkout_cannot_supply_evidence(self):
        self.analyzer.write_text("changed\n")
        self.assertIn("must be clean", " ".join(self.evaluate()["errors"]))
        self.head = self.base
        self.assertIn("must be checked out", " ".join(self.evaluate()["errors"]))

    def test_committed_symlink_cannot_escape_export_to_private_input(self):
        (self.project / "private_link").symlink_to(self.temp.name)
        self.commit()
        result = self.evaluate()
        self.assertEqual(result["status"], "fail")
        self.assertIn("export symlink escapes", " ".join(result["errors"]))


if __name__ == "__main__":
    unittest.main()
