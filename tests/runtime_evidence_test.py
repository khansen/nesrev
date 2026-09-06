"""Synthetic active runtime-question membership and executable-fixture checks."""
import contextlib
import csv
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import runtime_evidence_check as check
import data_blob_dispositions_check as blobs


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="runtime-evidence-fixture-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.project = self.root / "projects/demo"
        self.docs = self.project / "docs/reverse_engineering"
        (self.docs / "inventory").mkdir(parents=True)
        (self.project / "scripts").mkdir()
        (self.project / "tools/trace/fixtures").mkdir(parents=True)
        (self.project / "project.conf").write_text("# Synthetic project marker\n")
        self.deferrals = self.docs / "inventory/deferrals.csv"
        self.deferrals.write_text(",".join(check.DEFERRAL_FIELDS) + "\n1,Demo corridor,DemoBlob,runtime,Live selection unmeasured,Run the scenario,open\n")
        self.plan = self.docs / "TRACE_PLAN.md"
        self.plan.write_text("# Demo trace\n\nWhich record is selected after the scenario starts?\n")
        (self.project / "scripts/run_trace.py").write_text("import json\nprint(json.dumps({'entered': True, 'result': 1}))\n")
        self.analyzer = self.project / "scripts/analyze_trace.py"
        self.analyzer.write_text("""import json, sys
from pathlib import Path
fields = set()
for name in sys.argv[2:]:
    fields.update(json.loads(Path(name).read_text()))
missing = sorted({'entered', 'result'} - fields)
if missing:
    print('missing ' + ','.join(missing), file=sys.stderr)
    raise SystemExit(1)
Path(sys.argv[1]).write_text('accepted')
print('accepted scenario')
""")
        for name, value in (("valid", {"entered": True, "result": 1}), ("no_entry", {"result": 1}), ("no_result", {"entered": True})):
            (self.project / f"tools/trace/fixtures/{name}.json").write_text(json.dumps(value))
        self.question = {
            "subject": "DemoBlob", "question": "Which record is selected after the scenario starts?",
            "trace_plan": "docs/reverse_engineering/TRACE_PLAN.md", "runner": "scripts/run_trace.py",
            "analyzer": "scripts/analyze_trace.py", "blobs": ["DemoBlob"], "families": [],
            "required_signals": ["entered", "result"],
            "analyzer_command": ["python3", "{analyzer}", "{output}", "{fixtures}"],
            "checks": [
                {"name": "complete", "expect": "accept", "expected_exit": 0, "fixtures": ["tools/trace/fixtures/valid.json"], "missing_signals": [], "diagnostics": ["accepted scenario"]},
                {"name": "entry_missing", "expect": "refuse", "expected_exit": 1, "fixtures": ["tools/trace/fixtures/no_entry.json"], "missing_signals": ["entered"], "diagnostics": ["missing entered"]},
                {"name": "result_missing", "expect": "refuse", "expected_exit": 1, "fixtures": ["tools/trace/fixtures/no_result.json"], "missing_signals": ["result"], "diagnostics": ["missing result"]},
            ],
        }
        self.manifest = self.docs / "inventory/runtime_evidence.json"
        self.rows = [{"label": "DemoBlob", "disposition": "runtime_gated", "artifact": "TRACE_PLAN.md"}]
        self.save()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.track()

    def save(self, questions=None, version=1):
        self.manifest.write_text(json.dumps({"schema_version": version, "questions": [self.question] if questions is None else questions}))

    def track(self):
        subprocess.run(["git", "-C", str(self.root), "add", "."], check=True)

    def validate(self, mode="maturity"):
        with contextlib.redirect_stdout(io.StringIO()) as output:
            errors = check.validate_runtime_evidence(self.docs, self.rows, mode)
        self.output = output.getvalue()
        return errors

    def fail_with(self, message, mode="maturity"):
        self.assertIn(message, "\n".join(self.validate(mode)))

    def test_valid_pending_capture_executes_acceptance_and_each_refusal(self):
        self.assertEqual(self.validate(), [])
        self.assertIn("complete: accept exit=0", self.output)
        self.assertIn("entry_missing: refuse exit=1", self.output)
        self.assertIn("result_missing: refuse exit=1", self.output)
        self.assertIn("captures remain unresolved", self.output)

    def test_process_mode_explicitly_does_not_execute_fixtures(self):
        with patch.object(check, "run_case", side_effect=AssertionError("must not execute")):
            self.assertEqual(self.validate("process"), [])
        self.assertIn("not-run (process structure only)", self.output)

    def test_no_runtime_debt_needs_no_manifest(self):
        self.rows = []
        self.deferrals.write_text(",".join(check.DEFERRAL_FIELDS) + "\n")
        self.manifest.unlink()
        self.assertEqual(self.validate(), [])

    def test_missing_manifest_rejects_runtime_blob(self):
        self.manifest.unlink()
        self.fail_with("require inventory/runtime_evidence.json")

    def test_missing_manifest_rejects_runtime_deferral_without_blob(self):
        self.rows = []
        self.manifest.unlink()
        self.fail_with("require inventory/runtime_evidence.json")

    def test_artifact_free_row_is_rejected_in_row_validator(self):
        row = {name: "evidence" for name in blobs.FIELDS}
        row.update(label="DemoBlob", disposition="runtime_gated", artifact="", reflow_status="not_applicable")
        with contextlib.redirect_stderr(io.StringIO()) as output:
            valid, _ = blobs.validate_rows(Path("rows.csv"), self.docs, [row], "process")
        self.assertFalse(valid)
        self.assertIn("runtime_gated requires an executable trace-plan artifact", output.getvalue())

    def test_blob_must_link_the_bound_plan(self):
        self.rows[0]["artifact"] = "UNRELATED.md"
        self.fail_with("must link its trace_plan artifact")

    def test_plan_must_state_the_specific_question(self):
        self.plan.write_text("# Unrelated trace plan\n")
        self.fail_with("does not state the manifest's question")

    def test_closed_deferral_cannot_back_runtime_question(self):
        self.deferrals.write_text(self.deferrals.read_text().replace(",open", ",closed"))
        self.fail_with("no matching open runtime deferral")

    def test_static_deferral_cannot_back_runtime_question(self):
        self.deferrals.write_text(self.deferrals.read_text().replace(",runtime,", ",static,"))
        self.fail_with("no matching open runtime deferral")

    def test_every_open_runtime_subject_requires_membership(self):
        self.deferrals.write_text(self.deferrals.read_text() + "2,Other,AnotherGap,runtime,Unmeasured,Run another scenario,open\n")
        self.fail_with("open runtime deferrals missing questions: AnotherGap")

    def test_every_runtime_blob_requires_membership(self):
        self.question["blobs"] = []
        self.save()
        self.fail_with("runtime_gated blobs missing questions: DemoBlob")

    def test_question_cannot_invent_runtime_blob(self):
        self.question["blobs"] = ["UnknownBlob"]
        self.save()
        self.fail_with("is not a runtime_gated row")

    def write_runtime_family(self, artifact="TRACE_PLAN.md"):
        path = self.docs / "inventory/data_format_targets.csv"
        path.write_text("family,disposition,artifact,evidence\nbehavior_state_movement_animation,runtime_gated," + artifact + ",Live selection unknown\n")

    def test_runtime_family_without_blob_or_deferral_still_requires_manifest(self):
        self.rows = []
        self.deferrals.unlink()
        self.manifest.unlink()
        self.write_runtime_family()
        self.fail_with("require inventory/runtime_evidence.json")

    def test_runtime_family_requires_question_membership(self):
        self.write_runtime_family()
        self.fail_with("runtime_gated families missing questions")
        self.question["families"] = ["behavior_state_movement_animation"]
        self.save()
        self.assertEqual(self.validate(), [])

    def test_runtime_family_must_link_the_associated_plan(self):
        self.write_runtime_family("UNRELATED.md")
        self.question["families"] = ["behavior_state_movement_animation"]
        self.save()
        self.fail_with("family behavior_state_movement_animation must link its trace_plan artifact")

    def test_non_runtime_family_cannot_be_invented(self):
        self.question["families"] = ["behavior_state_movement_animation"]
        self.save()
        self.fail_with("family behavior_state_movement_animation is not a runtime_gated row")

    def test_missing_optional_blob_inventory_cannot_hide_runtime_deferral(self):
        self.manifest.unlink()
        with contextlib.redirect_stderr(io.StringIO()) as output:
            result = blobs.validate(self.docs / "missing.csv", self.docs, None, None, None, None, 12, "process", False)
        self.assertEqual(result, 1)
        self.assertIn("require inventory/runtime_evidence.json", output.getvalue())

    def test_standalone_family_checker_rejects_artifact_free_runtime_row(self):
        self.write_runtime_family("")
        script = Path(blobs.__file__).with_name("data_format_targets_check.py")
        result = subprocess.run([sys.executable, str(script), str(self.docs / "inventory/data_format_targets.csv"),
                                 "--doc-root", str(self.docs)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("runtime_gated rows require an artifact", result.stderr)

    def test_duplicate_questions_are_rejected(self):
        self.save([self.question, self.question])
        self.fail_with("duplicate runtime subject")

    def test_required_assets_must_be_tracked(self):
        subprocess.run(["git", "-C", str(self.root), "rm", "--cached", "-q", str(self.analyzer.relative_to(self.root))], check=True)
        self.fail_with("analyzer must be tracked")

    def test_untracked_runner_is_rejected(self):
        self.question["runner"] = "scripts/untracked.py"
        (self.project / "scripts/untracked.py").write_text("print('signals')\n")
        self.save()
        self.fail_with("runner must be tracked")

    def test_outside_asset_is_rejected(self):
        self.question["runner"] = "../../outside.py"
        (self.root / "outside.py").write_text("print('signals')\n")
        self.track()
        self.save()
        self.fail_with("escapes the project")

    def test_untracked_literal_glob_cannot_match_tracked_runner(self):
        self.question["runner"] = "scripts/run_*.py"
        (self.project / "scripts/run_*.py").write_text("print('untracked')\n")
        self.save()
        self.fail_with("runner must be tracked")

    def test_plan_anchor_must_exist_outside_fenced_example(self):
        self.question["trace_plan"] += "#acceptance"
        self.rows[0]["artifact"] += "#acceptance"
        self.plan.write_text(self.plan.read_text() + "\n```md\n## Acceptance\n```\n")
        self.save()
        self.fail_with("no matching Markdown anchor")
        self.plan.write_text(self.plan.read_text() + "\n## Acceptance\n")
        self.assertEqual(self.validate(), [])

    def run_blob_cli(self):
        inventory = self.docs / "inventory/data_blob_dispositions.csv"
        row = {name: "evidence" for name in blobs.FIELDS}
        row.update(self.rows[0], reflow_status="not_applicable")
        with inventory.open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=blobs.FIELDS)
            writer.writeheader()
            writer.writerow(row)
        return subprocess.run([sys.executable, str(Path(blobs.__file__)), str(inventory),
                               "--doc-root", str(self.docs), "--required"], capture_output=True, text=True)

    def test_cli_artifact_free_runtime_row_fails(self):
        self.rows[0]["artifact"] = ""
        result = self.run_blob_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("runtime_gated requires an executable trace-plan artifact", result.stderr)

    def test_cli_existing_plan_without_manifest_fails(self):
        self.manifest.unlink()
        result = self.run_blob_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("require inventory/runtime_evidence.json", result.stderr)

    def test_cli_valid_manifest_reports_structure_only(self):
        result = self.run_blob_cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("not-run (process structure only)", result.stdout)

    def test_acceptance_and_complete_refusal_coverage_are_required(self):
        for removed in range(3):
            with self.subTest(removed=removed):
                previous = self.question["checks"]
                self.question["checks"] = previous[:removed] + previous[removed + 1:]
                self.save()
                self.fail_with("refusal coverage must cover every required signal")
                self.question["checks"] = previous

    def test_analyzer_accepting_incomplete_trace_is_rejected(self):
        self.analyzer.write_text(self.analyzer.read_text().replace("raise SystemExit(1)", "raise SystemExit(0)"))
        self.fail_with("expected exit 1, got 0")

    def test_combined_missing_case_cannot_replace_isolated_signal_refusals(self):
        self.question["checks"] = self.question["checks"][:2]
        self.question["checks"][1]["missing_signals"] = ["entered", "result"]
        self.save()
        self.fail_with("refusal coverage must cover every required signal")

    def test_wrong_failure_diagnostic_is_not_a_refusal_pass(self):
        self.analyzer.write_text(self.analyzer.read_text().replace("'missing '", "'unrelated error '"))
        self.fail_with("missing diagnostic")

    def test_refusal_diagnostic_may_be_in_fresh_output_summary(self):
        self.analyzer.write_text(self.analyzer.read_text().replace(
            "print('missing ' + ','.join(missing), file=sys.stderr)",
            "Path(sys.argv[1]).write_text('missing ' + ','.join(missing))"))
        self.assertEqual(self.validate(), [])

    def test_output_from_another_case_cannot_supply_missing_diagnostic(self):
        self.analyzer.write_text(self.analyzer.read_text().replace(
            "print('missing ' + ','.join(missing), file=sys.stderr)", "print('unrelated error')"))
        self.analyzer.write_text(self.analyzer.read_text().replace(
            "write_text('accepted')", "write_text('missing entered')"))
        self.fail_with("missing diagnostic")

    def test_missing_fixture_is_rejected_before_execution(self):
        self.question["checks"][0]["fixtures"] = ["missing.json"]
        self.save()
        self.fail_with("fixture is missing")

    def test_command_requires_actual_analyzer_and_isolated_output(self):
        for command in (["python3", "-c", "print('accepted')"], ["python3", "{analyzer}", "{fixtures}"], ["python3", "{analyzer}", "{output}", "{fixtures}", "{unknown}"]):
            with self.subTest(command=command):
                self.question["analyzer_command"] = command
                self.save()
                self.assertTrue(self.validate())

    def test_boolean_schema_and_exit_are_rejected(self):
        self.save(version=True)
        self.fail_with("invalid runtime evidence schema_version")
        self.question["checks"][0]["expected_exit"] = False
        self.save()
        self.fail_with("invalid expectation/exit")

    def test_analyzer_timeout_is_not_an_expected_refusal(self):
        case = self.question["checks"][1]
        with patch.object(check.subprocess, "run", side_effect=subprocess.TimeoutExpired(["analyzer"], 30)):
            with self.assertRaisesRegex(check.EvidenceError, "could not complete"):
                check.run_case("DemoBlob", case, self.analyzer, [], self.question["analyzer_command"])

    def test_malformed_deferral_enum_is_not_silently_static(self):
        self.deferrals.write_text(self.deferrals.read_text().replace(",runtime,", ",runtim,"))
        self.fail_with("invalid kind/status")


if __name__ == "__main__":
    unittest.main()
