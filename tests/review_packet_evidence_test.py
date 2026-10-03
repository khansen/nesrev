import json
import argparse
import copy
import re
import sys
import tempfile
import unittest
from pathlib import Path

from review_packet_fixture import packet, environment_fixture
import review_packet_evidence as evidence
import agent_review


HEAD = "a" * 40


class PacketTests(unittest.TestCase):
    def test_complete_packet_passes(self):
        evidence.validate_packet(packet(HEAD), HEAD, "demo")

    def active_portability(self):
        cases = [{"id": "DemoGap/" + name, "subject": "DemoGap", "name": name, "expect": kind, "expected_exit": rc,
                  "exit_status": rc, "declared_command": ["python3", "{analyzer}", "{output}", "{fixtures}"],
                  "command": ["python3", "/clean/analyzer.py", "/scratch/output", "/clean/fixture.json"],
                  "diagnostics": [diagnostic], "matched_diagnostics": [diagnostic], "status": "pass"}
                 for name, kind, rc, diagnostic in (("complete", "accept", 0, "accepted"),
                                                    ("missing", "refuse", 1, "missing event"))]
        return {"schema_version": 1, "project": "demo", "base": "b" * 40, "review_head": HEAD,
                "status": "pass", "reason": "affected_runtime_inputs", "trigger_paths": ["projects/demo/scripts/analyzer.py"],
                "subjects": ["DemoGap"], "case_ids": [case["id"] for case in cases], "cases": cases,
                "errors": [], "captures": "unresolved"}

    def test_portability_acceptance_and_refusal_results_are_accepted(self):
        evidence.validate_packet(packet(HEAD, portability=self.active_portability()), HEAD)

    def test_portability_cannot_omit_or_hide_failed_and_unrun_cases(self):
        base = self.active_portability()
        mutations = []
        for key, value in (("exit_status", None), ("exit_status", 7), ("exit_status", True),
                           ("status", "not-run"), ("matched_diagnostics", []), ("command", [])):
            changed = copy.deepcopy(base)
            changed["cases"][0][key] = value
            mutations.append(changed)
        changed = copy.deepcopy(base)
        changed["cases"].pop()
        mutations.append(changed)
        for value in mutations:
            with self.subTest(value=value), self.assertRaisesRegex(evidence.PacketError, "Runtime Analyzer Portability"):
                evidence.validate_packet(packet(HEAD, portability=value), HEAD)

    def test_portability_must_match_range_and_cannot_resolve_live_captures(self):
        for key, value in (("review_head", "c" * 40), ("base", "c" * 40), ("project", "another_demo"),
                           ("captures", "resolved"), ("status", "not-required")):
            changed = self.active_portability()
            changed[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(evidence.PacketError, "Runtime Analyzer Portability"):
                evidence.validate_packet(packet(HEAD, portability=changed), HEAD)

    def test_portability_missing_unrun_or_failed_outer_command_blocks_handoff(self):
        for status in (None, 1):
            with self.subTest(status=status), self.assertRaisesRegex(agent_review.UserError, "Runtime Analyzer Portability"):
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    (root / "packet.md").write_text(packet(HEAD, statuses={"runtime-portability": status}))
                    agent_review.validate_packet(root, "packet.md", HEAD, "demo")
        value = packet(HEAD).replace("### Runtime Analyzer Portability", "### Missing Portability")
        with self.assertRaisesRegex(evidence.PacketError, "Runtime Analyzer Portability"):
            evidence.validate_packet(value, HEAD)

    def test_portability_command_cannot_substitute_different_range(self):
        value = packet(HEAD).replace("--base " + "b" * 40, "--base " + "c" * 40)
        with self.assertRaisesRegex(evidence.PacketError, "Runtime Analyzer Portability.*canonical command"):
            evidence.validate_packet(value, HEAD)

    def test_reused_state_packet_is_revalidated(self):
        with tempfile.TemporaryDirectory(prefix="packet-reuse-") as scratch:
            root = Path(scratch)
            (root / "packet.md").write_text(packet(HEAD, statuses={"project-docs-check": 2}))
            state = {"packet": "packet.md", "review_head": HEAD, "project": "demo"}
            with self.assertRaisesRegex(agent_review.UserError, "Project Docs Gate"):
                agent_review.ensure_packet(root, state, argparse.Namespace(packet=None, generate_packet=False))

    def test_every_required_gate_failure_is_rejected(self):
        for name in evidence.GATES:
            with self.subTest(name=name), self.assertRaisesRegex(evidence.PacketError, evidence.GATES[name]):
                evidence.validate_packet(packet(HEAD, statuses={name: 7}), HEAD)

    def test_all_failures_are_reported_not_only_first(self):
        with self.assertRaises(evidence.PacketError) as result:
            evidence.validate_packet(packet(HEAD, statuses={name: 3 for name in evidence.GATES}), HEAD)
        for title in evidence.GATES.values():
            self.assertIn(title, str(result.exception))

    def test_unrun_gates_never_count_as_passed(self):
        for name in evidence.GATES:
            with self.subTest(name=name), self.assertRaisesRegex(evidence.PacketError, "was not run"):
                evidence.validate_packet(packet(HEAD, statuses={name: None}), HEAD)

    def test_failed_preparation_and_supporting_evidence_are_explicit(self):
        for name in evidence.SUPPORTING:
            with self.subTest(name=name), self.assertRaisesRegex(evidence.PacketError, evidence.SUPPORTING[name]):
                evidence.validate_packet(packet(HEAD, statuses={name: 1}), HEAD)

    def test_summary_cannot_relabel_failed_process_section(self):
        value = packet(HEAD, statuses={"project-process-check": 9})
        value = value.replace('"exit_status": 9', '"exit_status": 0')
        with self.assertRaisesRegex(evidence.PacketError, "disagrees with Project Process Gate"):
            evidence.validate_packet(value, HEAD)

    def test_gate_state_must_match_reviewed_sha(self):
        value = packet(HEAD).replace(f"State: `review_head {HEAD}`", f"State: `review_head {'b' * 40}`", 2)
        with self.assertRaisesRegex(evidence.PacketError, "does not match review head"):
            evidence.validate_packet(value, HEAD)

    def test_summary_sha_must_match(self):
        prefix, summary = packet(HEAD).split("## Required Gate Summary")
        value = prefix + "## Required Gate Summary" + summary.replace('"review_head": "' + HEAD, '"review_head": "' + "b" * 40, 1)
        with self.assertRaisesRegex(evidence.PacketError, "does not match review head"):
            evidence.validate_packet(value, HEAD)

    def test_packet_subject_must_match_state(self):
        with self.assertRaisesRegex(evidence.PacketError, "project does not match"):
            evidence.validate_packet(packet(HEAD), HEAD, "another_demo")

    def test_nested_output_cannot_forge_gate_headers_or_status(self):
        forged = "```sh\ntrue\n```\n### Project Process Gate\nExit status: `0`\n"
        evidence.validate_packet(packet(HEAD, verify_output=forged), HEAD)
        with self.assertRaisesRegex(evidence.PacketError, "Project Process Gate"):
            evidence.validate_packet(packet(HEAD, verify_output=forged, statuses={"project-process-check": 2}), HEAD)

    def test_duplicate_or_missing_gate_sections_are_refused(self):
        value = packet(HEAD)
        with self.assertRaisesRegex(evidence.PacketError, "exactly one Project Docs Gate"):
            evidence.validate_packet(value + "\n### Project Docs Gate\n", HEAD)
        with self.assertRaisesRegex(evidence.PacketError, "exactly one Project Docs Gate"):
            evidence.validate_packet(value.replace("### Project Docs Gate", "### Missing Docs"), HEAD)

    def test_duplicate_summary_records_are_refused(self):
        value = packet(HEAD).replace('"name": "project-docs-check"', '"name": "project-process-check"')
        with self.assertRaisesRegex(evidence.PacketError, "duplicate terminal gate"):
            evidence.validate_packet(value, HEAD)

    def test_duplicate_json_fields_cannot_hide_a_conflicting_value(self):
        value = packet(HEAD).replace('"exit_status": 0', '"exit_status": 7, "exit_status": 0', 1)
        with self.assertRaisesRegex(evidence.PacketError, "duplicate JSON evidence field"):
            evidence.validate_packet(value, HEAD)

    def test_wrong_gate_command_is_not_a_canonical_gate(self):
        with self.assertRaisesRegex(evidence.PacketError, "canonical command"):
            evidence.validate_packet(packet(HEAD, verify_command="true"), HEAD)

    def test_stale_terminal_failure_list_is_refused(self):
        value = packet(HEAD).replace('"failures": [],\n  "status"', '"failures": ["stale failure"],\n  "status"')
        with self.assertRaisesRegex(evidence.PacketError, "failure categories disagree"):
            evidence.validate_packet(value, HEAD)

    def test_terminal_pass_cannot_hide_failed_prerequisite(self):
        env = environment_fixture()
        env.update(status="fail", failures=["missing reference"])
        with self.assertRaisesRegex(evidence.PacketError, "missing reference"):
            evidence.validate_packet(packet(HEAD, environment=env), HEAD)

    def test_empty_or_incomplete_environment_cannot_pass(self):
        for group in ("tools", "inputs"):
            env = environment_fixture()
            env[group] = {}
            with self.subTest(group=group), self.assertRaisesRegex(evidence.PacketError, "complete.*metadata"):
                evidence.validate_packet(packet(HEAD, environment=env), HEAD)

    def test_tool_or_fixture_metadata_cannot_claim_false_readiness(self):
        for group, name, field, value in (("tools", "assembler", "sha256", "unknown"),
                                        ("tools", "make", "path", "relative/tool"),
                                        ("inputs", "reference", "size", 0),
                                        ("inputs", "source", "size", True),
                                        ("inputs", "reference", "status", "missing_or_empty")):
            env = environment_fixture()
            env[group][name][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(evidence.PacketError):
                evidence.validate_packet(packet(HEAD, environment=env), HEAD)

    def test_gate_command_must_use_recorded_make_tool(self):
        with self.assertRaisesRegex(evidence.PacketError, "recorded make tool"):
            evidence.validate_packet(packet(HEAD, verify_command="true project-verify PROJECT=demo"), HEAD)

    def test_supporting_commands_cannot_be_replaced_by_no_ops(self):
        for name in evidence.SUPPORTING:
            value = packet(HEAD)
            _, record = evidence.gate_evidence(value, name)
            value = value.replace(record["command"], "true")
            with self.subTest(name=name), self.assertRaisesRegex(evidence.PacketError, "canonical command"):
                evidence.validate_packet(value, HEAD)

    def test_every_command_requires_captured_output(self):
        for title in ("Build and Fixture Prerequisites", *evidence.COMMANDS.values()):
            value = packet(HEAD)
            body = evidence.section(value, title, 3)
            stripped = re.sub(r"Output:\n\n(`{3,})text\n.*?\n\1\n", "", body, flags=re.S)
            self.assertNotEqual(body, stripped)
            with self.subTest(title=title), self.assertRaisesRegex(evidence.PacketError, "text evidence block"):
                evidence.validate_packet(value.replace(body, stripped), HEAD)

    def test_duplicate_outputs_are_refused_but_empty_output_is_valid(self):
        evidence.validate_packet(packet(HEAD, verify_output=""), HEAD)
        value = packet(HEAD).replace("Verification complete\n```", "Verification complete\n```\n\n```text\nextra\n```", 1)
        with self.assertRaisesRegex(evidence.PacketError, "exactly one text evidence block"):
            evidence.validate_packet(value, HEAD)

    def test_assembler_metadata_and_build_commands_must_agree(self):
        value = packet(HEAD).replace("XASM_BIN=xasm", "XASM_BIN=/unexpected/bin/assembler")
        with self.assertRaisesRegex(evidence.PacketError, "recorded assembler"):
            evidence.validate_packet(value, HEAD)

    def test_missing_or_duplicate_assembler_assignment_is_refused(self):
        for replacement in ("", "XASM_BIN=xasm XASM_BIN=xasm "):
            value = packet(HEAD).replace("XASM_BIN=xasm ", replacement)
            with self.subTest(replacement=replacement), self.assertRaises(evidence.PacketError):
                evidence.validate_packet(value, HEAD)

    def test_cache_preparation_cannot_enable_authored_queue_writes(self):
        value = packet(HEAD).replace("PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=0", "PROJECT_PASS_PREP_WRITE_RAW_RAM_REVIEW=1")
        with self.assertRaisesRegex(evidence.PacketError, "preserve the authored"):
            evidence.validate_packet(value, HEAD)

    def test_reconciliation_cannot_be_omitted_or_disabled(self):
        for replacement in ("", "PROJECT_PASS_PREP_CHECK_RAW_RAM_REVIEW=0 "):
            value = packet(HEAD).replace("PROJECT_PASS_PREP_CHECK_RAW_RAM_REVIEW=1 ", replacement)
            with self.subTest(replacement=replacement), self.assertRaisesRegex(evidence.PacketError, "check closeout reconciliation"):
                evidence.validate_packet(value, HEAD)

    def test_packet_next_pass_cannot_run_another_unchecked_prep(self):
        value = packet(HEAD).replace("PROJECT_NEXT_PASS_AUTO_PREP=0", "PROJECT_NEXT_PASS_AUTO_PREP=1")
        with self.assertRaisesRegex(evidence.PacketError, "prepared cache"):
            evidence.validate_packet(value, HEAD)

    def test_older_packets_require_regeneration(self):
        for version in (1, 2):
            value = packet(HEAD).replace('"schema_version": 3', f'"schema_version": {version}')
            with self.subTest(version=version), self.assertRaisesRegex(evidence.PacketError, "summary schema"):
                evidence.validate_packet(value, HEAD)

    def test_supporting_document_inputs_must_match_context(self):
        value = packet(HEAD).replace("scripts/proof_debt.py docs crosswalk", "scripts/proof_debt.py wrong crosswalk")
        with self.assertRaisesRegex(evidence.PacketError, "Proof Debt Signals.*canonical command"):
            evidence.validate_packet(value, HEAD)

    def test_changed_worktree_invalidates_even_zero_exit_gates(self):
        with self.assertRaisesRegex(evidence.PacketError, "worktree changed"):
            evidence.validate_packet(packet(HEAD, state_integrity="fail"), HEAD)

    def test_legacy_packet_without_terminal_summary_is_incomplete(self):
        with self.assertRaisesRegex(evidence.PacketError, "Required Gate Summary"):
            evidence.validate_packet(packet(HEAD).split("## Required Gate Summary")[0], HEAD)

    def test_environment_distinguishes_missing_and_mismatched_inputs(self):
        with tempfile.TemporaryDirectory(prefix="packet-input-") as scratch:
            source, reference = Path(scratch) / "Demo.asm", Path(scratch) / "demo.nes"
            source.write_text("RTS\n")
            reference.write_bytes(b"synthetic reference")
            result = evidence.environment(source, reference, "make", "xasm")
            self.assertEqual(result["status"], "pass")
            self.assertTrue(result["tools"]["assembler"]["sha256"])
            result = evidence.environment(source, reference, "make", "xasm", "0" * 64, "0" * 64)
            self.assertEqual(len(result["failures"]), 2)
            reference.unlink()
            result = evidence.environment(source, reference, "missing_make_fixture", "missing_assembler_fixture")
            self.assertEqual(len(result["failures"]), 3)

    def test_identical_version_text_does_not_hide_different_tool_bytes(self):
        with tempfile.TemporaryDirectory(prefix="packet-tools-") as scratch:
            source, reference = Path(scratch) / "Demo.asm", Path(scratch) / "demo.nes"
            source.write_text("RTS\n")
            reference.write_bytes(b"synthetic reference")
            first, second = Path(scratch) / "first", Path(scratch) / "second"
            for path, comment in ((first, "first"), (second, "second")):
                path.write_text(f'#!/bin/sh\n# {comment}\necho "assembler 1.0"\n')
                path.chmod(0o755)
            result = evidence.environment(source, reference, "make", str(second), evidence.digest(first))
            self.assertEqual(result["failures"], ["assembler SHA-256 mismatch against supplied expectation"])


if __name__ == "__main__":
    unittest.main()
