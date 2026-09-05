import json
import argparse
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
        value = packet(HEAD).replace('"review_head": "' + HEAD, '"review_head": "' + "b" * 40, 1)
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
