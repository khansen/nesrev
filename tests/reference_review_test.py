#!/usr/bin/env python3
"""Reference evidence must remain visible across layouts and later passes."""

import csv
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import proof_debt
from reference_review import inventory_path, packet_context, planning_scope
from project_artifact_manifest import ARTIFACTS, validate


class IdentityAcknowledgementTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.paths = {name: self.root / name for name in (
            "scorecard", "crosswalk", "semantic_claims", "renames", "working_notes",
            "deferrals", "acknowledgements")}
        self.paths["scorecard"].write_text("| pass_id | notes |\n|---|---|\n| 40 | closed machinery |\n")
        self.paths["crosswalk"].write_text(
            "| Reference term | Asm symbol(s) | Confidence | Notes |\n|---|---|---|---|\n"
            "| Sprite creature | | unmapped | Match selector and graphics |\n")

    def collect(self):
        return proof_debt.collect(**self.paths, doc_root=self.root)

    def acknowledge(self, signal, **overrides):
        row = dict(signal=signal["id"], reason="Reviewed current identity evidence",
                   pass_id=signal["pass_id"], scope=signal["scope"],
                   revisit_condition="Revisit after render ownership is proven")
        row.update(overrides)
        with self.paths["acknowledgements"].open("w", newline="") as output:
            writer = csv.DictWriter(output, fieldnames=proof_debt.ACK_HEADER)
            writer.writeheader()
            writer.writerow(row)

    def test_scoped_acknowledgement_survives_unrelated_completed_passes(self):
        self.acknowledge(self.collect()[0])
        self.assertEqual(self.collect(), [])
        with self.paths["scorecard"].open("a") as output:
            output.write("| 41 | audio channel cleanup |\n")
        self.assertEqual(self.collect(), [])

    def test_changed_crosswalk_evidence_invalidates_ack_even_with_same_counts(self):
        self.acknowledge(self.collect()[0])
        self.assertEqual(self.collect(), [])
        path = self.paths["crosswalk"]
        path.write_text(path.read_text().replace("Match selector", "Selector proven; match"))
        self.assertEqual([row["id"] for row in self.collect()], ["crosswalk_unmapped"])

    def test_missing_scope_condition_or_valid_pass_cannot_suppress_identity(self):
        signal = self.collect()[0]
        for fields in ({"scope": ""}, {"scope": "different"}, {"revisit_condition": ""},
                       {"pass_id": ""}, {"pass_id": "-1"}, {"pass_id": "bogus"},
                       {"pass_id": "41"}, {"reason": ""}):
            with self.subTest(fields=fields):
                self.acknowledge(signal, **fields)
                self.assertEqual(self.collect()[0]["id"], signal["id"])

    def test_one_subject_ack_does_not_hide_another_or_changed_deferrals(self):
        self.paths["crosswalk"].write_text("")
        with self.paths["deferrals"].open("w", newline="") as output:
            writer = csv.writer(output)
            writer.writerow(["pass_id", "corridor", "subject", "kind", "deferral", "revisit_condition", "status"])
            for subject in ("creature", "pickup"):
                for pass_id in (10, 20, 30):
                    writer.writerow([pass_id, "render", subject, "static", "unresolved", "match tiles", "open"])
        signals = self.collect()
        self.assertEqual(len(signals), 2)
        self.acknowledge(signals[0])
        self.assertEqual(self.collect(), [signals[1]])
        with self.paths["deferrals"].open("a") as output:
            output.write("40,render,creature,static,unresolved,match new selector,open\n")
        self.assertEqual(len(self.collect()), 2)

    def test_migrated_nonidentity_dispositions_remain_valid(self):
        self.paths["acknowledgements"].write_text(
            "signal,reason,pass_id,scope,revisit_condition\nsemantic_claims_empty,Reviewed exceptional shape,3,,\n"
            "crosswalk_unmapped,Unscoped identity disposition,40,,\n")
        self.assertEqual(proof_debt.load_acknowledgements(self.paths["acknowledgements"]),
                         {"semantic_claims_empty"})
        self.assertEqual([row["id"] for row in self.collect()], ["crosswalk_unmapped"])

    def test_old_acknowledgement_header_requires_migration(self):
        self.paths["acknowledgements"].write_text(
            "signal,reason,pass_id\nsemantic_claims_empty,Reviewed exceptional shape,3\n")
        with self.assertRaisesRegex(ValueError, "migrate to signal,reason,pass_id,scope,revisit_condition"):
            proof_debt.load_acknowledgements(self.paths["acknowledgements"])


class InventoryContextTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.doc_root = self.root / "projects/demo/docs/reverse_engineering"
        self.crosswalk = self.root / "projects/demo/docs/crosswalk/TERMINOLOGY_CROSSWALK.md"
        self.crosswalk.parent.mkdir(parents=True)
        self.crosswalk.write_text("# Terms\nSource inventory and mappings.\n")
        self.git("init", "-q")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.commit()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True,
                              text=True).stdout.strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "Reference fixture")
        return self.git("rev-parse", "HEAD")

    def context(self, head="HEAD"):
        return packet_context(self.root, head, "demo", self.doc_root, self.crosswalk)

    def test_missing_canonical_inventory_requests_intake_or_migration(self):
        output = self.context()
        self.assertIn("crosswalk/MANUAL_TERMS.md`: not committed at reviewed head", output)
        self.assertIn("migrate existing authored docs", output)
        self.assertIn("TERMINOLOGY_CROSSWALK.md` at", output)
        self.assertNotIn("waiver", output)

    def test_inventory_evidence_comes_from_reviewed_head(self):
        old_head = self.git("rev-parse", "HEAD")
        canonical = inventory_path(self.crosswalk)
        canonical.write_text("# Inventory\nSource citations.\n")
        self.assertIn("crosswalk/MANUAL_TERMS.md`: not committed", self.context())
        inventory_head = self.commit()
        self.assertIn("crosswalk/MANUAL_TERMS.md` at", self.context(inventory_head))
        canonical.unlink()
        self.commit()
        self.assertIn("crosswalk/MANUAL_TERMS.md` at", self.context(inventory_head))
        self.assertIn("crosswalk/MANUAL_TERMS.md`: not committed", self.context(old_head))


class AcknowledgementSchemaTests(unittest.TestCase):
    def test_manifest_requires_the_canonical_five_column_header(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for artifact in ARTIFACTS:
                path = root / artifact.relative_path
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text((artifact.header or "# Evidence") + "\n")
            path = root / "inventory/proof_debt_acknowledged.csv"
            self.assertEqual(validate(root, "demo"), [])
            for header in ("signal,reason,pass_id", "signal,reason,pass_id,scope"):
                path.write_text(header + "\n")
                self.assertTrue(any("invalid header" in error for error in validate(root, "demo")),
                                f"noncanonical header was accepted: {header}")


class PlanningContextTests(unittest.TestCase):
    def test_missing_invalid_and_stale_plans_are_explicitly_unrecorded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan = root / "inventory/pass/current_pass_plan.json"
            plan.parent.mkdir(parents=True)
            self.assertIn("Not recorded", planning_scope(root, "demo", "4"))
            for value in ("{broken", "[]", json.dumps({"project": "other", "intended_pass_id": 4}),
                          json.dumps({"project": "demo", "intended_pass_id": 3}),
                          json.dumps({"project": "demo", "intended_pass_id": 4, "corridor_objective": []})):
                plan.write_text(value)
                self.assertIn("Not recorded", planning_scope(root, "demo", "4"))
            scope = "Creature selector $12; match manual picture and render record"
            plan.write_text(json.dumps({"project": "demo", "intended_pass_id": 4,
                                        "corridor_objective": {"reference_scope": scope}}))
            self.assertEqual(planning_scope(root, "demo", "4"), scope)


if __name__ == "__main__":
    unittest.main()
