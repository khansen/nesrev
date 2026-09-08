#!/usr/bin/env python3
"""Typed policy, provenance, freshness and standalone-production controls."""

import copy
import csv
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import analysis_bundle as analysis
import branch_literals as branch
import analysis_prefix_compare as prefix
import kpi_ratchet_calibrate as calibration


class BranchLiterals(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="nesrev-branch-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.cwd = os.getcwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, self.cwd)
        self.source = self.root / "input.asm"
        self.source.write_text(".ORG $C000\nStart: BNE $+2\n RTS\n")
        self.policy = self.root / "kpis.conf"
        self.policy.write_text("MAX_ACTIVE_BRANCH_LITERALS=1\n")
        self.directory = self.root / "analysis"
        self.directory.mkdir()
        self.path = self.directory / "bundle.json"
        self.real_xasm = analysis.executable()

    def produce(self, profile="instructions-v1"):
        context = {"profile": profile, "source": str(self.source), "source_argument": str(self.source),
                   "policies": [analysis.fingerprint(self.policy)], "config": None, "project": None,
                   "rom_range": None, "cpu_base": None}
        if profile != "instructions-v1":
            context.update(config=str(self.policy), project="synthetic", rom_range="$C000-$FFFF", cpu_base="$C000")
        analysis.write_json(self.directory / "context.json", context)
        self.assertEqual(analysis.produce(self.directory, self.source, self.root / "out.bin"), 0)
        return analysis.Bundle(self.path, self.source)

    def run_cli(self, mode, *args, supplied=True, env=None):
        names = {"kpi": "branch_literal_kpi.sh", "sites": "branch_literal_sites.sh",
                 "check": "branch_literal_sites_check.sh"}
        environment = dict(os.environ)
        environment.pop("NESREV_ANALYSIS_BUNDLE", None)
        if supplied:
            environment["NESREV_ANALYSIS_BUNDLE"] = str(self.path)
        environment.update(env or {})
        return subprocess.run(["bash", str(ROOT / "scripts" / names[mode]), str(self.source),
                               *map(str, args)], env=environment, capture_output=True)

    def test_policy_covers_emitted_uses_not_text_lines(self):
        self.source.write_text('''MACRO SKIP amount
 BNE $+amount
ENDM
.ORG $C000
DELTA .EQU 2
Start: bne ($ + $02) : BEQ $+%10
 BCC $-0
 JMP $+3
 LDA $+3
 SKIP 2
 REPT 2
  BNE $+2
 ENDM
 IF 0
  BNE $+99
 ENDIF
 BNE $+DELTA
 BNE $+(1+1)
 BNE $-(-2)
 LDA #<($+2)
 LDA $+2,X
 JMP [$+3]
 ASL A
 ASL
 LSR
 ROL
 ROR
 RTS
.ORG 0
 LDA $+2
''')
        shared = self.produce()
        sites = branch.rows(shared)
        self.assertEqual(len(sites), 9)
        self.assertEqual([r["mnemonic"] for r in sites], ["BNE", "BEQ", "BCC", "JMP", "LDA",
                                                         "BNE", "BNE", "BNE", "LDA"])
        self.assertEqual(sites[0]["operand"], "($ + $02)")
        self.assertEqual(sites[0]["source"], "bne ($ + $02)")
        self.assertEqual(sites[0]["enclosing_label"], "Start")
        self.assertEqual(sites[5]["operand"], "$+amount")
        tree = json.loads(sites[5]["expression"])
        self.assertEqual(tree["children"][1]["source"]["text"], "2")
        self.assertNotEqual(sites[5]["line"], sites[5]["use_line"])
        self.assertEqual(sites[6]["source"], sites[7]["source"])
        self.assertNotEqual(sites[6]["origin_id"], sites[7]["origin_id"])
        self.assertNotIn(str(self.root), branch.csv_bytes(sites).decode())
        run = self.run_cli("kpi")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(b"strict_active_branch_literals=9", run.stdout)
        emitted = self.run_cli("sites")
        self.assertEqual(emitted.returncode, 0, emitted.stderr)
        self.assertEqual(emitted.stdout, branch.csv_bytes(sites))

    def test_all_profiles_and_strictness(self):
        for profile in analysis.PROFILES:
            with self.subTest(profile=profile):
                if self.path.exists():
                    shutil.rmtree(self.directory)
                    self.directory.mkdir()
                shared = self.produce(profile)
                self.assertEqual("--Werror=unused-equ" in shared.data["argv"],
                                 profile in analysis.STRICT_PROFILES)
                if profile == analysis.PROFILE:
                    with self.assertRaisesRegex(analysis.BundleError, "lacks required artifact"):
                        branch.rows(shared)
                else:
                    self.assertEqual(len(branch.rows(shared)), 1)
                for name in shared.data["outputs"]:
                    if name != "binary":
                        shared.load(name)

    def test_empty_complete_stream(self):
        self.source.write_text(".ORG $C000\n.DB 1,2,3\n")
        shared = self.produce()
        self.assertEqual(branch.rows(shared), [])
        run = self.run_cli("kpi", self.policy)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(b"strict_active_branch_literals=0", run.stdout)

    def test_standalone_once_and_supplied_refusal_no_fallback(self):
        spy = self.root / "xasm"
        shutil.copyfile(ROOT / "tests/fixtures/analysis_count_xasm.py", spy)
        spy.chmod(0o755)
        calls = self.root / "calls.jsonl"
        env = {"XASM_BIN": str(spy), "BUNDLE_TEST_REAL_XASM": self.real_xasm,
               "BUNDLE_TEST_CALLS": str(calls)}
        for mode, args in (("kpi", [self.policy]), ("sites", [])):
            run = self.run_cli(mode, *args, supplied=False, env=env)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertTrue(calls.exists(), (run.stdout, run.stderr, env))
            self.assertEqual(len(calls.read_text().splitlines()), 1)
            calls.unlink()
        with patch.dict(os.environ, env):
            shared = self.produce()
        calls.unlink()
        reused = self.run_cli("kpi", self.policy, env=env)
        self.assertEqual(reused.returncode, 0, reused.stderr)
        self.assertFalse(calls.exists())
        for path in ("", str(self.root / "missing.json"), str(self.path)):
            if path == str(self.path):
                Path(shared.data["outputs"]["instructions"]["path"]).write_text("{")
            run = self.run_cli("kpi", self.policy, env=dict(env, NESREV_ANALYSIS_BUNDLE=path))
            self.assertEqual(run.returncode, 65, run.stderr)
            self.assertIn(b"refused:", run.stderr)
            self.assertNotIn(b"strict_active_branch_literals=", run.stdout)
            self.assertFalse(calls.exists())

    def test_threshold_failure_is_distinct_from_refusal(self):
        self.policy.write_text("MAX_ACTIVE_BRANCH_LITERALS=0\n")
        self.produce()
        run = self.run_cli("kpi", self.policy)
        self.assertEqual(run.returncode, 68, run.stderr)
        self.assertIn(b"strict_active_branch_literals=1", run.stdout)
        self.policy.write_text("MAX_ACTIVE_BRANCH_LITERALS=1\n")
        run = self.run_cli("kpi", self.policy)
        self.assertEqual(run.returncode, 65, run.stderr)
        self.assertNotIn(b"strict_active_branch_literals=", run.stdout)

    def test_malformed_nonmatching_records_are_not_zero(self):
        self.source.write_text(".ORG $C000\n RTS\n")
        shared = self.produce()
        original = shared.load("instructions")
        for mutate in (lambda d: d.pop("version"), lambda d: d.pop("records"),
                       lambda d: d["records"][0].pop("expression"),
                       lambda d: d["records"][0].update(addressing_mode="other"),
                       lambda d: d["records"][0].update(expression={"kind": "integer"}),
                       lambda d: d["records"][0]["source"]["span"].update(line=0)):
            altered = copy.deepcopy(original)
            mutate(altered)
            with self.assertRaises(ValueError):
                analysis.check_schema("instructions", altered)

    def test_csv_atomic_replacement_and_late_refusal(self):
        shared = self.produce()
        target = self.root / "sites.csv"
        target.write_bytes(b"old ledger\n")
        data = branch.csv_bytes(branch.rows(shared))
        with patch.object(shared, "validate", side_effect=analysis.BundleError("late change")):
            with self.assertRaisesRegex(analysis.BundleError, "late change"):
                branch.write_csv(target, data, shared)
        self.assertEqual(target.read_bytes(), b"old ledger\n")
        run = self.run_cli("sites", target)
        self.assertEqual(run.returncode, 0, run.stderr)
        checked = self.run_cli("check", target)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertEqual(target.read_bytes(), data)
        self.source.write_text(self.source.read_text().replace("$+2", "$+3"))
        refused = self.run_cli("sites", target)
        self.assertEqual(refused.returncode, 65, refused.stderr)
        self.assertEqual(target.read_bytes(), data)

    def test_prefix_comparison_preserves_length_and_failure_semantics(self):
        shared = self.produce()
        actual = Path(shared.data["outputs"]["binary"]["path"]).read_bytes()
        reference = self.root / "reference.bin"
        for expected in (actual, actual[:1], actual + b"extra", b"", b"\xea"):
            with self.subTest(expected=expected):
                reference.write_bytes(expected)
                result = prefix.compare(shared, reference)
                size = min(len(actual), len(expected))
                self.assertEqual(result["compared_length"], size)
                self.assertEqual(result["match"], actual[:size] == expected[:size])
        reference.unlink()
        with self.assertRaises(FileNotFoundError):
            prefix.compare(shared, reference)
        reference.write_bytes(actual)
        self.source.write_text(self.source.read_text().replace("$+2", "$+3"))
        with self.assertRaisesRegex(analysis.BundleError, "changed input"):
            prefix.compare(shared, reference)

    def test_calibration_revalidates_source_and_policy_before_publication(self):
        original_source = self.source.read_bytes()
        measurement = (("branch_literal_kpi.sh", "strict_active_branch_literals", "MAX_ACTIVE_BRANCH_LITERALS"),)
        for changed in (None, self.source, self.policy):
            with self.subTest(changed=changed):
                self.source.write_bytes(original_source)
                self.policy.write_text("# Intake calibration pending.\nMAX_ACTIVE_BRANCH_LITERALS=9\n")
                before = self.policy.read_bytes()
                actual_measure = calibration.measure
                def measure(*args):
                    values = actual_measure(*args)
                    if changed is not None:
                        changed.write_bytes(changed.read_bytes() + b"; changed\n")
                    return values
                with patch.object(calibration, "MEASUREMENTS", measurement), \
                        patch.object(calibration, "measure", side_effect=measure):
                    rc = calibration.main([str(self.source), str(self.policy)])
                self.assertEqual(rc, 0 if changed is None else 1)
                if changed is None:
                    self.assertIn("MAX_ACTIVE_BRANCH_LITERALS=1", self.policy.read_text())
                    self.assertNotIn(calibration.PENDING_MARKER, self.policy.read_text())
                else:
                    self.assertEqual(self.policy.read_bytes(), before + (b"; changed\n" if changed == self.policy else b""))

    def test_include_identity_repeated_uses_and_checkout_portability(self):
        source = '.ORG $C000\n.INCSRC "left/part.inc"\n.INCSRC "right/part.inc"\n.INCSRC "left/part.inc"\n'
        self.source.write_text(source)
        for name, text in (("left", " BNE $+2\n"), ("right", " BEQ $+$02\n")):
            (self.root / name).mkdir()
            (self.root / name / "part.inc").write_text(text)
        shared = self.produce()
        records = branch.rows(shared)
        self.assertEqual([r["source_file"] for r in records], ["left/part.inc", "right/part.inc", "left/part.inc"])
        self.assertNotEqual(records[0]["origin_id"], records[2]["origin_id"])
        self.assertNotEqual(records[0]["output_offset"], records[2]["output_offset"])
        relocated = self.root / "relocated"
        relocated.mkdir()
        for name in ("left", "right"):
            shutil.copytree(self.root / name, relocated / name)
        copied = relocated / "input.asm"
        copied.write_text(source)
        analysis.prepare_source(relocated, copied, [])
        self.assertEqual(analysis.produce(relocated, copied, relocated / "out.bin"), 0)
        other = analysis.Bundle(relocated / "bundle.json", copied)
        self.assertEqual(branch.csv_bytes(records), branch.csv_bytes(branch.rows(other)))


if __name__ == "__main__":
    unittest.main()
