#!/usr/bin/env python3
"""Advisory findings and operational refusals with real synthetic assemblies."""

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
import analysis_bundle as bundle


PAIR = """ZP_TestPtrLo .EQU $10
ZP_TestPtrHi .EQU $11
.ORG $C000
ReadPair:
  LDY #0
  LDA RawAddresses,Y
  STA ZP_TestPtrLo
  LDA RawAddresses+1,Y
  STA ZP_TestPtrHi
  ; overwrite control
  LDA [ZP_TestPtrLo],Y
  RTS
RawAddresses: .DB $40,$C0,$42,$C0,$44,$C0,$46,$C0,$48,$C0,$4A,$C0
.ORG $C040
Payload: .DB 1,2,3,4,5,6,7,8,9,10,11,12
"""

STRUCT = """ZP_TestPtrLo .EQU $10
StructAlias .EQU RawAddresses
.ORG $C000
CopyBlock:
  LDX #11
@@copy:
  LDA StructAlias,X
  STA ZP_TestPtrLo,X
  DEX
  BPL @@copy
ReadBlock:
  LDY #0
  ; overwrite control
  LDA [ZP_TestPtrLo],Y
  RTS
RawAddresses: .DB $40,$C0,$4A,$C0,$42,$C0,$48,$C0,$44,$C0,$46,$C0
.ORG $C040
Payload: .DB 1,2,3,4,5,6,7,8,9,10,11,12
"""

# Both pointer bytes are replaced before the indirect read. The legacy
# matchers still match, although that read cannot consume the table's pointer.
OVERWRITE = "LDA #0\n  STA ZP_TestPtrLo\n  STA ZP_TestPtrHi"


class AdvisoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="nesrev-pointer-advisory-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "input.asm"
        self.env = {k: v for k, v in os.environ.items() if k != "NESREV_ANALYSIS_BUNDLE"}

    def run_audit(self, descriptor=None):
        env = dict(self.env)
        if descriptor is not None:
            env["NESREV_ANALYSIS_BUNDLE"] = str(descriptor)
        return subprocess.run(
            [sys.executable, str(ROOT / "scripts/embedded_pointer_audit.py"), str(self.source)],
            env=env, capture_output=True, text=True,
        )

    def produce(self, name="analysis"):
        directory = self.root / name
        directory.mkdir()
        config = self.root / "project.conf"
        config.write_text('NESREV_RECOVERY_STATUS="none"\n')
        context = {
            "profile": bundle.PROFILE, "project": "synthetic", "config": str(config),
            "source": str(self.source), "source_argument": str(self.source),
            "rom_range": "$C000-$FFFF", "cpu_base": "$C000",
            "policies": [bundle.fingerprint(config)],
        }
        bundle.write_json(directory / "context.json", context)
        with patch.dict(os.environ, self.env, clear=True):
            self.assertEqual(bundle.produce(str(directory), str(self.source), str(directory / "out.bin")), 0)
        return directory / "bundle.json"

    def assert_advisory(self, result):
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("embedded_pointer_heuristic_matches=1\n", result.stdout)
        self.assertIn("ADVISORY:", result.stderr)
        self.assertIn("RawAddresses bank=0", result.stderr)
        self.assertIn("pointer flow unproven", result.stderr)
        self.assertNotRegex(result.stdout + result.stderr, r"confirmed|consumer_proof|FAIL:|audit passed")

    def test_genuine_and_overwritten_matches_standalone_and_bundle(self):
        for kind, source in (("pair", PAIR), ("struct", STRUCT)):
            for overwritten in (False, True):
                with self.subTest(kind=kind, overwritten=overwritten):
                    overwrite = OVERWRITE.replace("ZP_TestPtrHi", "ZP_TestPtrLo+1")
                    self.source.write_text(source.replace("; overwrite control", overwrite if overwritten else ""))
                    plain = self.run_audit()
                    self.assert_advisory(plain)
                    descriptor = self.produce(f"{kind}-{overwritten}")
                    reused = self.run_audit(descriptor)
                    self.assert_advisory(reused)
                    self.assertEqual((plain.stdout, plain.stderr), (reused.stdout, reused.stderr))

    def test_discovery_without_consumer_match_remains_visible(self):
        for kind, source, counter in (("pair", PAIR, "raw_runs_strong"),
                                      ("struct", STRUCT, "struct_candidates")):
            with self.subTest(kind=kind):
                self.source.write_text(source.replace("LDA [ZP_TestPtrLo],Y", "NOP"))
                result = self.run_audit()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(f"embedded_pointer_{counter}=1\n", result.stdout)
                self.assertIn("embedded_pointer_heuristic_matches=0\n", result.stdout)
                self.assertNotIn("ADVISORY:", result.stderr)
                reused = self.run_audit(self.produce(kind))
                self.assertEqual((reused.returncode, reused.stdout, reused.stderr),
                                 (result.returncode, result.stdout, result.stderr))

    def test_noninteger_min_run_is_an_analysis_refusal(self):
        self.source.write_text(PAIR)
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts/embedded_pointer_audit.py"),
             str(self.source), "not-an-integer"],
            env=self.env, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 65, result.stderr)
        self.assertIn("analysis refused:", result.stderr)
        self.assertNotIn("embedded_pointer_heuristic_matches=", result.stdout)

    def test_empty_discovery_is_not_a_completeness_claim(self):
        self.source.write_text(".ORG $C000\nReset: RTS\n")
        result = self.run_audit()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("embedded_pointer_heuristic_matches=0\n", result.stdout)
        self.assertIn("advisory", result.stdout)
        self.assertNotRegex(result.stdout, r"confirmed|audit passed")

    def test_detail_limit_keeps_total_and_unproven_omission_notice(self):
        pieces = ["ZP_TestPtrLo .EQU $10\nZP_TestPtrHi .EQU $11\n.ORG $C000\n"]
        body = PAIR.split("ReadPair:\n", 1)[1].split(".ORG $C040", 1)[0]
        for index in range(21):
            pieces.append(f"ReadPair{index}:\n" + body.replace("RawAddresses", f"RawAddresses{index}"))
        self.source.write_text("".join(pieces))
        result = self.run_audit()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("embedded_pointer_heuristic_matches=21\n", result.stdout)
        self.assertEqual(result.stderr.count("ADVISORY: raw pointer-shaped bytes"), 20)
        self.assertIn("1 additional heuristic matches omitted; pointer flow unproven", result.stderr)

    def test_stale_and_malformed_supplied_evidence_refuse_without_fallback(self):
        spy = self.root / "xasm"
        shutil.copyfile(ROOT / "tests/fixtures/analysis_count_xasm.py", spy)
        spy.chmod(0o755)
        calls = self.root / "calls.jsonl"
        self.env.update(XASM_BIN=str(spy), BUNDLE_TEST_REAL_XASM=bundle.executable(),
                        BUNDLE_TEST_CALLS=str(calls))
        self.source.write_text(PAIR)
        descriptor = self.produce()
        self.assertEqual(len(calls.read_text().splitlines()), 1)
        calls.unlink()
        data = json.loads(descriptor.read_text())
        listing = Path(data["outputs"]["listing"]["path"])
        original_listing = listing.read_bytes()
        for fault in ("source", "listing", "descriptor", "missing", "empty"):
            with self.subTest(fault=fault):
                supplied = descriptor
                original_descriptor = descriptor.read_bytes()
                if fault == "source":
                    self.source.write_text(PAIR + "; changed\n")
                elif fault == "listing":
                    listing.write_text("{")
                elif fault == "descriptor":
                    descriptor.write_text("{}")
                elif fault == "missing":
                    supplied = self.root / "missing.json"
                else:
                    supplied = ""
                result = self.run_audit(supplied)
                self.assertEqual(result.returncode, 65, result.stderr)
                self.assertIn("analysis refused:", result.stderr)
                self.assertNotIn("embedded_pointer_heuristic_matches=", result.stdout)
                self.assertFalse(calls.exists(), "invalid supplied evidence must not trigger assembly")
                self.source.write_text(PAIR)
                listing.write_bytes(original_listing)
                descriptor.write_bytes(original_descriptor)

    def test_assembly_error_is_not_report_only(self):
        self.source.write_text(".ORG $C000\nReset: LDA MissingTarget\n")
        result = self.run_audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("xasm analysis failed", result.stderr)
        self.assertIn("MissingTarget", result.stderr)
        self.assertNotIn("embedded_pointer_heuristic_matches=", result.stdout)

    def test_maturity_exposes_advisory_and_preserves_independent_body_gate(self):
        # Reuse the complete synthetic maturity setup, with real gates. All
        # project writes stay under this test's temporary working directory.
        source = PAIR.replace("ReadPair", "Reset")
        source = "ZP_FrameOamCursor .EQU $3F\n" + source.replace(
            "  LDY #0", "  LDA ZP_FrameOamCursor\n  LDY #0")
        source = source.replace("RawAddresses: .DB", "; Format: Six little-endian address pairs.\n"
                                "; Used by: Reset.\nRawAddresses: .DB")
        source = source.replace("Payload: .DB", "; Format: Twelve one-byte values.\n"
                                "; Used by: Reset through an indirect pointer.\nPayload: .DB")
        self.source.write_text(source)
        env = dict(self.env, REPO_ROOT=str(ROOT), NESREV_TEST_TMPDIR=str(self.root))
        setup = '''set -euo pipefail
source "$REPO_ROOT/tests/shell/lib.sh"
source "$REPO_ROOT/tests/shell/cases/semantic_claims_test.sh"
_make_sc_project synthetic 1
_write_valid_claim synthetic
cp input.asm projects/synthetic/asm/synthetic.asm
_run_maturity synthetic
'''
        result = subprocess.run(["bash", "-c", setup], cwd=self.root, env=env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("embedded_pointer_heuristic_matches=1", result.stdout)
        self.assertIn("ADVISORY:", result.stdout)
        self.assertIn("pointer flow unproven", result.stdout)
        self.assertIn("OK: maturity hard gates passed", result.stdout)

        # Renaming only the body and references invokes the independent
        # named-pointer-table rule, even though heuristic matches remain advisory.
        self.source.write_text(source.replace("RawAddresses", "RawPointerTable"))
        result = subprocess.run(["bash", "-c", setup], cwd=self.root, env=env,
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("embedded_pointer_heuristic_matches=1", result.stdout)
        self.assertIn("maturity gate failed: pointer-table bodies must be symbolic", result.stderr)


if __name__ == "__main__":
    unittest.main()
