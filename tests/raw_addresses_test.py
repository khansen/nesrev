#!/usr/bin/env python3
"""Raw literal policy and failure controls using real producer records."""

import copy
from contextlib import redirect_stdout
import io
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
import raw_addresses as raw


class RawAddresses(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="nesrev-raw-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        cwd = os.getcwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, cwd)
        self.source = self.root / "input.asm"
        self.source.write_text(".ORG $C000\n LDA $20\n LDA $C000\n RTS\n")
        self.policy = self.root / "kpis.conf"
        self.policy.write_text("MAX_ACTIVE_RAW_LOWADDR=1\nMAX_ACTIVE_RAW_ABSROM=1\n")
        self.directory = self.root / "analysis"
        self.directory.mkdir()
        self.path = self.directory / "bundle.json"

    def produce(self, profile="instructions-v1"):
        analysis.prepare_source(self.directory, self.source, [self.policy])
        if profile != "instructions-v1":
            context = analysis.read_json(self.directory / "context.json")
            context.update(profile=profile, config=str(self.policy), project="synthetic",
                           rom_range="$C000-$FFFF", cpu_base="$C000")
            analysis.write_json(self.directory / "context.json", context)
        self.assertEqual(analysis.produce(self.directory, self.source, self.root / "out.bin"), 0)
        return analysis.Bundle(self.path, self.source)

    def run_cli(self, policy=None, supplied=True, env=None):
        environment = dict(os.environ)
        environment.pop("NESREV_ANALYSIS_BUNDLE", None)
        if supplied:
            environment["NESREV_ANALYSIS_BUNDLE"] = str(self.path)
        environment.update(env or {})
        return subprocess.run(["bash", str(ROOT / "scripts/raw_address_kpi.sh"), str(self.source),
                               *([str(policy)] if policy is not None else [])],
                              env=environment, capture_output=True)

    def test_spelling_matrix_uses_token_not_resolved_value(self):
        cases = [("$0", True), ("$F", True), ("$00", True), ("$FF", True),
                 ("$000", True), ("$0FF", True), ("$0100", True), ("$0FFF", True),
                 ("$100", False), ("$FFF", False), ("$00002", False),
                 ("$0f", False), ("$0fff", False), ("32", False), ("%100000", False),
                 ("$20+0", False), ("-$20", False),
                 ("<$20", False), (">$2000", False), ("Address", False)]
        self.source.write_text(".ORG $C000\nAddress .EQU $20\n" +
                               "".join(f" LDA {text}\n" for text, _ in cases))
        bundle = self.produce()
        records = bundle.load("instructions")["records"]
        self.assertEqual(len(records), len(cases))
        for (spelling, expected), record in zip(cases, records):
            with self.subTest(spelling=spelling):
                self.assertEqual(raw.category(record), raw.METRICS[0] if expected else None)

    def test_rom_boundaries_and_each_store_exclusion(self):
        cases = [("LDA $BFFF", False), ("LDA $C000", True), ("LDA $FFFF", True),
                 ("LDA $c000", False), ("LDA $0C000", False),
                 ("STA $E000", False), ("STX $E000", False), ("STY $E000", False),
                 ("STA.W $E000", False), ("STX.W $E000", False), ("STY.W $E000", False),
                 ("INC $E000", True), ("DEC $E000", True), ("ASL $E000", True),
                 ("LDA $E000,X", True), ("LDA $E000,Y", True), ("STA $E000,X", False),
                 ("JMP [$E000]", True), ("JSR $E000", True), ("JMP $E000", True),
                 ("LDA #<$E000", False), ("LDA #$20", False)]
        self.source.write_text(".ORG $C000\n" + "".join(f" {text}\n" for text, _ in cases))
        bundle = self.produce()
        for (source, expected), record in zip(cases, bundle.load("instructions")["records"]):
            with self.subTest(source=source):
                self.assertEqual(raw.category(record), raw.METRICS[1] if expected else None)

    def test_modes_grouping_width_and_low_stores(self):
        cases = ["LDA $20", "LDA.W $20", "LDA $20,X", "LDA.W $20,X", "LDX $20,Y",
                 "LDA [$20,X]", "LDA [$20],Y", "JMP [$0020]", "LDA (($20))",
                 "LDA ( $20 ), X", "lda $20", "STA $20", "STX $20", "STY $20",
                 "BNE $0040"]
        self.source.write_text(".ORG 0\n" + "".join(f" {text}\n" for text in cases))
        bundle = self.produce()
        records = bundle.load("instructions")["records"]
        self.assertEqual(len(records), len(cases))
        self.assertEqual(records[0]["addressing_mode"], "zeropage")
        self.assertEqual(records[1]["addressing_mode"], "absolute")
        self.assertEqual(records[-1]["addressing_mode"], "relative")
        self.assertEqual(raw.counts(bundle), dict(zip(raw.METRICS, (len(cases), 0))))

    def test_emitted_macro_include_same_line_and_inactive_coverage(self):
        (self.root / "part.asm").write_text(" LDA $0A\n")
        self.source.write_text('''MACRO FETCH address
 LDA address
ENDM
MACRO UNUSED
 LDA $30
ENDM
.ORG $C000
Start: LDA $20 : LDA $21
 FETCH $22
 FETCH 34
 REPT 2
  FETCH $23
 ENDM
 INCLUDE "part.asm"
 INCLUDE "part.asm"
 IF 0
  LDA $24
 ENDIF
 .DB $25
 RTS
''')
        bundle = self.produce()
        records = [r for r in bundle.load("instructions")["records"] if raw.category(r)]
        self.assertEqual(len(records), 7)
        self.assertEqual(records[2]["operand_source"]["text"], "address")
        self.assertEqual(records[2]["expression"]["source"]["text"], "$22")
        self.assertEqual(len({r["origin_id"] for r in records}), 7)
        self.assertEqual(records[-1]["source"], records[-2]["source"])

    def test_complete_empty_stream(self):
        self.source.write_text(".ORG $C000\n.DB 1,2,3\n")
        bundle = self.produce()
        self.assertEqual(raw.counts(bundle), dict.fromkeys(raw.METRICS, 0))
        run = self.run_cli(self.policy)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(b"OK: raw-address KPI gate passed", run.stdout)

    def test_limits_and_invalid_policy(self):
        for text, status in (("MAX_ACTIVE_RAW_LOWADDR=0\nMAX_ACTIVE_RAW_ABSROM=0\n", 68),
                             ("MAX_ACTIVE_RAW_LOWADDR=1\nMAX_ACTIVE_RAW_ABSROM=0\n", 69),
                             ("MAX_ACTIVE_RAW_LOWADDR=1\nMAX_ACTIVE_RAW_ABSROM=1\n", 0),
                             ("MAX_ACTIVE_RAW_LOWADDR=1\n", 67),
                             ("MAX_ACTIVE_RAW_LOWADDR=-1\nMAX_ACTIVE_RAW_ABSROM=1\n", 65)):
            with self.subTest(status=status):
                if self.path.exists():
                    shutil.rmtree(self.directory)
                    self.directory.mkdir()
                self.policy.write_text(text)
                self.produce()
                run = self.run_cli(self.policy)
                self.assertEqual(run.returncode, status, run.stderr)
                if status in (0, 68, 69):
                    self.assertIn(b"strict_active_raw_lowaddr=1", run.stdout)
                    self.assertIn(b"strict_active_raw_absrom=1", run.stdout)
                else:
                    self.assertNotIn(b"strict_active_raw_", run.stdout)

    def test_standalone_once_supplied_never_assembles_or_falls_back(self):
        spy = self.root / "xasm"
        shutil.copyfile(ROOT / "tests/fixtures/analysis_count_xasm.py", spy)
        spy.chmod(0o755)
        calls = self.root / "calls.jsonl"
        env = dict(XASM_BIN=str(spy), BUNDLE_TEST_REAL_XASM=analysis.executable(),
                   BUNDLE_TEST_CALLS=str(calls))
        standalone = self.run_cli(self.policy, supplied=False, env=env)
        self.assertEqual(standalone.returncode, 0, standalone.stderr)
        self.assertEqual(len(calls.read_text().splitlines()), 1)
        with patch.dict(os.environ, env):
            shared = self.produce()
        calls.unlink()
        reused = self.run_cli(self.policy, env=env)
        self.assertEqual(reused.returncode, 0, reused.stderr)
        self.assertEqual(reused.stdout, standalone.stdout)
        self.assertFalse(calls.exists())
        for value in ("", "missing.json", str(self.path)):
            if value == str(self.path):
                Path(shared.data["outputs"]["instructions"]["path"]).write_text("{")
            run = self.run_cli(env=dict(env, NESREV_ANALYSIS_BUNDLE=value))
            self.assertEqual(run.returncode, 65, run.stderr)
            self.assertNotIn(b"strict_active_raw_", run.stdout)
            self.assertFalse(calls.exists())

    def test_schema_nonmatching_record_and_binary_guard_independently(self):
        shared = self.produce()
        document = shared.load("instructions")
        original = copy.deepcopy(shared.data)
        path = Path(shared.data["outputs"]["instructions"]["path"])
        for kind in ("schema", "source", "binary"):
            with self.subTest(kind=kind):
                changed = copy.deepcopy(document)
                record = changed["records"][-1]
                if kind == "schema":
                    del record["immediate"]
                    expected = b"immediate boolean required"
                elif kind == "source":
                    record["source"]["span"]["file"] = str(self.root / "unconsumed.asm")
                    expected = b"source span absent"
                else:
                    record["bytes"][0] = record["opcode"] = 234
                    expected = b"instruction bytes differ"
                analysis.write_json(path, changed)
                descriptor = copy.deepcopy(original)
                descriptor["outputs"]["instructions"] = analysis.fingerprint(path)
                analysis.write_json(self.path, descriptor)
                run = self.run_cli()
                self.assertEqual(run.returncode, 65, run.stderr)
                self.assertIn(expected, run.stderr)
                self.assertNotIn(b"strict_active_raw_", run.stdout)

    def test_late_change_and_unbound_policy_refuse_before_reporting(self):
        shared = self.produce()
        measured = raw.counts(shared)
        other = self.root / "other.conf"
        other.write_bytes(self.policy.read_bytes())
        with redirect_stdout(io.StringIO()) as output:
            with self.assertRaisesRegex(analysis.BundleError, "policy input not bound"):
                raw.report(shared, measured, other)
            self.assertEqual(output.getvalue(), "")
            self.source.write_text(self.source.read_text() + "; changed\n")
            with self.assertRaisesRegex(analysis.BundleError, "changed input"):
                raw.report(shared, measured)
            self.assertEqual(output.getvalue(), "")

    def test_data_only_profile_is_not_empty_evidence(self):
        self.produce("ci-data-v1")
        run = self.run_cli()
        self.assertEqual(run.returncode, 65, run.stderr)
        self.assertIn(b"lacks required artifact: instructions", run.stderr)
        self.assertNotIn(b"strict_active_raw_", run.stdout)


if __name__ == "__main__":
    unittest.main()
