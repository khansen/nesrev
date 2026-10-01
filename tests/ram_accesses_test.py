#!/usr/bin/env python3
"""Real-producer controls for primary RAM operands and supporting byte reads."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import analysis_bundle
from ram_accesses import access_facts, group_sites, instruction_ram_sites


class RamAccesses(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="nesrev-ram-access-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        cwd = os.getcwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, cwd)
        self.source = Path("input.asm")

    def produce(self, text):
        self.source.write_text(text)
        result = subprocess.run([
            os.environ.get("XASM_BIN") or shutil.which("xasm"), "--pure-binary",
            "-o", "output.bin", "--instruction-records-output=instructions.json",
            "--dependency-manifest=dependencies.json",
            str(self.source)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return analysis_bundle.load_instruction_cache("instructions.json")

    def facts(self, sites):
        return {addr: access_facts(rows) for addr, rows in group_sites(sites).items()}

    def test_pointer_bytes_are_reads_and_only_bases_are_operands(self):
        document = self.produce(""".ORG $C000
Reader:
 LDA $21
 STA [$20],Y
 STA [$22,X]
 INC $21
 LDA [$FF],Y
 JMP [$01FF]
""")
        raw, symbolic = instruction_ram_sites(document, {}, str(self.source), repo_root=self.root)
        self.assertFalse(symbolic)
        facts = self.facts(raw)
        expected = {"0x0020": (1, 1, 0), "0x0021": (2, 3, 1),
                    "0x0022": (1, 1, 0), "0x0023": (0, 1, 0),
                    "0x00ff": (1, 1, 0), "0x0000": (0, 1, 0),
                    "0x01ff": (1, 1, 0), "0x0100": (0, 1, 0)}
        self.assertEqual(set(facts), set(expected))
        for addr, counts in expected.items():
            with self.subTest(addr=addr):
                self.assertEqual(tuple(facts[addr][key] for key in
                                       ("operand_count", "read_count", "write_count")), counts)
        document["records"].reverse()
        reversed_raw, _ = instruction_ram_sites(document, {}, str(self.source), repo_root=self.root)
        self.assertEqual(self.facts(reversed_raw), facts)

    def test_symbolized_counts_follow_resolved_base_not_high_byte_or_equate(self):
        document = self.produce(""".ORG $C000
ZP_Ptr .EQU $20
ZP_Base .EQU $10
Reader:
 STA [ZP_Ptr],Y
 INC ZP_Base+2
 LDA #ZP_Base
""")
        raw, symbolic = instruction_ram_sites(document, {0x20: ["ZP_Ptr"], 0x10: ["ZP_Base"]}, str(self.source), repo_root=self.root)
        self.assertFalse(raw)
        facts = self.facts(symbolic)
        self.assertEqual(set(facts), {"0x0020", "0x0021", "0x0012"})
        self.assertEqual(facts["0x0021"]["operand_count"], 0)
        self.assertEqual(facts["0x0021"]["read_count"], 1)
        self.assertEqual(facts["0x0012"]["operand_count"], 1)
        self.assertEqual(facts["0x0012"]["write_count"], 1)

    def test_truncated_pointer_keeps_written_candidate_and_resolved_reads(self):
        document = self.produce(".ORG $C000\n LDA [$0100],Y\n")
        raw, _ = instruction_ram_sites(document, {}, str(self.source), repo_root=self.root)
        facts = self.facts(raw)
        self.assertEqual({s["addr"] for s in raw if s["primary"]}, {0x100})
        self.assertEqual(facts["0x0100"]["read_count"], 0)
        self.assertEqual(facts["0x0100"]["sites"][0]["pointer"]["address"], 0)
        for addr in ("0x0000", "0x0001"):
            self.assertEqual(facts[addr]["operand_count"], 0)
            self.assertEqual(facts[addr]["read_count"], 1)

    def test_literal_policy_and_control_flow_exclusion(self):
        document = self.produce(""".ORG 0
Address .EQU $10
 LDA $f
 STA.W $0100
 LDA $FFF
 LDA $1000
 LDA #$10
 LDA 16
 LDA %10000
 LDA $00010
 LDA $10+0
 LDA Address
 JMP $30
 JSR $30
 BNE $30
""")
        raw, _ = instruction_ram_sites(document, {}, str(self.source), repo_root=self.root)
        self.assertEqual({s["addr"] for s in raw if s["primary"]}, {15, 256, 4095})

    def test_expansion_identity_data_owner_and_portable_provenance(self):
        Path("part.inc").write_text("IncludeOwner: LDA $24\n")
        source = """MACRO FETCH
 LDA $20
ENDM
.ORG $C000
Code:
 REPT 2
 FETCH
 ENDM
Data:
 .DB 0
 LDA $21 : STA $21
.IF 0
 LDA $22
.ENDIF
.INCLUDE "part.inc"
"""
        document = self.produce(source)
        raw, _ = instruction_ram_sites(document, {}, str(self.source), repo_root=self.root)
        facts = self.facts(raw)
        expanded = facts["0x0020"]["sites"]
        self.assertEqual(facts["0x0020"]["operand_count"], 2)
        self.assertEqual(expanded[0]["use"], expanded[1]["use"])
        self.assertNotEqual(expanded[0]["origin_id"], expanded[1]["origin_id"])
        self.assertEqual(facts["0x0021"]["distinct_owner_routines"], ["Data"])
        self.assertEqual(facts["0x0021"]["operand_count"], 2)
        self.assertNotIn("0x0022", facts)
        self.assertEqual(facts["0x0024"]["sites"][0]["file"], "part.inc")
        self.assertEqual(expanded[0]["file"], "input.asm")
        other = self.root / "second-checkout"
        other.mkdir()
        (other / "part.inc").write_bytes(Path("part.inc").read_bytes())
        os.chdir(other)
        self.assertEqual(instruction_ram_sites(document, {}, str(self.source), repo_root=self.root)[0], raw)
        second = self.produce(source)
        self.assertEqual(instruction_ram_sites(second, {}, str(self.source), repo_root=other)[0], raw)


if __name__ == "__main__":
    unittest.main()
