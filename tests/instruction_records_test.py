#!/usr/bin/env python3
"""Version 2 instruction-record validation: accepted xasm output and one refusal per fact."""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import instruction_records  # noqa: E402

SOURCE = """.ORG $C000
ZP_Ptr .EQU $FF
Base .EQU $0300
Start:
    LDA Base+2,X
    INC Base
    LDA [ZP_Ptr],Y
    STA [ZP_Ptr,X]
    JMP [$12FF]
    LDA #<Start
    LDA #$123
    BNE Start
    RTS
END
"""


class InstructionRecords(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with tempfile.TemporaryDirectory(prefix="nesrev-records-test-") as temp:
            root = Path(temp)
            (root / "input.asm").write_text(SOURCE)
            subprocess.run([os.environ.get("XASM_BIN", "xasm"), "--pure-binary", str(root / "input.asm"),
                            "-o", str(root / "out.bin"), f"--xref={root / 'xref.json'}",
                            "--xref-instructions=true"], check=True, capture_output=True)
            cls.payload = json.loads((root / "xref.json").read_text())["instruction_records"]

    def record(self, text):
        return next(r for r in self.payload["records"] if r["source"]["text"] == text)

    def refuse(self, text, mutate, message):
        payload = copy.deepcopy(self.payload)
        mutate(next(r for r in payload["records"] if r["source"]["text"] == text))
        with self.assertRaisesRegex(ValueError, message):
            instruction_records.validate(payload)

    def test_xasm_output_validates(self):
        records = instruction_records.validate(copy.deepcopy(self.payload))
        self.assertEqual(len(records), 9)
        # The truncated immediate is accepted: its term sums to $123 and the operand is $23.
        truncated = self.record("LDA #$123")
        self.assertEqual((truncated["operand_value"], truncated["additive_terms"]["terms"][0]["value"]),
                         (0x23, 0x123))

    def test_version_1_refused(self):
        payload = copy.deepcopy(self.payload)
        payload["version"] = "1"
        with self.assertRaisesRegex(ValueError, "version 2 required"):
            instruction_records.validate(payload)

    def test_memory_access_refusals(self):
        self.refuse("INC Base", lambda r: r.pop("memory_access"), "missing memory_access")
        self.refuse("INC Base", lambda r: r["memory_access"]["data"].update(kind="modify"),
                    "invalid data access kind")
        self.refuse("LDA Base+2,X", lambda r: r["memory_access"]["data"].update(address=0x300),
                    "data address must be the operand value")
        self.refuse("LDA Base+2,X", lambda r: r["memory_access"]["data"].update(index_register=None),
                    "data index/mode mismatch")
        self.refuse("LDA [ZP_Ptr],Y", lambda r: r["memory_access"]["data"].update(via_pointer=False),
                    "data via_pointer/mode mismatch")
        self.refuse("LDA [ZP_Ptr],Y", lambda r: r["memory_access"]["pointer"].update(high_byte_address=0x100),
                    "invalid pointer access")
        self.refuse("STA [ZP_Ptr,X]", lambda r: r["memory_access"]["pointer"].update(index_register=None),
                    "invalid pointer access")
        self.refuse("JMP [$12FF]", lambda r: r["memory_access"]["pointer"].update(high_byte_address=0x1300),
                    "invalid pointer access")
        self.refuse("JMP [$12FF]", lambda r: r.update(memory_access=None), "pointer mode without memory_access")

    def test_additive_terms_refusals(self):
        self.refuse("LDA Base+2,X", lambda r: r.pop("additive_terms"), "missing additive_terms")
        self.refuse("RTS", lambda r: r.update(additive_terms={"projection": "none", "terms": []}),
                    "additive terms for an operandless record")
        self.refuse("LDA Base+2,X", lambda r: r["additive_terms"]["terms"][1].update(value=3),
                    "additive terms do not add up to the operand value")
        self.refuse("LDA #<Start", lambda r: r["additive_terms"].update(projection="high"),
                    "additive terms do not add up to the operand value")
        self.refuse("LDA Base+2,X", lambda r: r["additive_terms"]["terms"][1].update(binding=None),
                    "binding presence/kind mismatch")
        self.refuse("LDA Base+2,X", lambda r: r["additive_terms"]["terms"][0]["binding"].update(kind="alias"),
                    "invalid term binding")
        self.refuse("LDA Base+2,X", lambda r: r["additive_terms"]["terms"][0].pop("name"),
                    "invalid term name")


if __name__ == "__main__":
    unittest.main()
