#!/usr/bin/env python3
"""Version 3 instruction-record validation: accepted xasm output and one refusal per fact."""

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
    LDA [$00],Y
    LDA $01
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
        self.assertEqual(len(records), 11)
        # The truncated immediate is accepted: its term sums to $123 and the operand is $23.
        truncated = self.record("LDA #$123")
        self.assertEqual((truncated["operand_value"], truncated["additive_terms"]["terms"][0]["value"]),
                         (0x23, 0x123))

    def test_earlier_versions_refused(self):
        for version in ("1", "2"):
            payload = copy.deepcopy(self.payload)
            payload["version"] = version
            with self.assertRaisesRegex(ValueError, "version 3 required"):
                instruction_records.validate(payload)

    def test_file_table_refusals(self):
        def document(mutate, message):
            payload = copy.deepcopy(self.payload)
            mutate(payload)
            with self.assertRaisesRegex(ValueError, message):
                instruction_records.validate(payload)
        document(lambda d: d.pop("files"), "file table of distinct paths required")
        document(lambda d: d.update(files=[""]), "file table of distinct paths required")
        document(lambda d: d.update(files=d["files"] * 2), "file table of distinct paths required")
        self.refuse("INC Base", lambda r: r["use"].update(file=1), "invalid span file index")
        self.refuse("INC Base", lambda r: r["source"]["span"].update(file="input.asm"), "invalid span file index")
        self.refuse("LDA Base+2,X", lambda r: r["additive_terms"]["terms"][0]["binding"]["definition"].update(file=-1),
                    "invalid span file index")

    def test_source_check_runs_once_per_file(self):
        seen = []
        instruction_records.validate(copy.deepcopy(self.payload), seen.append)
        self.assertEqual(seen, self.payload["files"])

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
        self.refuse("JMP [$12FF]", lambda r: r["memory_access"].update(
            data={"kind": "read", "address": 0x12FF, "index_register": None, "via_pointer": False}),
            "data access/mode mismatch")
        self.refuse("LDA #<Start", lambda r: r.update(memory_access={
            "data": {"kind": "read", "address": r["operand_value"], "index_register": None, "via_pointer": False},
            "pointer": None}), "memory_access on a mode without a memory operand")
        self.refuse("LDA [ZP_Ptr],Y", lambda r: r.update(operand_value=None),
                    "memory_access requires an operand value")
        # JSON booleans compare equal to 0 and 1 in Python; a pointer at $00 is common.
        self.refuse("LDA [$00],Y", lambda r: r["memory_access"]["pointer"].update(address=False),
                    "invalid pointer access")
        self.refuse("LDA [$00],Y", lambda r: r["memory_access"]["pointer"].update(high_byte_address=True),
                    "invalid pointer access")
        self.refuse("LDA $01", lambda r: r["memory_access"]["data"].update(address=True),
                    "data address must be the operand value")
        self.refuse("LDA [$00],Y", lambda r: r["memory_access"]["data"].pop("address"),
                    "data address must be the operand value")

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
        self.refuse("LDA Base+2,X", lambda r: r["additive_terms"]["terms"][0]["binding"].pop("definition"),
                    "invalid term binding")

    def test_every_corrupted_field_is_refused_not_crashed(self):
        """Deleting or retyping any record value raises ValueError, never another exception."""
        def paths(value, prefix=()):
            yield prefix
            if isinstance(value, dict):
                for key, child in value.items():
                    yield from paths(child, prefix + (key,))
            elif isinstance(value, list):
                for index, child in enumerate(value):
                    yield from paths(child, prefix + (index,))
        tried = 0
        for index, record in enumerate(self.payload["records"]):
            for field in record:
                for path in list(paths(record[field], (field,))):
                    for replacement in ("delete", None, "x", 1.5, True, [], {}, -1):
                        payload = copy.deepcopy(self.payload)
                        parent = payload["records"][index]
                        for key in path[:-1]:
                            parent = parent[key]
                        if replacement == "delete":
                            if isinstance(parent, list):
                                parent.pop(path[-1])
                            else:
                                del parent[path[-1]]
                        else:
                            parent[path[-1]] = replacement
                        tried += 1
                        try:
                            instruction_records.validate(payload)
                        except ValueError:
                            pass
                        except Exception as exc:
                            self.fail(f"{path} = {replacement!r} raised {type(exc).__name__}: {exc}")
        self.assertGreater(tried, 5000)


if __name__ == "__main__":
    unittest.main()
