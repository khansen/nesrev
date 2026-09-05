"""Synthetic consumer models with explicit byte and caller-domain contracts."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from consumer_audit import Assembly, AuditError, Span, adc8, assemble, read_footprint, sbc8, walk_u8


def row_copy(initial=4, helper_increment=4):
    def step(index):
        index, _ = adc8(index, 1)
        if index & 7:
            return index
        index, _ = adc8(index, helper_increment)
        return None if index >= 68 else index
    return walk_u8(initial, step)


class ConsumerTests(unittest.TestCase):
    def test_carry_and_borrow_are_not_discarded(self):
        self.assertEqual(adc8(255, 0, 1), (0, 1))
        self.assertEqual(adc8(2, 3, 0), (5, 0))
        self.assertEqual(sbc8(0, 0, 0), (255, 0))
        self.assertEqual(sbc8(0, 0, 1), (0, 1))
        low, carry = adc8(250, 12)
        self.assertEqual(adc8(128, 0, carry)[0] * 256 + low, 0x8106)
        self.assertNotEqual(128 * 256 + low, 0x8106)

    def test_byte_operators_reject_silently_truncated_inputs(self):
        for values in ((256, 0), (-1, 0), (0, 0, 2), (True, 0)):
            with self.subTest(values=values), self.assertRaises(AuditError):
                adc8(*values)

    def test_helper_side_effect_changes_actual_payload_length(self):
        correct = row_copy()
        self.assertEqual(correct, [row * 8 + column for row in range(8) for column in range(4, 8)])
        self.assertEqual(len(correct), 32)
        self.assertNotEqual(len(row_copy(helper_increment=8)), len(correct))

    def test_wrapped_stride_reaches_a_previously_missed_end_index(self):
        def step(index):
            next_index, _ = adc8(index, 3)
            return None if next_index == 2 else next_index
        self.assertEqual(walk_u8(252, step), [252, 255])

    def test_no_stop_is_reported_as_a_cycle_not_a_finite_extent(self):
        with self.assertRaisesRegex(AuditError, "cycles"):
            walk_u8(0, lambda index: adc8(index, 2)[0])

    def test_zero_count_decrement_loop_executes_256_times(self):
        def decrement(index):
            value, _ = sbc8(index, 1)
            return value if value else None
        self.assertEqual(len(walk_u8(0, decrement)), 256)
        self.assertEqual(len(walk_u8(3, decrement)), 3)

    def test_read_footprint_distinguishes_allocation_record_and_tail(self):
        report = read_footprint(Span(100, 120), Span(108, 112), [108, 109, 110, 111, 112, 112])
        self.assertEqual(report["outside_allocation"], [])
        self.assertEqual(report["outside_selected_record"], [112])
        self.assertEqual(report["read_count"], 6)
        self.assertEqual(report["unique_read_offsets"], [108, 109, 110, 111, 112])
        report = read_footprint(Span(100, 120), Span(118, 120), [118, 119, 120])
        self.assertEqual(report["outside_allocation"], [120])

    def test_unread_allocated_tail_is_not_reported_as_consumed(self):
        report = read_footprint(Span(0, 40), Span(0, 16), range(15))
        self.assertEqual(len(report["unique_read_offsets"]), 15)
        self.assertNotIn(15, report["unique_read_offsets"])

    def test_empty_coverage_is_explicit(self):
        self.assertEqual(read_footprint(Span(0, 8), Span(0, 2), [])["read_count"], 0)

    def test_invalid_spans_and_indices_are_refused(self):
        with self.assertRaises(AuditError):
            Span(4, 3)
        with self.assertRaises(AuditError):
            walk_u8(0, lambda index: 256)
        with self.assertRaises(AuditError):
            read_footprint(Span(0, 8), Span(0, 2), [-1])

    def test_fresh_assembly_binds_consumer_and_helper_bytes(self):
        with tempfile.TemporaryDirectory(prefix="consumer-source-") as scratch:
            source = Path(scratch) / "Demo.asm"
            source.write_text(" .ORG $8000\nConsumer:\n JSR Advance\n RTS\nAdvance:\n INX\n INX\n RTS\nRecords:\n .DB 1,2,3\nEnd:\n")
            first = assemble(source)
            helper = first.value("Advance")
            first.require_bytes("Consumer", [0x20, helper & 255, helper >> 8, 0x60])
            first.require_bytes("Advance", [0xE8, 0xE8, 0x60])
            self.assertEqual(first.offset("End") - first.offset("Records"), 3)
            self.assertTrue(first.provenance["listing_sha256"])
            source.write_text(source.read_text().replace(" INX\n INX", " INX\n DEX"))
            second = assemble(source)
            with self.assertRaisesRegex(AuditError, "instruction contract changed"):
                second.require_bytes("Advance", [0xE8, 0xE8, 0x60])
            self.assertNotEqual(first.provenance["binary_sha256"], second.provenance["binary_sha256"])
            with self.assertRaisesRegex(AuditError, "escape"):
                second.data("Records", 4)

    def test_missing_assembler_or_symbols_never_claims_coverage(self):
        with self.assertRaisesRegex(AuditError, "assembler not found"):
            assemble(Path("missing.asm"), assembler="not-an-assembler-fixture")
        image = Assembly(b"", {"symbols": []})
        self.assertIsNone(image.provenance)
        with self.assertRaisesRegex(AuditError, "missing defined symbol"):
            image.offset("Absent")

    def test_noop_assembler_cannot_reuse_old_outputs(self):
        with self.assertRaisesRegex(AuditError, "did not produce valid"):
            assemble(Path("Demo.asm"), assembler="true")

    def test_scoped_anchor_must_be_unique(self):
        xref = {"symbols": [{"name": name, "defined": True, "definition": {"output_offset": 0}}
                            for name in ("@@step#A", "@@step#B")]}
        image = Assembly(b"", xref)
        self.assertIs(image.xref, xref)
        with self.assertRaisesRegex(AuditError, "found 2"):
            image.unique_local("@@step")
        with self.assertRaisesRegex(AuditError, "found 0"):
            image.unique_local("@@missing")

    def test_empty_instruction_contract_is_not_coverage(self):
        image = Assembly(b"", {"symbols": []})
        with self.assertRaisesRegex(AuditError, "must not be empty"):
            image.require_bytes("Absent", [])


if __name__ == "__main__":
    unittest.main()
