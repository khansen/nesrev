#!/usr/bin/env python3
"""Real-assembler fixtures for the named-table gate; no project inputs."""
import copy
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import analysis_bundle as analysis
import pointer_table_body_check as checker


class PointerTables(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='nesrev-pointer-test-')
        self.root = Path(self.temp.name)
        self.source = self.root / 'input.asm'
        self.serial = 0

    def tearDown(self):
        self.temp.cleanup()

    def bundle(self, source, profile='data-listing-v1'):
        self.source.write_text(source)
        self.serial += 1
        directory = self.root / str(self.serial)
        directory.mkdir()
        analysis.prepare_source(directory, self.source, [], profile=profile)
        run = subprocess.run([sys.executable, str(ROOT / 'scripts/analysis_bundle.py'),
                              'produce', str(directory), str(self.source), str(directory / 'out.bin')],
                             capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        return analysis.Bundle(directory / 'bundle.json', self.source)

    def names(self, source):
        return [row.name for row in checker.findings(self.bundle(source))]

    def cli(self, *args, env=None):
        return subprocess.run([sys.executable, str(ROOT / 'scripts/pointer_table_body_check.py'),
                               *map(str, args)], capture_output=True, text=True,
                              env={**os.environ, **(env or {})})

    def test_selector_variants_and_suffix_boundary(self):
        yes = ['ImagePtrByX', 'ImagePointerBy2Frames', 'ImagePtrAByIndex',
               'ImagePtrBByFrame_Index', 'OldPtrTable']
        no = ['ImagePtrByte', 'ImagePtrBytes', 'ImagePtrBypass', 'ImagePtrBy_x',
              'ImagePtrByframe', 'ImagePtrBy', 'ImagePtrVariantByIndex']
        source = '.ORG $C000\n' + ''.join(name + ': .DB $00,$90,$20,$90\n' for name in yes + no)
        self.assertEqual(self.names(source), yes)

    def test_active_same_line_and_instruction_boundary(self):
        source = ('.ORG $C000\n.IF 0\nInactivePtrTable: .DB $00,$90,$20,$90\n.ENDIF\n'
                  'ActivePtrByX: .DB $00,$90,$20,$90\n'
                  'AdvancePtrByX: LDA #0\nRTS\n.DB $00,$90,$20,$90\n'
                  'InterruptedPtrByX: .DB $00,$90\nNOP\n.DB $20,$90\n')
        self.assertEqual(self.names(source), ['ActivePtrByX'])

    def test_aliases_share_bytes_and_symbolic_exclusion(self):
        self.assertEqual(self.names('.ORG $C000\nImagePtrByX:\nAlias:\n.DB $00,$90,$20,$90\n'),
                         ['ImagePtrByX'])
        self.assertEqual(self.names('.ORG $C000\nImagePtrByX:\nAlias:\n.DB $00,$90,$20,$90\n'
                                    '.DB <Target,>Target\nTarget: RTS\n'), [])

    def test_constant_operands_do_not_claim_raw_pointer_evidence(self):
        source = ('.ORG $C000\nHI = $90\nImagePtrByX: .DB 0,HI,1,HI\n'
                  'SymbolicPtrByX: .DB <Target,>Target,<Target,>Target\n'
                  'NumericWordsPtrTable: .DW $9000,$9020\nTarget: RTS\n')
        self.assertEqual(self.names(source), [])

    def test_end_markers_require_matching_table_and_exact_boundary(self):
        source = ('.ORG $C000\nImagePtrTable: .DW Target,Target\nImagePtrTableEnd:\n'
                  'PackedPayload: .DB $10,$90,$20,$90\n'
                  'RawPtrTable: .DB $00,$90,$20,$90\nRawPtrTableEnd:\n'
                  'OtherPayload: .DB $30,$90,$40,$90\n'
                  'OrphanPtrTableEnd: .DB $50,$90,$60,$90\n'
                  'OffsetPtrTable: .DW Target,Target\n.DSB 1\n'
                  'OffsetPtrTableEnd: .DB $70,$90,$80,$90\n'
                  'OriginPtrTable: .DW Target,Target\n.ORG $D000\n'
                  'OriginPtrTableEnd: .DB $90,$90,$A0,$90\nTarget: RTS\n')
        self.assertEqual(self.names(source), ['RawPtrTable', 'OrphanPtrTableEnd', 'OffsetPtrTableEnd',
                                             'OriginPtrTableEnd'])

    def test_split_ram_cannot_be_decoded_as_interleaved_rom(self):
        source = ('.ORG $C000\nImagePtrLoByX: .DB $80,$80,$90,$90\n'
                  'ImagePtrHiByX: .DB $04,$04,$04,$04\n')
        self.assertEqual(self.names(source), [])

    def test_single_label_split_ram_layout_is_not_guessed(self):
        self.assert_unresolved_layout('ImagePtrByX: .DB $80,$80,$90,$90,$04,$04,$04,$04\n',
                                      'ambiguous interleaved ROM')

    def test_split_rom_all_spellings_and_order(self):
        for lo, hi in (('PtrLo','PtrHi'), ('PointerLo','PointerHi'), ('PtrLow','PtrHigh'),
                       ('LoPtr','HiPtr'), ('LowPtr','HighPtr')):
            with self.subTest(lo=lo):
                self.assertEqual(self.names(f'.ORG $C000\nImage{hi}ByX: .DB $90,$90\n'
                                            f'Image{lo}ByX: .DB $00,$20\n'), [f'Image{lo}ByX'])

    def assert_unresolved_layout(self, source, message):
        shared = self.bundle('.ORG $C000\n' + source)
        rows = checker.findings(shared)
        self.assertTrue(rows)
        for row in rows:
            self.assertIsNone(row.proof)
            self.assertIn(message, row.unresolved)
        for mode, status in (('', 0), ('--strict-whole-body', 0), ('--strict', 68)):
            run = self.cli(self.source, *([mode] if mode else []),
                           env={'NESREV_ANALYSIS_BUNDLE': str(shared.path)})
            self.assertEqual(run.returncode, status, run.stderr)
            self.assertIn('has unresolved layout:', run.stderr)
            self.assertNotIn('evidence refused', run.stderr)
            self.assertIn('raw_pointer_table_bodies=0', run.stdout)
            self.assertIn(f'unresolved_layout_bodies={len(rows)}', run.stdout)

    def test_split_unresolved_layouts(self):
        cases = [
            ('ZpCursorPtrLoTable: .DB $10,$12,$14\n', 'counterpart'),
            ('RomPtrLoTable: .DB $00,$90,$20,$90\n', 'counterpart'),
            ('ImagePtrLoByX: .DB $00,$20\n', 'counterpart'),
            ('ImagePtrHiByX: .DB $90,$90\n', 'counterpart'),
            ('ImagePtrLoByX: .DB $00,$20\nImagePtrHiByX: .DB $90\n', 'incomplete, unequal'),
            ('ImagePtrLoByX: .DB $00,$20\nImagePtrHiByY: .DB $90,$90\n', 'counterpart'),
            ('ImagePtrLoByX:\nImagePtrHiByX: .DB $90,$90\n', 'incomplete, unequal'),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                self.assert_unresolved_layout(source, message)

    def test_named_aliases_report_once_per_body(self):
        shared = self.bundle('.ORG $C000\nOnePtrTable:\nTwoPtrTable:\nAlias:\n'
                             '.DB $00,$90,$20,$90\n')
        rows = checker.findings(shared)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].aliases, ['TwoPtrTable', 'Alias'])
        run = self.cli(self.source, '--strict-whole-body',
                       env={'NESREV_ANALYSIS_BUNDLE': str(shared.path)})
        self.assertEqual(run.returncode, 68, run.stderr)
        self.assertEqual(run.stderr.count('advisory:'), 1)
        self.assertIn('aliases: TwoPtrTable, Alias', run.stderr)
        self.assertIn('raw_pointer_table_bodies=1', run.stdout)
        self.assertEqual(self.names('.ORG $C000\nAliasPtrTable:\nImagePtrLoByX:\n'
                                    '.DB $80,$80,$90,$90\nImagePtrHiByX: .DB 4,4,4,4\n'), [])

    def test_origin_segment_and_trailing_boundaries(self):
        source = ('.ORG $C000\nImagePtrByX: .DB $00,$90\n.ORG $D000\n.DB $20,$90\n'
                  '.DATASEG\n.ORG $300\nStoragePtrByX: .DSB 4\n.CODESEG\n.ORG $C010\n'
                  'CompletePtrByX: .DB $00,$90,$20,$90\nTrailingPtrByX:\n.END\n')
        self.assertEqual(self.names(source), ['CompletePtrByX'])

    def test_storage_before_data_and_instructions(self):
        self.assertEqual(self.names('.ORG $C000\nReset: RTS\n.DSB 16377\n.DW Reset,Reset,Reset\n'), [])
        self.assertEqual(self.names('.ORG $C000\n.DSW 2\nImagePtrByX: .DB $00,$90,$20,$90\nRTS\n'),
                         ['ImagePtrByX'])

    def test_includes_and_repetition(self):
        (self.root/'part.inc').write_text('IncludedPtrByX: .DB $00,$90,$20,$90\n')
        self.assertEqual(self.names('.ORG $C000\n.INCSRC "part.inc"\n'
                                    'RepeatedPtrByX:\n.REPT 2\n.DB $00,$90\n.ENDM\n'),
                         ['IncludedPtrByX', 'RepeatedPtrByX'])

    def test_macro_data_expansion(self):
        source = ('MACRO BYTES\n.DB $00,$90\nENDM\n.ORG $C000\n'
                  'ImagePtrByX:\nREPT 2\nBYTES\nENDM\n')
        self.assertEqual(self.names(source), ['ImagePtrByX'])

    def test_macro_local_identity_is_not_guessed(self):
        source = ('MACRO BYTES\n@@entry: .DB $00,$90,$20,$90\nENDM\n'
                  '.ORG $C000\nImagePtrByX:\nREPT 2\nBYTES\nENDM\n')
        with self.assertRaisesRegex(analysis.BundleError, 'unavailable scope'):
            checker.findings(self.bundle(source))

    def test_undefined_redefined_identity_refuses(self):
        with self.assertRaisesRegex(analysis.BundleError, 'ambiguous or redefined'):
            checker.findings(self.bundle('.ORG $C000\nImagePtrByX: .DB $00,$90,$20,$90\n'
                                         '.UNDEF ImagePtrByX\nImagePtrByX: RTS\n'))

    def test_intermediate_unavailable_scope_refuses(self):
        with self.assertRaisesRegex(analysis.BundleError, 'unavailable scope'):
            checker.findings(self.bundle('.ORG $C000\nImagePtrByX: .DB $00,$90\n'
                                         '@@part: .DB $20,$90\n'))

    def test_prefix_modes(self):
        shared = self.bundle('.ORG $C000\nImagePtrByX: .DB $00,$90,$20,$90\n'
                             '.DB $20,$00,$18,$11,$22,$33,$44,$55,$66,$77,$88,$99,$AA,$BB,$CC,$DD\n')
        env = {'NESREV_ANALYSIS_BUNDLE':str(shared.path)}
        for mode, status in (('',0), ('--strict-whole-body',0), ('--strict',68)):
            run = self.cli(self.source, *([mode] if mode else []), env=env)
            self.assertEqual(run.returncode,status,run.stderr)
            self.assertIn('proof: leading prefix',run.stderr)

    def test_bad_cli_and_supplied_evidence_never_assemble(self):
        spy = self.root/'spy'
        touched = self.root/'touched'
        spy.write_text('#!/bin/sh\ntouch "'+str(touched)+'"\nexit 1\n')
        spy.chmod(0o755)
        env = {'XASM_BIN':str(spy)}
        self.assertEqual(self.cli(self.source, '--stict',env=env).returncode,64)
        for path in ('',str(self.root/'missing.json')):
            run = self.cli(self.source, env={**env,'NESREV_ANALYSIS_BUNDLE':path})
            self.assertEqual(run.returncode,65,run.stderr)
        self.assertFalse(touched.exists())

    def test_stale_bundle_and_missing_listing_refuse(self):
        shared = self.bundle('.ORG $C000\nImagePtrByX: .DB $00,$90,$20,$90\n')
        self.source.write_text(self.source.read_text()+'; edit\n')
        run = self.cli(self.source,env={'NESREV_ANALYSIS_BUNDLE':str(shared.path)})
        self.assertEqual(run.returncode,65,run.stderr)
        self.assertIn('changed input',run.stderr)
        shared = self.bundle('.ORG $C000\nReset: RTS\n',profile='instructions-v1')
        run = self.cli(self.source,env={'NESREV_ANALYSIS_BUNDLE':str(shared.path)})
        self.assertEqual(run.returncode,65,run.stderr)
        self.assertIn('lacks required artifact',run.stderr)

    def test_malformed_listing_and_data_reference_refuse(self):
        shared = self.bundle('.ORG $C000\nImagePtrByX: .DB $00,$90,$20,$90\n'
                             'Other: .DB <Target,>Target\nTarget: RTS\n')
        listing, xref = shared.load('listing'), shared.load('xref')
        binary = analysis.read_bytes(shared.data['outputs']['binary']['path'])
        broken = copy.deepcopy(listing)
        next(r for r in broken['records'] if r['bytes_hex'])['bytes_hex'][0] = 'FF'
        with self.assertRaisesRegex(analysis.BundleError,'disagree with binary'):
            checker.table_bodies(xref,broken,binary)
        broken = copy.deepcopy(xref)
        broken['data_directive_references'][0]['emitted_value'] ^= 1
        with self.assertRaisesRegex(analysis.BundleError,'invalid data reference bytes'):
            checker.table_bodies(broken,listing,binary)

    def test_standalone_assembles_once_and_maps_failure(self):
        real = analysis.executable()
        log = self.root/'calls'
        spy = self.root/'spy'
        shutil.copyfile(ROOT/'tests/fixtures/analysis_count_xasm.py',spy)
        spy.chmod(0o755)
        env = {'XASM_BIN':str(spy),'BUNDLE_TEST_REAL_XASM':real,'BUNDLE_TEST_CALLS':str(log)}
        self.source.write_text('.ORG $C000\nImagePtrByX: .DB $00,$90,$20,$90\n')
        run = self.cli(self.source,'--strict',env=env)
        self.assertEqual(run.returncode,68,run.stderr)
        self.assertEqual(len(log.read_text().splitlines()),1)
        self.assertNotIn('defined but not used', run.stderr)
        self.assertNotIn('warning:', run.stderr)
        self.source.write_text('LDA MissingLabel\n')
        run = self.cli(self.source,env=env)
        self.assertEqual(run.returncode,65)
        self.assertIn('MissingLabel', run.stderr)


if __name__ == '__main__':
    unittest.main()
