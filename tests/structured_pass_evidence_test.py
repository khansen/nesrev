"""Analysis-query controls ported to native bindings and emission identities."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import producer, evidence_views as views, analogue_inputs
from structured_pass.model import certify


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        producer.EXE=Path(os.environ['STRUCTURED_PASS_XASM'])
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);source=self.root/'sample.asm';binary=self.root/'sample.bin'
        text=(ROOT/'tests/fixtures/structured_source_queries.asm').read_bytes();source.write_bytes(text)
        subprocess.run([str(producer.EXE),'--pure-binary',str(source),'-o',str(binary)],capture_output=True,check=True)
        raw=binary.read_bytes();padding=16384-len(raw)
        source.write_bytes(text+b'.DB "'+b'A'*padding+b'"\n.END\n')
        reference=self.root/'sample.nes';reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+raw+b'A'*padding)
        self.model,_=certify(source,self.root/'capture',reference)

    def ident(self,name):return self.model.ids[self.model.declarations[name]]

    def test_ram_aliases_need_memory_binding_and_rmw_stays_visible(self):
        rows=views.memory(self.model,address=0x40)
        aliases={ident for row in rows for ident in row['alias_proof_declaration_ids']}
        self.assertEqual(aliases,{self.ident('Cell'),self.ident('Alias')})
        self.assertNotIn(self.ident('ValueMask'),aliases)
        self.assertTrue(any(r['access']=='read_modify_write' for r in rows))
        selected=views.memory(self.model,record_id=self.ident('ValueMask'))
        self.assertTrue(all(not row['selected_alias_proven'] for row in selected))

    def test_pointer_wrap_and_indexed_destinations_are_not_exact(self):
        rows=views.memory(self.model,address=0)
        self.assertTrue(any(r['category']=='pointer_byte' and r['pointer_part']=='high' for r in rows))
        unknown=[r for r in rows if r['category']=='unresolved_indirect_destination']
        self.assertEqual(len(unknown),2)
        self.assertTrue(all(not r['exact_destination'] for r in unknown))
        self.assertTrue(any(r['category']=='indexed_other_base_possible' and r['memory_access']['data']['address']==0xFFFF for r in rows))

    def test_indexed_pointer_bytes_include_both_zero_page_boundaries(self):
        indexed=[self.model.ids[n] for n,ins in self.model.instructions.items()
                 if ins['memory_access'] and ins['memory_access']['pointer']
                 and ins['memory_access']['pointer']['index_register']]
        self.assertEqual(len(indexed),1)
        for address in (0,0xFE,0xFF):
            with self.subTest(address=address):
                rows=views.memory(self.model,address=address)
                hits=[r for r in rows if r['category']=='indexed_pointer_byte']
                self.assertEqual({(r['record_id'],r['pointer_part']) for r in hits},
                                 {(indexed[0],'low'),(indexed[0],'high')})
                self.assertEqual(len(hits),2)
                self.assertTrue(all(not r['exact_destination'] for r in hits))

    def test_indexed_pointer_bytes_exclude_nonzero_page_but_keep_unknown_targets(self):
        selections=[{'address':n} for n in (0x100,0x400,0x2000,0x6000,0xFFFF)]
        selections.extend({'record_id':self.ident(name)} for name in ('DisplacedCell','PrgCell'))
        for selection in selections:
            with self.subTest(selection=selection):
                rows=views.memory(self.model,**selection)
                self.assertFalse(any(r['category']=='indexed_pointer_byte' for r in rows))
                unknown=[r for r in rows if r['category']=='unresolved_indirect_destination']
                self.assertEqual(len(unknown),2)
                self.assertTrue(all(not r['exact_destination'] and r['pointer_part'] is None
                                    for r in unknown))

    def test_overlaid_cpu_addresses_never_merge_sites(self):
        m=self.model;entry=m.locations[m.declarations['Entry']];over=m.locations[m.declarations['Overlaid']]
        self.assertEqual(entry['cpu_address'],over['cpu_address'])
        self.assertNotEqual(entry['segment_id'],over['segment_id'])
        calls=[]
        for n,i in m.instructions.items():
            calls.extend(row for row in views.outgoing(m,m.ids[n]) if row['declaration_id']==self.ident('Called'))
        self.assertEqual(len(calls),2)
        self.assertEqual(len({r['record_id'] for r in calls}),2)
        # Leaf source spans alone do not expose physical layout: resolve the
        # native owning statement and retain its segment and output location.
        statements=[m.locations[m.node(r['statement_id'])] for r in calls]
        self.assertEqual(len({r['segment_id'] for r in statements}),2)

    def test_through_equ_and_data_arithmetic_keep_native_reference_leaves(self):
        m=self.model;alias=self.ident('CodeAlias');target=self.ident('ViaEquTarget')
        uses=[row for n in m.instructions for row in views.outgoing(m,m.ids[n]) if row['declaration_id']==alias]
        self.assertEqual(len(uses),1);self.assertEqual(uses[0]['through_equ_declaration_ids'],[target])
        data=views.data_rows(m,self.ident('Pointers'))
        refs=[r['reference_id'] for row in data for r in row['references']]
        self.assertEqual(len(refs),len(set(refs)))
        self.assertEqual(len(refs),6)
        self.assertEqual([r['element_width'] for r in data],[2]*4)

    def test_analogue_ids_are_separate_and_inputs_are_pinned(self):
        m=self.model
        analogue_inputs.capture([str(m.capture/'model.json')],m.capture)
        rows=analogue_inputs.rows(m,self.ident('Cell'));self.assertTrue(rows)
        analogue=analogue_inputs.project(m,0)
        self.assertTrue(set(m.ids.values()).isdisjoint(analogue.ids.values()))
        self.assertEqual(analogue.source,m.source)
        (m.capture/'analogue-0.json.gz').write_bytes(b'{}')
        with self.assertRaisesRegex(ValueError,'CAPTURE_CHANGED'):analogue_inputs.project(m,0)


if __name__=='__main__':unittest.main()
