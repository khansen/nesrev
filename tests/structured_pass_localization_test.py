"""Grouped localization preserves bindings, ledger obligations and review uses."""
import copy
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import producer, source_edits
from structured_pass.model import certify, digest
from structured_pass.rename_service import edits_for, ledger_operation, RenameService

TEXT=b'''.ORG $8000
Entry:
BEQ First
BNE Third
First:
BCC Second
Second:
BMI First
Third:
BPL Second
RTS
Next:
BNE @@first
@@first:
RTS
'''


def fixture(root, text=TEXT, **unused):
    root=Path(root);root.mkdir(parents=True,exist_ok=True)
    source=root/'sample.asm';binary=root/'sample.bin';reference=root/'sample.nes'
    source.write_bytes(text)
    subprocess.run([str(producer.EXE),'--pure-binary',str(source),'-o',str(binary)],
                   capture_output=True,check=True)
    raw=binary.read_bytes();padding=b'A'*(16384-len(raw))
    source.write_bytes(text+b'.DB "'+padding+b'"\n.END\n')
    reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+raw+padding)
    return source,reference


def operations(model):
    result=[]
    for name in ('First','Second','Third'):
        n=model.declarations[name]
        result.append({'kind':'localize','declaration_id':model.ids[n],
            'scope_id':model.ids[model.declarations['Entry']],
            'preimage':digest(model.source[slice(*model.ranges[n])]),
            'new_name':'@@'+name.lower(),'reason':'Internal branch target in the entry routine'})
    return result


def ledger(model,ops,preimage=None):
    return {'kind':'ledger_append','path':'projects/sample/docs/reverse_engineering/inventory/renames.csv',
        'preimage':preimage,'rows':[{'old_name':model.name(model.node(o['declaration_id'])),
            'new_name':o['new_name'],'reason':o['reason'],'confidence':'high','pass_id':'1'} for o in ops]}


class LocalizationTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        producer.EXE=Path(os.environ['STRUCTURED_PASS_XASM'])
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.source,self.reference=fixture(self.root)
        self.model,_=certify(self.source,self.root/'base',self.reference)

    def test_complete_group_preserves_every_use_and_neighbor_scope(self):
        m=self.model
        for index,ops in enumerate((operations(m),list(reversed(operations(m))))):
            with self.subTest(order=index):
                edits,data=edits_for(m,ops,'projects/sample/')
                self.source.write_bytes(data)
                changed,receipt=certify(self.source,self.root/str(index),self.reference,m,edits)
                self.assertTrue(receipt['reference_prg_parity'])
                self.assertTrue(RenameService.properties(None,m,changed,ops)['passed'])
                expected={m.ids[m.declarations[name]] for name in ('First','Second','Third')}
                expected|={m.ids[r] for r,d in m.bindings.items() if m.ids[d] in expected}
                review=[r for op in ops for r in source_edits.review(m,changed,op,edits)]
                self.assertEqual({r['before']['record_id'] for r in review},expected)
                self.assertEqual(len(review),8)
                for row in review:
                    self.assertEqual(row['before']['record_id'],row['after']['record_id'])
                    self.assertTrue(row['after']['name'].startswith('@@'))
                    self.assertEqual(row['before']['declaration_id'],row['after']['declaration_id'])
                neighbor=next(n for n,d in m.declaration_records.items() if d['kind']=='local')
                self.assertEqual(changed.ids[changed.owners[changed.node(m.ids[neighbor])]],m.ids[m.declarations['Next']])

    def test_localization_must_use_requested_name_after_certification(self):
        m=self.model;ops=operations(m);edits,data=edits_for(m,ops,'projects/sample/')
        self.source.write_bytes(data)
        changed,_=certify(self.source,self.root/'changed',self.reference,m,edits)
        source_edits.reconcile(m,changed,ops,edits)
        n=changed.node(ops[0]['declaration_id']);changed.facts[n]['name']='@@wrong'
        with self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_IDENTITY$'):
            source_edits.reconcile(m,changed,ops,edits)

    def test_gap_collision_and_owner_localization_refuse(self):
        ops=operations(self.model)
        cases=[ops[1:],ops[:1]+ops[2:]]
        duplicate=copy.deepcopy(ops);duplicate[1]['new_name']=duplicate[0]['new_name'];cases.append(duplicate)
        nested=copy.deepcopy(ops);nested[2]['scope_id']=nested[0]['declaration_id'];cases.append(nested)
        for bad in cases:
            with self.subTest(operations=bad),self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCOPE$'):
                edits_for(self.model,bad,'projects/sample/')

    def test_outside_equ_data_and_call_uses_refuse(self):
        for index,extra in enumerate((b'BEQ First\n',b'Alias .EQU First\n',b'.DW First\n',b'JSR First\n',b'JMP First\n')):
            with self.subTest(extra=extra):
                source,reference=fixture(self.root/str(index),TEXT.replace(b'Next:\n',b'Next:\n'+extra))
                m,_=certify(source,self.root/('capture'+str(index)),reference)
                with self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCOPE$'):
                    edits_for(m,operations(m),'projects/sample/')

    def in_scope_model(self,index,extra):
        source,reference=fixture(self.root/str(index),TEXT.replace(b'BNE Third\n',b'BNE Third\n'+extra))
        m,_=certify(source,self.root/('capture'+str(index)),reference)
        start=m.ranges[m.declarations['Entry']][0];end=m.ranges[m.declarations['Next']][0]
        refs=[r for r,d in m.bindings.items() if d==m.declarations['First']]
        self.assertEqual(len(refs),3)
        self.assertTrue(all(start<=m.ranges[r][0]<end for r in refs))
        return m,refs

    def test_in_scope_call_and_jump_uses_refuse(self):
        for index,mnemonic in enumerate(('JSR','JMP')):
            with self.subTest(mnemonic=mnemonic):
                m,refs=self.in_scope_model(index,(mnemonic+' First\n').encode())
                self.assertTrue(all(m.context(r) in m.instructions for r in refs))
                self.assertEqual(sum(m.instructions[m.context(r)]['mnemonic']==mnemonic for r in refs),1)
                with self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCOPE$'):
                    edits_for(m,operations(m),'projects/sample/')

    def test_in_scope_data_and_equ_uses_refuse(self):
        for index,extra in enumerate((b'.DW First\n',b'Alias .EQU First\n')):
            with self.subTest(extra=extra):
                m,refs=self.in_scope_model(index,extra)
                self.assertEqual(sum(m.context(r) not in m.instructions for r in refs),1)
                with self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCOPE$'):
                    edits_for(m,operations(m),'projects/sample/')

    def test_existing_local_names_cannot_collide_after_scopes_merge(self):
        for index,text in enumerate((TEXT.replace(b'First:\n',b'First:\n@@second:\n'),
                 TEXT.replace(b'First:\n',b'First:\n@@inner:\n').replace(b'Third:\n',b'Third:\n@@inner:\n'))):
            with self.subTest(case=index):
                source,reference=fixture(self.root/str(index),text)
                m,_=certify(source,self.root/('capture'+str(index)),reference)
                with self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCOPE$'):
                    edits_for(m,operations(m),'projects/sample/')

    def test_localization_requires_exact_ledger_and_rejects_declaration_rows(self):
        m=self.model;ops=operations(m);row=ledger(m,ops)
        with self.assertRaisesRegex(ValueError,'^LEDGER_SCHEMA$'):
            ledger_operation(ops,'projects/sample/',m)
        self.assertEqual(ledger_operation(ops+[row],'projects/sample/',m),row)
        row['rows'][0]['old_name']='Wrong'
        with self.assertRaisesRegex(ValueError,'^LEDGER_RENAME_MISMATCH$'):
            ledger_operation(ops+[row],'projects/sample/',m)
        row=ledger(m,ops[:1])
        with self.assertRaisesRegex(ValueError,'^LEDGER_RENAME_MISMATCH$'):
            ledger_operation([{'kind':'declare'},row],'projects/sample/',m)

    def test_stale_localization_prose_must_be_repaired(self):
        source,reference=fixture(self.root/'prose',TEXT.replace(b'Entry:\n',b'; First owns this path.\nEntry:\n'))
        m,_=certify(source,self.root/'prose-base',reference);ops=operations(m)
        for index,repair in enumerate((False,True)):
            requests=copy.deepcopy(ops)
            if repair:
                i=next(i for i,u in enumerate(m.units) if u['kind']=='comment');unit=m.units[i]
                requests.append({'kind':'unit_replace','unit_id':'u'+str(i),
                    'preimage':digest(bytes.fromhex(unit['hex'])),'text':'','reason':'Remove stale target prose'})
            edits,data=edits_for(m,requests,'projects/sample/');source.write_bytes(data)
            after,_=certify(source,self.root/('prose-after'+str(index)),reference,m,edits)
            result=RenameService.properties(None,m,after,requests)
            self.assertEqual(result['no_stale_source_prose'],repair)
            self.assertEqual(result['passed'],repair)

    def test_localization_publication_preserves_ledger_and_review_in_both_sessions(self):
        from structured_pass_fixture import prepare,closeout_ops
        from structured_pass.retained_service import RetainedReviewService
        scratch=ROOT/'tmp';scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as temp:
            root=Path(temp)
            with patch('structured_pass_fixture.fixture',fixture):c=prepare(root)
            g=c.editor.state['current'];m=c.editor.model(g);ops=operations(m)
            prefix=Path(c.editor.state['generations'][g]['checkout'],c.editor.ledger).read_bytes()
            ops.append(ledger(m,ops,c.editor.state['generations'][g]['manifest'][c.editor.ledger]))
            ops+=closeout_ops(c,g)
            preview=c.dispatch('preview',{'generation':g,'operations':ops},'implementer')
            cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
            validated=c.dispatch('validate',{'cid':cid},'implementer')
            self.assertEqual(validated['status'],'validated',validated)
            pub=c.dispatch('publish',{'cid':cid},'implementer')
            current=c.editor.state['current']
            contents=Path(c.editor.state['generations'][current]['checkout'],c.editor.ledger).read_bytes()
            self.assertTrue(contents.startswith(prefix));self.assertEqual(len(contents[len(prefix):].splitlines()),3)
            reader=RetainedReviewService.from_publication(root/'reader',root/'store',pub['review']['artifact_id'])
            a,b=reader.config['artifacts']
            def scan(service,after,before):
                offset=0;changes=[]
                while offset is not None:
                    page=service.review(after,before,offset);changes+=page['changes'];offset=page['next_offset']
                return changes
            live=scan(c.editor,current,g);retained=scan(reader,b,a)
            self.assertEqual(live,retained)
            localized=[r for r in live if r['kind']=='source_change' and r.get('operation_kind')=='localize']
            self.assertEqual(len(localized),8)


if __name__=='__main__':unittest.main()
