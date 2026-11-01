#!/usr/bin/env python3
"""Project-neutral source-model migration and workflow regressions."""
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import producer
from structured_pass.model import Model, certify, digest


def fixture(root, uses=1, declarations=1):
    root=Path(root);root.mkdir(parents=True,exist_ok=True)
    source=root/'sample.asm';reference=root/'sample.nes'
    prefix=b'.ORG $8000\nCell .EQU 16\nEntry: '+b'LDA #Cell\n'*uses+b'RTS\n.DW Entry\n; Private source comment\n'
    body=b'\xa9\x10'*uses+b'\x60\x00\x80'
    for index in range(1,declarations):
        prefix+=f'Cell{index} .EQU 16\nLDA #Cell{index}\n'.encode()
        body+=b'\xa9\x10'
    source.write_bytes(prefix+b'.DB "'+b'A'*(16384-len(body))+b'"\n.END\n')
    reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+body+b'A'*(16384-len(body)))
    return source,reference


class ProducerModelTests(unittest.TestCase):
    def setUp(self):
        executable=os.environ.get('STRUCTURED_PASS_XASM')
        if not executable:self.skipTest('Set STRUCTURED_PASS_XASM to the pinned source-model producer')
        producer.EXE=Path(executable).resolve()
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.source,self.reference=fixture(self.root)
        self.model,self.receipt=certify(self.source,self.root/'capture',self.reference)

    def test_reconstruction_without_source(self):
        expected=self.source.read_bytes();self.source.unlink()
        restored=Model(self.root/'capture')
        self.assertEqual(restored.source,expected)
        self.assertTrue(self.receipt['reference_prg_parity'])
        self.assertEqual(len(restored.bindings),2)

    def test_bound_rename_and_comment_only_repair(self):
        from structured_pass.rename_service import edits_for,comments
        m=self.model;n=m.declarations['Cell']
        operation={'kind':'rename','declaration_id':m.ids[n],'old_name':'Cell','new_name':'Capacity',
            'preimage':m.statement(n)['preimage_sha256']}
        edits,data=edits_for(m,[operation],'projects/sample/')
        self.source.write_bytes(data)
        changed,_=certify(self.source,self.root/'changed',self.reference,m,edits)
        self.assertEqual(changed.ids[changed.declarations['Capacity']],m.ids[n])
        self.assertEqual({m.ids[r] for r in m.bindings},{changed.ids[r] for r in changed.bindings})
        c=comments(changed)[0]
        op={'kind':'comment_replace','record_id':c['record_id'],'preimage':c['preimage_sha256'],
            'text':'; Byte sequence is intentionally repeated','reason':'Preserve an invariant'}
        edits,data=edits_for(changed,[op],'projects/sample/')
        self.source.write_bytes(data)
        final,_=certify(self.source,self.root/'repair',self.reference,changed,edits)
        self.assertEqual(len(final.bindings),2)

    def test_surviving_old_name_comment_fails_semantics(self):
        from structured_pass.rename_service import edits_for, RenameService
        m=self.model;n=m.declarations['Cell']
        op={'kind':'rename','declaration_id':m.ids[n],'old_name':'Cell','new_name':'Capacity',
            'preimage':m.statement(n)['preimage_sha256']}
        edits,data=edits_for(m,[op],'projects/sample/')
        # A real parity-preserving bad edit, deliberately bypassing preview.
        at=m.source.index(b'; Private source comment')
        edits.append((at,at+len(b'; Private source comment'),b'; Cell remains mentioned.'))
        edits.sort();data=m.source
        for lo,hi,value in reversed(edits):data=data[:lo]+value+data[hi:]
        self.source.write_bytes(data)
        changed,receipt=certify(self.source,self.root/'stale-comment',self.reference,m,edits)
        self.assertTrue(receipt['reference_prg_parity'])
        properties=RenameService.properties(None,m,changed,[op])
        self.assertFalse(properties['no_stale_source_prose'])
        self.assertFalse(properties['passed'])

    def test_partition_and_binding_tampering_refuse(self):
        import copy
        original=self.model.document
        for mutation in ('unit','binding','scope'):
            doc=copy.deepcopy(original)
            if mutation=='unit':doc['units'][0]['byte_end_exclusive']+=1
            elif mutation=='binding':doc['references'][0]['declaration_id']=doc['declarations'][-1]['id']
            else:doc['syntax'][0]['scope_id']='absent'
            path=self.root/'mutated.json';path.write_text(json.dumps(doc))
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):producer.load(path)

    def assemble_fixture(self,text,expected,name):
        source=self.root/(name+'.asm');reference=self.root/(name+'.nes')
        source.write_bytes(text+b'.DB "'+b'A'*(16384-len(expected))+b'"\n.END\n')
        reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+expected+b'A'*(16384-len(expected)))
        return certify(source,self.root/name,reference)[0],source,reference

    def test_scoped_local_rename_and_native_segments(self):
        from structured_pass.rename_service import edits_for, RenameService
        text=b'.ORG $8000\nFirst:\n@@loop:\nNOP\nBNE @@loop\n.ORG $8000\nSecond:\n@@loop:\nNOP\nBNE @@loop\n'
        model,source,reference=self.assemble_fixture(text,bytes.fromhex('ea d0 fd ea d0 fd'),'scopes')
        locals_=[n for n,f in model.facts.items() if f['kind']=='LOCAL_LABEL_NODE']
        a,b=locals_;self.assertNotEqual(model.locations[a]['segment_id'],model.locations[b]['segment_id'])
        self.assertEqual(model.locations[a]['cpu_address'],model.locations[b]['cpu_address'])
        op={'kind':'rename','declaration_id':model.ids[a],'old_name':'@@loop','new_name':'@@retry','preimage':model.statement(a)['preimage_sha256']}
        edits,data=edits_for(model,[op],'projects/sample/');source.write_bytes(data)
        after,_=certify(source,self.root/'scopes-after',reference,model,edits)
        self.assertEqual(after.name(after.node(model.ids[b])),'@@loop')
        self.assertTrue(RenameService.properties(None,model,after,[op])['passed'])

    def test_nested_data_and_equ_use_inventory(self):
        text=b'.ORG $8000\nMaskA .EQU 1\nMaskB .EQU 2\nAlias .EQU MaskA|MaskB\nEntry: LDA #(MaskA|MaskB)\n.DW Entry,Alias\n'
        model,_,_=self.assemble_fixture(text,bytes.fromhex('a9 03 00 80 03 00'),'nested')
        self.assertEqual(len(model.bindings),6)
        contexts={model.facts[model.context(n)]['kind'] for n in model.bindings}
        self.assertEqual(contexts,{'EQU_NODE','DATA_NODE','INSTRUCTION_NODE'})

    def test_alias_cannot_hide_a_missed_rename_use(self):
        from structured_pass.rename_service import edits_for,RenameService
        model=self.model;n=model.declarations['Cell']
        op={'kind':'rename','declaration_id':model.ids[n],'old_name':'Cell','new_name':'Capacity','preimage':model.statement(n)['preimage_sha256']}
        planned,_=edits_for(model,[op],'projects/sample/')
        # Preserve bytes while a faulty planner leaves the instruction using an
        # old-name alias. Record the real edits so identity alignment is intact.
        insertion=model.ranges[n][1]+1
        planned=[planned[0],(insertion,insertion,b'Cell .EQU Capacity\n')]
        data=model.source
        for lo,hi,replacement in reversed(planned):data=data[:lo]+replacement+data[hi:]
        self.source.write_bytes(data)
        bad,_=certify(self.source,self.root/'alias',self.reference,model,planned)
        properties=RenameService.properties(None,model,bad,[op])
        self.assertFalse(properties['passed'])
        self.assertFalse(properties['every_bound_use_preserved'])
        self.assertFalse(properties['reference_inventory_preserved'])

    def test_nes2_reference_uses_existing_rom_reader(self):
        data=bytearray(self.reference.read_bytes());data[7]=8;self.reference.write_bytes(data)
        _,receipt=certify(self.source,self.root/'nes2',self.reference)
        self.assertTrue(receipt['reference_prg_parity'])

    def test_parity_preserving_wrong_direction_edits(self):
        from structured_pass.rename_service import edits_for,RenameService
        model=self.model
        def operation(old,new):
            n=model.declarations[old]
            return {'kind':'rename','declaration_id':model.ids[n],'old_name':old,'new_name':new,
                    'preimage':model.statement(n)['preimage_sha256']}
        wanted=operation('Cell','Capacity')
        planned,_=edits_for(model,[wanted],'projects/sample/')
        unrelated,_=edits_for(model,[wanted,operation('Entry','Start')],'projects/sample/')
        reference=next(r for r in model.bindings if model.facts[model.context(r)]['kind']=='DATA_NODE')
        lo,hi=model.ranges[reference]
        cases=[('omitted',[],['declarations_renamed']),
               ('unrelated',unrelated,['unselected_declarations_preserved']),
               ('rebind',sorted(planned+[(lo,hi,b'$8000')]),
                ['unselected_bindings_preserved','reference_inventory_preserved'])]
        for name,edits,properties in cases:
            with self.subTest(case=name):
                data=model.source
                for lo,hi,replacement in reversed(edits):data=data[:lo]+replacement+data[hi:]
                self.source.write_bytes(data)
                bad,receipt=certify(self.source,self.root/name,self.reference,model,edits)
                self.assertTrue(receipt['reference_prg_parity'])
                result=RenameService.properties(None,model,bad,[wanted])
                for prop in properties:self.assertFalse(result[prop],prop)
                self.assertFalse(result['passed'])


if __name__=='__main__':unittest.main()
