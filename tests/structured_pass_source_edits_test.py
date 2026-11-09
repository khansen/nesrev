"""Typed edits checked against the pinned assembler, including wrong-direction cases."""
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import producer, source_edits, ownership, service
from structured_pass.model import certify, digest
from structured_pass.rename_service import edits_for, RenameService
from structured_pass import evidence_views, artifact_edits


class SourceEditTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        producer.EXE=Path(os.environ['STRUCTURED_PASS_XASM'])
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.serial=0
        text=b'.ORG $8000\nValue .EQU 16\nUnused .EQU 4\nEntry:\nLDA #16\nBNE Step\nStep:\nLDA #Value\nRTS\n.DB 1,2,3,4\n; Invariant\n'
        code=bytes.fromhex('a9 10 d0 00 a9 10 60 01 02 03 04')
        self.source=self.root/'sample.asm';self.reference=self.root/'sample.nes'
        self.source.write_bytes(text+b'.DB "'+b'A'*(16384-len(code))+b'"\n.END\n')
        self.reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+code+b'A'*(16384-len(code)))
        self.base,_=certify(self.source,self.root/'base',self.reference)

    def ident(self,name):return self.base.ids[self.base.declarations[name]]

    def hash(self,n):
        lo,hi=self.base.ranges[n];return digest(self.base.source[lo:hi])

    def apply(self,ops):
        self.serial+=1;edits,data=edits_for(self.base,ops,'projects/sample/')
        self.source.write_bytes(data)
        changed,receipt=certify(self.source,self.root/str(self.serial),self.reference,self.base,edits)
        self.assertTrue(receipt['reference_prg_parity'])
        self.assertTrue(RenameService.properties(None,self.base,changed,ops)['passed'])
        return changed

    def test_declare_and_replace_selected_expression(self):
        m=self.base;n=m.declarations['Value'];inst=next(iter(m.instructions))
        operand=next(n for n,e in m.expression_records.items() if e['context_syntax_id']==inst)
        ops=[{'kind':'declare','anchor_id':m.ids[n],'preimage':self.hash(n),
              'declaration_kind':'equ','name':'Limit','expression':{'integer':16},'reason':'Loop limit'},
             {'kind':'replace_expression','expression_id':m.ids[operand],'preimage':self.hash(operand),
              'expression':{'declaration_id':'new:Limit'},'reason':'Use the selected loop limit'}]
        new=self.apply(ops)
        self.assertEqual(new.values['Limit'],16)
        self.assertIn(new.declarations['Limit'],new.bindings.values())
        # A new equal-valued declaration cannot impersonate the requested binding.
        leaf=next(r for r,d in new.bindings.items() if d==new.declarations['Limit'])
        new.bindings[leaf]=new.declarations['Value']
        edits,_=edits_for(m,ops,'projects/sample/')
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_BINDING'):source_edits.reconcile(m,new,ops,edits)

    def test_multiple_declarations_share_anchor_in_request_order(self):
        m=self.base;n=m.declarations['Entry'];ops=[]
        for name in ('Zeta','Alpha','Middle'):
            ops.append({'kind':'declare','anchor_id':m.ids[n],'preimage':self.hash(n),
                'declaration_kind':'equ','name':name,'expression':{'integer':16},'reason':'Selected separate constant role'})
        inst=next(iter(m.instructions));e=next(n for n,v in m.expression_records.items() if v['context_syntax_id']==inst)
        ops.append({'kind':'replace_expression','expression_id':m.ids[e],'preimage':self.hash(e),
            'expression':{'declaration_id':'new:Alpha'},'reason':'Bind only the selected reader'})
        new=self.apply(ops)
        self.assertIn(b'Zeta .EQU 16\nAlpha .EQU 16\nMiddle .EQU 16\nEntry:',new.source)
        for name in ('Zeta','Alpha','Middle'):self.assertEqual(new.values[name],16)
        self.assertEqual(sum(d==new.declarations['Alpha'] for d in new.bindings.values()),1)
        self.assertNotIn(new.declarations['Zeta'],new.bindings.values())

    def test_binary_expression_has_canonical_literal_spelling(self):
        m=self.base;inst=next(iter(m.instructions));e=next(n for n,v in m.expression_records.items() if v['context_syntax_id']==inst)
        op={'kind':'replace_expression','expression_id':m.ids[e],'preimage':self.hash(e),
            'expression':{'operator':'+','operands':[{'declaration_id':self.ident('Value')},{'integer':0}]},
            'reason':'Expose the selected zero displacement'}
        new=self.apply([op]);self.assertIn(b'LDA #(Value)+0\n',new.source)
        op['expression']['operands'][1]={'integer':-1}
        text,_=source_edits.typed_expression(m,op['expression'],{})
        self.assertEqual(text,b'(Value)+(-1)')

    def test_reflow_continuation_indentation_is_bounded_trivia(self):
        m=self.base;data=m.document['data'][0];n=data['syntax_id']
        native={e['id']:node for node,e in m.expression_records.items()}
        ids=[m.ids[native[o['expression_id']]] for o in data['operands']]
        op={'kind':'reflow_data','record_ids':[m.ids[n]],'preimages':[self.hash(n)],
            'groups':[ids[:2],ids[2:]],'continuation_indent':'    ','reason':'Keep generated rows aligned'}
        new=self.apply([op]);self.assertIn(b'.DB 1,2\n    .DB 3,4\n',new.source)
        for bad in ('\nNOP\n',';',' '*17,1):
            with self.subTest(indent=bad),self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCHEMA$'):
                op['continuation_indent']=bad;edits_for(m,[op],'projects/sample/')

    def test_data_extent_aliases_share_only_their_native_physical_start(self):
        from structured_pass_localization_test import fixture
        text=(b'.ORG $8000\nStream:\n; Shared stream entry\nStreamAlias:\n.DB 1,2,3\n'
              b'Tail:\n.DB 4\nBeforeOrigin:\n.ORG $8000\nOverlaid:\n.DB 5,6\nCode:\nRTS\n')
        source,reference=fixture(self.root/'alias',text)
        m,_=certify(source,self.root/'alias-base',reference)
        def ident(name):return m.ids[m.declarations[name]]
        try:rows=evidence_views.data_rows(m,ident('Stream'))
        except ValueError as exc:self.fail('Native alias was refused: '+str(exc))
        self.assertEqual(rows,evidence_views.data_rows(m,ident('StreamAlias')))
        self.assertEqual(sum(r['byte_length'] for r in rows),3)
        self.assertEqual([r['value'] for r in evidence_views.decode(m,ident('Stream'),'bytes',byte_count=3)],[1,2,3])
        with self.assertRaisesRegex(ValueError,'^EVIDENCE_RANGE_INVALID$'):
            evidence_views.decode(m,ident('Stream'),'bytes',byte_count=4)
        self.assertEqual(sum(r['byte_length'] for r in evidence_views.data_rows(m,ident('Overlaid'))),2)
        self.assertNotEqual(rows[0]['segment_id'],evidence_views.data_rows(m,ident('Overlaid'))[0]['segment_id'])
        with self.assertRaisesRegex(ValueError,'^EVIDENCE_RANGE_INVALID$'):
            evidence_views.data_rows(m,ident('BeforeOrigin'))
        path=self.root/'projects/sample'/artifact_edits.PATHS['extent_rows'];path.parent.mkdir(parents=True)
        path.write_text('label,expected_size,reason\nStream,3,Reviewed shared stream.\nStreamAlias,3,Same entry.\nTail,1,Distinct byte.\nOverlaid,2,Separate bank.\n')
        op={'kind':'extent_rows','preimage':digest(path.read_bytes()),'reason':'Validate reviewed extents','changes':[]}
        artifact_edits.extents(self.root,m,[op],'projects/sample/')
        path.write_text(path.read_text().replace('Stream,3,','Stream,4,'))
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_ROW_INVALID$'):
            artifact_edits.extents(self.root,m,[op],'projects/sample/')

    def test_equ_inside_data_is_not_a_data_extent_or_warning_split(self):
        from structured_pass_localization_test import fixture
        text=b'.ORG $8000\nTable:\nOldLimit .EQU 1\n.DB 1,2\nTail:\n.DB 3\n'
        source,reference=fixture(self.root/'equ-data',text)
        m,_=certify(source,self.root/'equ-data-base',reference)
        ident=m.ids[m.declarations['OldLimit']]
        with self.assertRaisesRegex(ValueError,'^EVIDENCE_RANGE_INVALID$'):
            evidence_views.data_rows(m,ident)
        data=m.document['data'][0];n=data['syntax_id'];exprs={e['id']:node for node,e in m.expression_records.items()}
        ids=[m.ids[exprs[o['expression_id']]] for o in data['operands']]
        ops=[{'kind':'rename','declaration_id':ident,'old_name':'OldLimit','new_name':'NewLimit',
              'preimage':m.statement(m.declarations['OldLimit'])['preimage_sha256']},
             {'kind':'reflow_data','record_ids':[m.ids[n]],'preimages':[digest(m.source[slice(*m.ranges[n])])],
              'groups':[[ids[0]],[ids[1]]],'boundaries':[{'operand_id':ids[1],'name':'Inner'}],
              'reason':'Separate the two byte fields'}]
        edits,after=edits_for(m,ops,'projects/sample/');source.write_bytes(after)
        changed,_=certify(source,self.root/'equ-data-after',reference,m,edits)
        with self.assertRaisesRegex(ValueError,'^WARNING_IDENTITY_CHANGED$'):
            artifact_edits.warning_changes(b'OldLimit|External ownership.\n',b'NewLimit|Different rationale.\n',m,changed)
        kept=artifact_edits.warning_changes(b'OldLimit|External ownership.\n',b'NewLimit|External ownership.\n',m,changed)
        self.assertEqual([r['transition'] for r in kept],['rename'])

    def test_rebind_delete_and_reflow_form_one_candidate(self):
        from structured_pass_localization_test import fixture
        text=b'.ORG $8000\nStream:\n.DB 1,2\n; Obsolete interior boundary\nTail:\n.DB 3,4\nVectors:\n.DW Tail\n'
        source,reference=fixture(self.root/'merged',text)
        m,_=certify(source,self.root/'merged-base',reference);tail=m.declarations['Tail']
        exprs={e['id']:n for n,e in m.expression_records.items()};data=m.document['data']
        vector=exprs[data[2]['operands'][0]['expression_id']]
        ids=[m.ids[exprs[o['expression_id']]] for d in data[:2] for o in d['operands']]
        def pre(n):return digest(m.source[slice(*m.ranges[n])])
        unit_index=next(i for i,u in enumerate(m.units) if u['kind']=='comment');unit=m.units[unit_index]
        ops=[{'kind':'replace_expression','expression_id':m.ids[vector],'preimage':pre(vector),
              'expression':{'integer':m.locations[tail]['cpu_address'],'format':'hex'},'reason':'Literal vector is not an entry declaration'},
             {'kind':'delete_declaration','declaration_id':m.ids[tail],'preimage':pre(tail),'reason':'Remove the retired boundary'},
             {'kind':'unit_replace','unit_id':'u'+str(unit_index),'preimage':digest(bytes.fromhex(unit['hex'])),
              'text':'','reason':'Remove the retired boundary contract'},
             {'kind':'reflow_data','record_ids':[m.ids[d['syntax_id']] for d in data[:2]],
              'preimages':[pre(d['syntax_id']) for d in data[:2]],'groups':[ids],
              'reason':'The complete four-byte stream has one reviewed extent'}]
        for order,requests in enumerate((ops,list(reversed(ops)))):
            edits,changed=edits_for(m,requests,'projects/sample/');source.write_bytes(changed)
            after,receipt=certify(source,self.root/('merged-after'+str(order)),reference,m,edits)
            self.assertTrue(receipt['reference_prg_parity'])
            self.assertTrue(RenameService.properties(None,m,after,requests)['passed'])
            self.assertIn(b'Stream:\n.DB 1,2,3,4\n',changed)
            self.assertIn(b'.DW $8002\n',changed)
            self.assertNotIn(b'Tail',changed);self.assertNotIn(b'Obsolete',changed)
            self.assertEqual(sum(r['byte_length'] for r in evidence_views.data_rows(after,after.ids[after.declarations['Stream']])),4)
        for index,code in ((0,'SOURCE_EDIT_LIVE_DECLARATION'),(1,'SOURCE_EDIT_BOUNDARY'),(2,'SOURCE_EDIT_BOUNDARY')):
            with self.subTest(omitted=index),self.assertRaisesRegex(ValueError,'^'+code+'$'):
                edits_for(m,ops[:index]+ops[index+1:],'projects/sample/')

    def test_literal_expression_formats_are_typed(self):
        for fmt,expected in (('hex',b'$10'),('binary',b'%10000'),('decimal',b'16')):
            self.assertEqual(source_edits.typed_expression(self.base,{'integer':16,'format':fmt},{})[0],expected)
        for bad in ({'integer':16,'format':'$10\nNOP'}, {'integer':-1,'format':'hex'},
                    {'declaration_id':self.ident('Value'),'format':'hex'}):
            with self.subTest(request=bad),self.assertRaisesRegex(ValueError,'^SOURCE_EDIT_SCHEMA$'):
                source_edits.typed_expression(self.base,bad,{})

    def test_deleted_declaration_requires_current_prose_cleanup(self):
        self.source.write_bytes(b'; Unused defines this value.\n'+self.base.source)
        m,_=certify(self.source,self.root/'delete-base',self.reference);n=m.declarations['Unused']
        delete={'kind':'delete_declaration','declaration_id':m.ids[n],
            'preimage':digest(m.source[slice(*m.ranges[n])]),'reason':'Retire the unreferenced definition'}
        i=next(i for i,u in enumerate(m.units) if u['kind']=='comment');u=m.units[i]
        cleanup={'kind':'unit_replace','unit_id':'u'+str(i),'preimage':digest(bytes.fromhex(u['hex'])),
            'text':'','reason':'Remove prose naming the retired declaration'}
        for index,ops in enumerate(([delete],[delete,cleanup])):
            edits,data=edits_for(m,ops,'projects/sample/');self.source.write_bytes(data)
            after,_=certify(self.source,self.root/('delete-after'+str(index)),self.reference,m,edits)
            self.assertEqual(RenameService.properties(None,m,after,ops)['passed'],bool(index))

    def test_localize_and_delete_unused_declaration(self):
        m=self.base;n=m.declarations['Step'];unused=m.declarations['Unused']
        ops=[{'kind':'localize','declaration_id':m.ids[n],'scope_id':self.ident('Entry'),
              'preimage':self.hash(n),'new_name':'@@step','reason':'Only this branch reaches the internal step'},
             {'kind':'delete_declaration','declaration_id':m.ids[unused],'preimage':self.hash(unused),'reason':'Unused definition'}]
        new=self.apply(ops)
        self.assertEqual(new.name(new.node(m.ids[n])),'@@step')
        self.assertNotIn(m.ids[unused],new.nodes)
        ops[1]['declaration_id']=self.ident('Value');ops[1]['preimage']=self.hash(m.declarations['Value'])
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_LIVE_DECLARATION'):edits_for(m,ops,'projects/sample/')

    def test_declaration_preserves_attached_native_headers(self):
        for index, header in enumerate((b'; Format: two fields\n; Used by: entry\n',
                                         b'\t; Indented header\n', b'')):
            with self.subTest(header=header):
                text=self.base.source.replace(b'Entry:\n',header+b'Entry:\n')
                self.source.write_bytes(text)
                model,_=certify(self.source,self.root/('header-base-'+str(index)),self.reference)
                n=model.declarations['Entry'];a,b=model.ranges[n]
                op={'kind':'declare','anchor_id':model.ids[n],
                    'preimage':digest(model.source[a:b]),'declaration_kind':'equ',
                    'name':'Limit','expression':{'integer':16},'reason':'Selected limit role'}
                edits,changed=edits_for(model,[op],'projects/sample/')
                expected=text.replace(header+b'Entry:\n',b'Limit .EQU 16\n'+header+b'Entry:\n')
                self.assertEqual(changed,expected)
                self.source.write_bytes(changed)
                after,_=certify(self.source,self.root/('header-after-'+str(index)),self.reference,model,edits)
                self.assertTrue(RenameService.properties(None,model,after,[op])['passed'])

    def test_declaration_does_not_move_before_previous_inline_comment(self):
        header=b'; Public entry contract\n'
        text=self.base.source.replace(b'Unused .EQU 4\nEntry:',
            b'Unused .EQU 4 ; previous definition\n'+header+b'Entry:')
        self.source.write_bytes(text)
        model,_=certify(self.source,self.root/'inline-base',self.reference)
        n=model.declarations['Entry'];a,b=model.ranges[n]
        op={'kind':'declare','anchor_id':model.ids[n],'preimage':digest(model.source[a:b]),
            'declaration_kind':'equ','name':'Limit','expression':{'integer':16},'reason':'Selected limit role'}
        _,changed=edits_for(model,[op],'projects/sample/')
        self.assertEqual(changed,text.replace(header,b'Limit .EQU 16\n'+header))

    def test_typed_operator_must_match_even_when_values_coincide(self):
        m=self.base;inst=next(iter(m.instructions))
        operand=next(n for n,e in m.expression_records.items() if e['context_syntax_id']==inst)
        value={'operator':'+','operands':[{'declaration_id':self.ident('Value')},{'integer':0}]}
        op={'kind':'replace_expression','expression_id':m.ids[operand],'preimage':self.hash(operand),
            'expression':value,'reason':'Expose a zero displacement without changing bytes'}
        changed=self.apply([op])
        root=next(n for n,e in changed.expression_records.items() if e.get('operator')=='add')
        changed.expression_records[root]['operator']='subtract'
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_EXPRESSION'):
            source_edits.verify_expression(changed,root,value,{})

    def test_reflow_preserves_operand_identity_and_rejects_reordering(self):
        m=self.base;data=m.document['data'][0];n=data['syntax_id']
        native={e['id']:node for node,e in m.expression_records.items()}
        ids=[m.ids[native[o['expression_id']]] for o in data['operands']]
        op={'kind':'reflow_data','record_ids':[m.ids[n]],'preimages':[self.hash(n)],
            'groups':[ids[:2],ids[2:]],'reason':'Two fields per record'}
        new=self.apply([op])
        for ident in ids:self.assertIn(ident,new.nodes)
        op['groups']=[list(reversed(ids))]
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_IDENTITY'):edits_for(m,[op],'projects/sample/')

    def test_comment_and_whitespace_without_dummy_edit(self):
        m=self.base;i=next(i for i,u in enumerate(m.units) if u['kind']=='comment')
        op={'kind':'unit_replace','unit_id':'u'+str(i),'preimage':digest(bytes.fromhex(m.units[i]['hex'])),
            'text':'','reason':'Remove redundant comment'}
        new=self.apply([op]);self.assertNotIn(b'; Invariant',new.source)
        op['text']='; injected\nNOP'
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_BOUNDARY'):edits_for(m,[op],'projects/sample/')

    def test_reflow_literal_formats_and_boundary_header_keep_identities(self):
        m=self.base;data=m.document['data'][0];n=data['syntax_id']
        native={e['id']:node for node,e in m.expression_records.items()}
        ids=[m.ids[native[o['expression_id']]] for o in data['operands']]
        op={'kind':'reflow_data','record_ids':[m.ids[n]],'preimages':[self.hash(n)],
            'groups':[ids[:2],ids[2:]],'formats':{ids[0]:'binary',ids[1]:'hex'},
            'boundaries':[{'operand_id':ids[2],'name':'Tail',
                'header':['; Format: two trailing fields','; Used by: external reader']}],
            'reason':'Separate the trailing fields while preserving each operand'}
        new=self.apply([op])
        self.assertIn(b'.DB %00000001,$02\n\n; Format: two trailing fields\n'
            b'; Used by: external reader\nTail:\n.DB 3,4',new.source)
        self.assertEqual([new.expression_records[new.node(i)]['value'] for i in ids],[1,2,3,4])
        before=evidence_views.data_rows(m,m.ids[n])
        tail=evidence_views.data_rows(new,new.ids[new.declarations['Tail']])[:2]
        self.assertEqual([(r['record_id'],r['output_offset']) for r in tail],
                         [(r['record_id'],r['output_offset']) for r in before[2:]])
        self.assertEqual(source_edits.previews(m,[op])[0]['format'],'binary')
        self.assertEqual(source_edits.review(m,new,op,edits_for(m,[op],'projects/sample/')[0])[-1]['header'],
                         op['boundaries'][0]['header'])
        new.expression_records[new.node(ids[0])]['value']=257
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_EXPRESSION'):
            source_edits.reconcile(m,new,[op],edits_for(m,[op],'projects/sample/')[0])

    def test_reflow_formatting_cannot_replace_bindings_or_strings(self):
        m=self.base;data=m.document['data'][1];n=data['syntax_id']
        operand=next(n for n,e in m.expression_records.items() if e['id']==data['operands'][0]['expression_id'])
        ident=m.ids[operand]
        op={'kind':'reflow_data','record_ids':[m.ids[n]],'preimages':[self.hash(n)],
            'groups':[[ident]],'formats':{ident:'binary'},'reason':'Invalid string format request'}
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_EXPRESSION'):edits_for(m,[op],'projects/sample/')
        del op['formats'];op['boundaries']=[{'operand_id':ident,'name':'Tail','header':['; Header\nNOP']}]
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_SCHEMA'):edits_for(m,[op],'projects/sample/')
        op['boundaries'][0]['header']=[';'+('x'*4096)]
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_SCHEMA'):edits_for(m,[op],'projects/sample/')
        del op['boundaries'];op['formats']={self.ident('Value'):'decimal'}
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_SCHEMA'):edits_for(m,[op],'projects/sample/')
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_EXPRESSION'):
            ref=next(iter(m.bindings))
            source_edits.operand_spelling(m,ref,'decimal',1)

    def test_warning_rename_is_one_identity_and_preserves_rationale(self):
        m=self.base;n=m.declarations['Unused']
        op={'kind':'rename','declaration_id':m.ids[n],'preimage':self.hash(n),
            'old_name':'Unused','new_name':'ReservedCount'}
        changed=self.apply([op])
        before=b'Unused|External reader owns this count.\n'
        after=b'ReservedCount|External reader owns this count.\n'
        rows=artifact_edits.warning_changes(before,after,m,changed)
        self.assertEqual(len(rows),1)
        self.assertEqual(rows[0]['transition'],'rename')
        self.assertEqual(rows[0]['declaration_id'],m.ids[n])
        self.assertEqual(rows[0]['before']['rationale'],rows[0]['after']['rationale'])
        with self.assertRaisesRegex(ValueError,'WARNING_IDENTITY_CHANGED'):
            artifact_edits.warning_changes(before,b'ReservedCount|Different rationale.\n',m,changed)
        before+=b'Value|Public count for callers.\n'
        requested=['ReservedCount|External reader owns this count.','Value|Public count for callers.']
        self.assertEqual(artifact_edits.warning_bytes(before,requested,m,changed),
                         ('\n'.join(requested)+'\n').encode())
        with self.assertRaisesRegex(ValueError,'WARNING_ORDER_CHANGED'):
            artifact_edits.warning_bytes(before,list(reversed(requested)),m,changed)

    def test_evidence_distinguishes_unknown_from_zero_and_retains_layout(self):
        m=self.base;unused=self.ident('Unused')
        rows=evidence_views.query(m,'scopes',record_id=unused)['records']
        self.assertEqual(rows[0]['direct_use_count'],0)
        self.assertIsNone(rows[0]['safe_to_localize'])
        with self.assertRaisesRegex(ValueError,'UNKNOWN_RECORD'):evidence_views.query(m,'scopes',record_id='missing')
        stmt=m.document['data'][0]['syntax_id']
        rows=evidence_views.query(m,'data',record_id=m.ids[stmt])['records']
        self.assertEqual([r['byte_length'] for r in rows],[1]*4)
        decoded=evidence_views.query(m,'decode',record_id=m.ids[stmt],decoder='words_le',byte_count=4)['records']
        self.assertEqual([r['value'] for r in decoded],[513,1027])
        with self.assertRaisesRegex(ValueError,'EVIDENCE_RANGE_INVALID'):
            evidence_views.query(m,'decode',record_id=m.ids[stmt],decoder='words_le',byte_count=3)


class SourceLifecycleTests(unittest.TestCase):
    def test_blob_citation_sees_candidate_document_and_refuses_missing_artifact(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        from structured_pass_fixture import prepare,closeout_ops
        scratch=Path(__file__).resolve().parents[1]/'tmp';scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as root:
            c=prepare(Path(root));g=c.editor.state['current'];m=c.editor.model(g)
            n=m.document['data'][0]['syntax_id']
            declaration={'kind':'declare','anchor_id':m.ids[n],'preimage':m.statement(n)['preimage_sha256'],
                'declaration_kind':'label','name':'PointerWord','reason':'One pointer field'}
            path='projects/sample/docs/reverse_engineering/PARITY_GAPS.md'
            document={'kind':'document_write','path':path,'preimage':None,'text':'# Field format\n\nOne pointer word.\n',
                      'reason':'Document the pointer field'}
            row={'label':'PointerWord','disposition':'pointer_table','format':'one pointer word',
                 'artifact':'PARITY_GAPS.md','consumer_evidence':'External pointer reader',
                 'pointer_evidence':'One native word','extent_evidence':'Two emitted bytes',
                 'reflow_status':'not_applicable','notes':'Single pointer field'}
            artifact={'kind':'blob_rows','preimage':None,'reason':'Record the pointer format',
                      'changes':[{'key':'PointerWord','preimage':None,'row':row}]}
            operations=[declaration,artifact,*closeout_ops(c,g)]
            with self.assertRaisesRegex(ValueError,'ARTIFACT_ROW_INVALID'):
                c.dispatch('preview',{'generation':g,'operations':operations},'implementer')
            operations.insert(1,document)
            p=c.dispatch('preview',{'generation':g,'operations':operations},'implementer')
            cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
            result=c.dispatch('validate',{'cid':cid},'implementer')
            self.assertEqual(result['status'],'validated',result)
            c.dispatch('publish',{'cid':cid},'implementer')
            generation=c.editor.state['generations'][c.editor.state['current']]
            absolute={**row,'artifact':str(Path(generation['checkout'])/path)}
            with self.assertRaisesRegex(ValueError,'ARTIFACT_ROW_INVALID'):
                artifact_edits.validate_blob_rows(Path(generation['checkout']),'projects/sample/',
                    'projects/sample/'+artifact_edits.PATHS['blob_rows'],[absolute],[])
            deletion={'kind':'document_delete','path':path,'preimage':generation['manifest'][path],
                      'reason':'Exercise dangling artifact refusal'}
            artifact['preimage']=generation['manifest']['projects/sample/'+artifact_edits.PATHS['blob_rows']]
            artifact['changes']=[]
            with self.assertRaisesRegex(ValueError,'ARTIFACT_ROW_INVALID'):
                c.dispatch('preview',{'generation':c.editor.state['current'],
                    'operations':[deletion,artifact,*closeout_ops(c,c.editor.state['current'])]},'implementer')

    def test_data_boundary_and_extent_rows_share_one_publication(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        from structured_pass_fixture import prepare,closeout_ops
        from structured_pass.retained_service import RetainedReviewService
        scratch=Path(__file__).resolve().parents[1]/'tmp';scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as root:
            root=Path(root);c=prepare(root);g=c.editor.state['current'];m=c.editor.model(g)
            data=m.document['data'];ops=[]
            for name,statement in zip(('Pointers','Padding'),data):
                n=statement['syntax_id'];ops.append({'kind':'declare','anchor_id':m.ids[n],
                    'preimage':m.statement(n)['preimage_sha256'],'declaration_kind':'label','name':name,
                    'reason':'Separate the pointer word from fill bytes'})
            ops.append({'kind':'extent_rows','preimage':None,'reason':'Pin the complete pointer word',
                'changes':[{'key':'Pointers','preimage':None,
                            'row':{'label':'Pointers','expected_size':'2','reason':'One complete pointer word'}}]})
            ops+=closeout_ops(c,g)
            preview=c.dispatch('preview',{'generation':g,'operations':ops},'implementer')
            cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
            validated=c.dispatch('validate',{'cid':cid},'implementer');self.assertEqual(validated['status'],'validated',validated)
            pub=c.dispatch('publish',{'cid':cid},'implementer')
            reader=RetainedReviewService.from_publication(root/'reader',root/'store',pub['review']['artifact_id'])
            a,b=reader.config['artifacts'];pages=[];offset=0
            while offset is not None:
                page=reader.review(b,a,offset);pages.extend(page['changes']);offset=page['next_offset']
            fields=[r['row'] for r in pages if r['kind']=='artifact_change']
            self.assertEqual({r['field'] for r in fields},{'label','expected_size','reason'})
            result=reader.dispatch('evidence',{'generation':b,'view':'artifact_rows','artifact':'extent_rows','key':'Pointers'},'reviewer')
            self.assertEqual(result['total_rows'],1);self.assertEqual(result['total_records'],3)

    def test_warning_writer_uses_fresh_diagnostics_and_rejects_nonwarnings(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        from structured_pass_fixture import prepare,closeout_ops
        scratch=Path(__file__).resolve().parents[1]/'tmp';scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as root:
            c=prepare(Path(root));g=c.editor.state['current'];m=c.editor.model(g);n=m.declarations['Cell']
            decl={'kind':'declare','anchor_id':m.ids[n],'preimage':m.statement(n)['preimage_sha256'],
                  'declaration_kind':'label','name':'ReservedLimit','reason':'Reserved public entry'}
            baseline={'kind':'warning_baseline','preimage':None,'reason':'Retain a public definition with no local user',
                      'entries':[{'declaration_id':'new:ReservedLimit',
                                  'rationale':'Public limit for external callers, retained without a local use.'}]}
            def validate(entries):
                operations=[decl,{**baseline,'entries':entries},*closeout_ops(c,g)]
                p=c.dispatch('preview',{'generation':g,'operations':operations},'implementer')
                cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
                return cid,c.dispatch('validate',{'cid':cid},'implementer')
            _,bad=validate([{**baseline['entries'][0],'declaration_id':m.ids[n]}])
            self.assertEqual(bad['error'],'WARNING_NOT_CURRENT')
            read=bad['error_details']['read']
            evidence=c.dispatch(read['operation'],read['arguments'],'implementer')
            self.assertEqual([r['symbol'] for r in evidence['records']],['ReservedLimit'])
            self.assertEqual(evidence['records'][0]['declaration_id'],'new:ReservedLimit')
            cid,good=validate(baseline['entries']);self.assertEqual(good['status'],'validated',good)
            c.dispatch('publish',{'cid':cid},'implementer')
            g=c.editor.state['current'];m=c.editor.model(g);n=m.declarations['ReservedLimit']
            generation=c.editor.state['generations'][g]
            rename={'kind':'rename','declaration_id':m.ids[n],'old_name':'ReservedLimit','new_name':'ExternalLimit',
                    'preimage':m.statement(n)['preimage_sha256']}
            ledger={'kind':'ledger_append','path':c.editor.ledger,'preimage':generation['manifest'][c.editor.ledger],
                    'rows':[{'old_name':'ReservedLimit','new_name':'ExternalLimit','reason':'External public limit',
                             'confidence':'high','pass_id':'1'}]}
            warning={**baseline,'preimage':generation['manifest']['projects/sample/'+artifact_edits.PATHS['warning_baseline']],
                     'entries':[{'declaration_id':m.ids[n],'rationale':baseline['entries'][0]['rationale']}]}
            def renamed_validate(rationale):
                operations=[rename,ledger,{**warning,'entries':[{'declaration_id':m.ids[n],'rationale':rationale}]},
                            *closeout_ops(c,g)]
                p=c.dispatch('preview',{'generation':g,'operations':operations},'implementer')
                cid=c.dispatch('confirm',{'generation':g,'preview_digest':p['preview_digest']},'implementer')['candidate']
                return cid,c.dispatch('validate',{'cid':cid},'implementer')
            _,bad=renamed_validate('Changed ownership without evidence.')
            self.assertEqual(bad['error'],'WARNING_IDENTITY_CHANGED')
            cid,good=renamed_validate(warning['entries'][0]['rationale'])
            self.assertEqual(good['status'],'validated',good)
            pub=c.dispatch('publish',{'cid':cid},'implementer')
            from structured_pass.retained_service import RetainedReviewService
            reader=RetainedReviewService.from_publication(Path(root)/'warning-reader',Path(root)/'store',pub['review']['artifact_id'])
            old,new=reader.config['artifacts'][-2:];offset=0;transitions=[]
            while offset is not None:
                page=reader.review(new,old,offset)
                transitions.extend(row['row'] for row in page['changes'] if row.get('operation_kind')=='warning_baseline')
                offset=page['next_offset']
            self.assertEqual([r['transition'] for r in transitions],['rename'])
            self.assertEqual(transitions[0]['before']['symbol'],'ReservedLimit')
            self.assertEqual(transitions[0]['after']['symbol'],'ExternalLimit')

    def test_new_operations_publish_and_retain_review_and_queries(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        from structured_pass_fixture import prepare,closeout_ops
        from structured_pass.retained_service import RetainedReviewService
        scratch=Path(__file__).resolve().parents[1]/'tmp';scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as root:
            root=Path(root);c=prepare(root);g=c.editor.state['current'];m=c.editor.model(g)
            n=m.declarations['Cell'];inst=next(iter(m.instructions))
            operand=next(n for n,e in m.expression_records.items() if e['context_syntax_id']==inst)
            op=[{'kind':'declare','anchor_id':m.ids[n],'preimage':m.statement(n)['preimage_sha256'],
                'declaration_kind':'equ','name':'Limit','expression':{'integer':16},'reason':'Independent limit role'},
                {'kind':'replace_expression','expression_id':m.ids[operand],
                 'preimage':digest(m.source[slice(*m.ranges[operand])]),'expression':{'declaration_id':'new:Limit'},
                 'reason':'Bind this selected use to its limit'},*closeout_ops(c,g)]
            preview=c.dispatch('preview',{'generation':g,'operations':op},'implementer')
            cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
            validated=c.dispatch('validate',{'cid':cid},'implementer');self.assertEqual(validated['status'],'validated',validated)
            pub=c.dispatch('publish',{'cid':cid},'implementer')
            reader=RetainedReviewService.from_publication(root/'reader',root/'store',pub['review']['artifact_id'])
            older,newer=reader.config['artifacts'];offset=0;changes=[]
            while offset is not None:
                page=reader.review(newer,older,offset=offset);changes+=page['changes'];offset=page['next_offset']
            self.assertEqual(sum(row['kind']=='source_change' for row in changes),2)
            for target,generation in ((c,pub['generation']),(reader,newer)):
                evidence=target.dispatch('evidence',{'generation':generation,'view':'scopes'},'reviewer')
                self.assertTrue(any(r['name']=='Limit' for r in evidence['records']))


class ArtifactLayoutTests(unittest.TestCase):
    def prepare(self,before,changes):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();path='projects/sample/'+artifact_edits.PATHS['extent_rows']
            target=root/path;target.parent.mkdir(parents=True);target.write_bytes(before)
            op={'kind':'extent_rows','preimage':digest(before),'reason':'Reviewed table bounds','changes':changes}
            try:return artifact_edits.prepare(root,{path:digest(before)},[op],'projects/sample/')[0]['after']
            finally:self.assertEqual(target.read_bytes(),before)

    def test_quoted_csv_noop_preserves_every_byte(self):
        for ending in (b'\n',b'\r\n',b'\r'):
            before=ending.join((b'# Extents',b'',b'"label","expected_size","reason"',
                b'"Zeta","3","First, reviewed extent."',b'"Alpha","4","Second extent."'))
            with self.subTest(ending=ending):self.assertEqual(self.prepare(before,[]),before)

    def test_changed_csv_row_preserves_other_rows_header_and_footer(self):
        before=(b'# Extents\n\n"label","expected_size","reason"\r\n\r\n'
                b'"Zeta","3","First, reviewed extent."\r\n"Alpha","4","Second extent."\r\n'
                b'"Mid","8","Last extent."\r\n\r\n# End of reviewed extents\r\n')
        old=artifact_edits.read_rows(before,'extent_rows')[1]
        changed={**old,'reason':'Measured second extent.'}
        after=self.prepare(before,[{'key':'Alpha','preimage':artifact_edits.row_hash(old),'row':changed}])
        self.assertEqual(after,before.replace(b'"Alpha","4","Second extent."',b'Alpha,4,Measured second extent.'))

    def test_csv_add_and_remove_keep_surviving_row_bytes_and_row_endings(self):
        before=b'# Extents\nlabel,expected_size,reason\n"Zeta","3","First extent."\r\n"Alpha","4","Second extent."'
        old=artifact_edits.read_rows(before,'extent_rows')[0]
        new={'label':'Beta','expected_size':'7','reason':'New extent.'}
        after=self.prepare(before,[{'key':'Zeta','preimage':artifact_edits.row_hash(old),'row':None},
                                   {'key':'Beta','preimage':None,'row':new}])
        self.assertEqual(after,b'# Extents\nlabel,expected_size,reason\n"Alpha","4","Second extent."\r\nBeta,7,New extent.\r\n')

    def test_interleaved_csv_trivia_refuses_even_for_noop(self):
        self.assertIn('ARTIFACT_LAYOUT_UNSUPPORTED',service.PUBLIC_ERROR_CODES)
        for middle in (b'# Section B\n',b'\n',b' \t\n'):
            before=b'label,expected_size,reason\nZeta,3,First extent.\n'+middle+b'Alpha,4,Second extent.\n'
            for changes in ([],[{'key':'Beta','preimage':None,
                                'row':{'label':'Beta','expected_size':'7','reason':'New extent.'}}]):
                with self.subTest(middle=middle,changes=changes):
                    with self.assertRaisesRegex(ValueError,'^ARTIFACT_LAYOUT_UNSUPPORTED$'):self.prepare(before,changes)

    def test_csv_header_only_and_missing_final_newline(self):
        row={'label':'Alpha','expected_size':'4','reason':'Second extent.'}
        for before in (b'# Extents\r\nlabel,expected_size,reason\r\n',b''):
            with self.subTest(before=before):
                self.assertEqual(self.prepare(before,[]),before)
                ending=b'\r\n' if before else b'\n'
                expected=before or b'label,expected_size,reason\n'
                self.assertEqual(self.prepare(before,[{'key':'Alpha','preimage':None,'row':row}]),
                                 expected+b'Alpha,4,Second extent.'+ending)
        before=b'label,expected_size,reason\r\n"Alpha","4","Second extent."'
        self.assertEqual(self.prepare(before,[{'key':'Alpha','preimage':artifact_edits.row_hash(row),
                                              'row':{**row,'expected_size':'5'}}]),
                         b'label,expected_size,reason\r\nAlpha,5,Second extent.')

    def test_csv_creation_anchor_preserves_survivors_and_exposes_position(self):
        before=b'label,expected_size,reason\n"Zeta","3","First extent."\n"Tail","1","Tail extent."\n"Alpha","4","Second extent."\n'
        old=artifact_edits.read_rows(before,'extent_rows')[1]
        new={'label':'Whole','expected_size':'7','reason':'Combined extent.'}
        changes=[{'key':'Tail','preimage':artifact_edits.row_hash(old),'row':None},
                 {'key':'Whole','preimage':None,'row':new,'before_key':'Alpha'}]
        after=self.prepare(before,changes)
        self.assertEqual(after,before.replace(b'"Tail","1","Tail extent."',b'Whole,7,Combined extent.'))
        op={'kind':'extent_rows','preimage':digest(before),'reason':'Reviewed combined extent','changes':changes}
        preview=[r for r in artifact_edits.preview_rows([op]) if r['key']=='Whole']
        self.assertTrue(preview and all(r['insert_before_key']=='Alpha' for r in preview))
        review=artifact_edits.changes(before,after,op)
        self.assertEqual({(r['key'],r['row_index_before'],r['row_index_after']) for r in review},
                         {('Tail',1,None),('Whole',None,1)})
        another={'label':'More','expected_size':'2','reason':'Another extent.'}
        changes.append({'key':'More','preimage':None,'row':another,'before_key':'Alpha'})
        self.assertEqual(self.prepare(before,changes),after.replace(b'"Alpha"',b'More,2,Another extent.\n"Alpha"'))

    def test_csv_creation_anchor_cannot_move_an_existing_row_or_target_a_removed_row(self):
        before=b'label,expected_size,reason\nZeta,3,First extent.\nAlpha,4,Second extent.\n'
        old=artifact_edits.read_rows(before,'extent_rows')[0]
        new={'label':'Beta','expected_size':'7','reason':'New extent.'}
        create={'key':'Beta','preimage':None,'row':new,'before_key':'Zeta'}
        for anchor in ('Missing','Beta'):
            with self.subTest(anchor=anchor),self.assertRaisesRegex(ValueError,'^ARTIFACT_ROW_INVALID$'):
                self.prepare(before,[{**create,'before_key':anchor}])
        remove={'key':'Zeta','preimage':artifact_edits.row_hash(old),'row':None}
        for changes in ([remove,create],[create,remove]):
            with self.subTest(changes=changes),self.assertRaisesRegex(ValueError,'^ARTIFACT_ROW_INVALID$'):
                self.prepare(before,changes)
        change={'key':'Zeta','preimage':artifact_edits.row_hash(old),'row':{**old,'reason':'Revised extent.'},'before_key':'Alpha'}
        with self.assertRaisesRegex(ValueError,'^ARTIFACT_EDIT_SCHEMA$'):self.prepare(before,[change])


class WarningLayoutTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve();capture=self.root/'capture';capture.mkdir()
        declarations={name:name for name in ('Alpha','Beta','Zeta','Mid','New')}
        self.model=SimpleNamespace(capture=capture,declarations=declarations,ids=declarations,
            nodes=declarations,declaration_records={name:{} for name in declarations},name=lambda node:node)
        (capture/'producer.log').write_text("warning: `Alpha' defined but not used\nwarning: `Beta' defined but not used\n")
        self.path='projects/sample/'+artifact_edits.PATHS['warning_baseline']
        self.target=self.root/self.path;self.target.parent.mkdir(parents=True)
        self.op={'kind':'warning_baseline','reason':'Keep externally owned entries','preimage':None,
                 'entries':[{'declaration_id':'Alpha','rationale':'First reason.'},
                            {'declaration_id':'Beta','rationale':'Second reason.'}]}

    def prepare(self,before):
        self.target.write_bytes(before)
        self.op['preimage']=digest(before)
        return artifact_edits.prepare(self.root,{self.path:digest(before)},[self.op],'projects/sample/')

    def write(self,before):
        artifact_edits.warnings(self.root,self.model,[self.op],'projects/sample/',self.model,before)

    def test_noop_preserves_header_blank_lines_and_original_row_bytes(self):
        for before in (b'\n# symbol|rationale\n\n  # External entries\nAlpha|First reason.\nBeta|Second reason.\n',
                       b'# symbol|rationale\r\n\r\nAlpha | First reason.\r\nBeta|Second reason.',
                       b'Alpha|First reason.\nBeta|Second reason.\n\n# End of registry\n'):
            with self.subTest(before=before):
                self.prepare(before);self.write(before)
                self.assertEqual(self.target.read_bytes(),before)
                import json
                report=json.loads((self.model.capture/'warning-curation.json').read_text())
                self.assertEqual(report['transitions'],[])
                self.op['entries'].reverse();self.write(before)
                self.assertEqual(self.target.read_bytes(),before)
                self.op['entries'].reverse()

    def test_interleaved_comment_or_blank_refuses_preview_and_writer(self):
        self.assertIn('WARNING_LAYOUT_UNSUPPORTED',service.PUBLIC_ERROR_CODES)
        for middle in (b'# Section B: entries below share one owner\n',b'\n',b' \t\n',b'  # Section B\n'):
            with self.subTest(middle=middle):
                before=b'# symbol|rationale\nAlpha|First reason.\n'+middle+b'Beta|Second reason.\n'
                with self.assertRaisesRegex(ValueError,'WARNING_LAYOUT_UNSUPPORTED'):self.prepare(before)
                with self.assertRaisesRegex(ValueError,'WARNING_LAYOUT_UNSUPPORTED'):self.write(before)
                self.assertEqual(self.target.read_bytes(),before)
                self.assertFalse((self.model.capture/'warning-curation.json').exists())

    def test_empty_warning_set_preserves_a_file_containing_only_header_bytes(self):
        (self.model.capture/'producer.log').write_text('')
        self.op['entries']=[]
        for before in (b'',b'# Header without a final newline',b'\r\n# Header\r\n\r\n'):
            with self.subTest(before=before):
                self.prepare(before);self.write(before)
                self.assertEqual(self.target.read_bytes(),before)

    def test_changed_row_keeps_header_footer_and_untouched_row_spelling(self):
        before=b'\n# symbol|rationale\r\n\r\nAlpha | First reason.\r\nBeta|Second reason.\r\n\r\n# End\r\n'
        self.op['entries'][1]['rationale']='A revised ownership reason.'
        self.prepare(before);self.write(before)
        self.assertEqual(self.target.read_bytes(),before.replace(b'Beta|Second reason.',b'Beta|A revised ownership reason.'))

    def test_changed_warning_set_refuses_surviving_row_reorder(self):
        import difflib,json
        self.assertIn('WARNING_ORDER_CHANGED',service.PUBLIC_ERROR_CODES)
        before=b'# symbol|rationale\nZeta|External owner.\nAlpha|First reason.\nMid|Middle reason.\n'
        rows=artifact_edits.entries(before,'warning_baseline')
        (self.model.capture/'producer.log').write_text(''.join(
            "warning: `"+name+"' defined but not used\n" for name in rows))
        rows['Mid']['rationale']='Revised middle reason.'
        self.op['entries']=[{'declaration_id':name,'rationale':rows[name]['rationale']} for name in sorted(rows)]
        self.prepare(before)
        with self.assertRaisesRegex(ValueError,'^WARNING_ORDER_CHANGED$'):self.write(before)
        self.assertEqual(self.target.read_bytes(),before)
        self.assertFalse((self.model.capture/'warning-curation.json').exists())
        self.op['entries']=[{'declaration_id':name,'rationale':row['rationale']} for name,row in rows.items()]
        self.write(before);after=self.target.read_bytes()
        self.assertEqual(after,before.replace(b'Mid|Middle reason.',b'Mid|Revised middle reason.'))
        delta=list(difflib.ndiff(before.decode().splitlines(),after.decode().splitlines()))
        self.assertEqual(sum(line[:2] in ('- ','+ ') for line in delta),2)
        transitions=json.loads((self.model.capture/'warning-curation.json').read_text())['transitions']
        self.assertEqual([row['transition'] for row in transitions],['retain'])

    def test_new_warning_rows_can_be_inserted_between_surviving_rows(self):
        before=b'# symbol|rationale\nZeta|External owner.\nMid|Middle reason.\nAlpha|First reason.\n'
        expected=b'# symbol|rationale\nZeta|External owner.\nNew|New external owner.\nAlpha|First reason.\n'
        rows=artifact_edits.entries(expected,'warning_baseline')
        (self.model.capture/'producer.log').write_text(''.join(
            "warning: `"+name+"' defined but not used\n" for name in rows))
        self.op['entries']=[{'declaration_id':name,'rationale':row['rationale']} for name,row in rows.items()]
        self.prepare(before);self.write(before)
        self.assertEqual(self.target.read_bytes(),expected)

    def test_new_rows_inherit_header_line_ending(self):
        for ending in (b'\r\n',b'\r',b'\n'):
            with self.subTest(ending=ending):
                before=b'# symbol|rationale'+ending+ending
                self.prepare(before);self.write(before)
                self.assertEqual(self.target.read_bytes(),
                    before+b'Alpha|First reason.'+ending+b'Beta|Second reason.'+ending)


class RawRamRefreshTests(unittest.TestCase):
    def encoded(self,rows,fields=None):
        import csv,io
        stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=fields or self.fields,lineterminator='\n')
        writer.writeheader();writer.writerows(rows);return stream.getvalue().encode()

    def setUp(self):
        self.fields=list(artifact_edits.RAW_RAM_PROTECTED+artifact_edits.RAW_RAM_GENERATED)
        self.row=dict(zip(self.fields,['0x0040','symbolized','Scratch','Reviewed owner.',
            '7','yes','4','2','3','1','Reader:3','Writer:1']))
        self.before=self.encoded([self.row])

    def test_refresh_exposes_facts_but_cannot_change_judgments(self):
        after={**self.row,'distinct_owner_count':'1','top_writers':'Owner:1'}
        changes=artifact_edits.raw_ram_changes(self.before,self.encoded([after]))
        self.assertEqual(changes,[{'key':'0x0040','row_index':0,
            'changed_fields':['distinct_owner_count','top_writers'],
            'before':{'distinct_owner_count':'2','top_writers':'Writer:1'},
            'after':{'distinct_owner_count':'1','top_writers':'Owner:1'}}])
        for field in ('status','proposed_symbol','notes','last_pass_reviewed'):
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'RAW_RAM_JUDGMENT_CHANGED'):
                artifact_edits.raw_ram_changes(self.before,self.encoded([{**after,field:'changed'}]))

    def test_refresh_keeps_address_order_schema_and_membership(self):
        other={**self.row,'addr_hex':'0x0840'}
        before=self.encoded([self.row,other])
        self.assertEqual(artifact_edits.raw_ram_changes(before,before),[])
        self.assertEqual(artifact_edits.raw_ram_changes(None,None),[])
        for after in (None,self.encoded([self.row]),self.encoded([other,self.row]),
                      self.encoded([self.row,self.row]),self.encoded([self.row,other,{**other,'addr_hex':'0x0041'}]),
                      self.encoded([self.row,other],list(reversed(self.fields))),before+b'bad,row\n'):
            with self.subTest(after=after),self.assertRaisesRegex(ValueError,'RAW_RAM_REFRESH_UNSUPPORTED'):
                artifact_edits.raw_ram_changes(before,after)
        with self.assertRaisesRegex(ValueError,'RAW_RAM_REFRESH_UNSUPPORTED'):
            artifact_edits.raw_ram_changes(None,before)

    def test_inventory_admits_only_protected_refresh(self):
        with tempfile.TemporaryDirectory() as root:
            root=Path(root).resolve();base=root/'base';candidate=root/'candidate';project='projects/sample/'
            raw=project+artifact_edits.RAW_RAM_PATH;source=project+'asm/sample.asm'
            policy=project+'docs/reverse_engineering/inventory/kpis.conf'
            data={raw:self.before,source:b'.END\n',policy:b'MAX_VALUE=1\n'}
            for folder in (base,candidate):
                for path,value in data.items():
                    file=folder/path;file.parent.mkdir(parents=True,exist_ok=True);file.write_bytes(value)
            record={'checkout':str(base),'manifest':{p:digest(v) for p,v in data.items()}}
            stub=SimpleNamespace(project=project,source=source,ledger=project+'docs/reverse_engineering/inventory/renames.csv',
                generated=set(),state={'current':'G','generations':{'G':record}},model=lambda g:None,
                manifest_paths=lambda record,operations:list(data),
                ownership=lambda p,project,source:service.file_ownership(p,project,source))
            operations=[{'kind':'comment_replace'}]
            (candidate/raw).write_bytes(self.encoded([{**self.row,'distinct_owner_count':'1'}]))
            self.assertEqual(RenameService.inventory_result(stub,candidate,None,operations)['inventory_gates'],
                             'refreshed and verified')
            stub.readers=lambda:{}
            stub.review_metadata=lambda generation,base_generation:{}
            stub.state['generations']['After']={'base':'G','provenance':[],'checkout':str(candidate),
                'manifest':{p:digest((candidate/p).read_bytes()) for p in data}}
            page=RenameService.review.__wrapped__(stub,'After','G',1)
            self.assertEqual(page['total_pages'],2)
            self.assertEqual(len(page['changes']),1)
            row=page['changes'][0]
            self.assertEqual((row['kind'],row['operation_kind'],row['ownership']),
                             ('artifact_change','raw_ram_refresh','refresh-generated'))
            self.assertEqual(row['row']['after'],{'distinct_owner_count':'1'})
            self.assertEqual(row['before_sha256'],digest(self.before))
            self.assertEqual(row['after_sha256'],digest((candidate/raw).read_bytes()))
            (candidate/raw).write_bytes(self.encoded([{**self.row,'notes':'Unapproved judgment'}]))
            with self.assertRaisesRegex(ValueError,'RAW_RAM_JUDGMENT_CHANGED'):
                RenameService.inventory_result(stub,candidate,None,operations)
            (candidate/raw).write_bytes(self.before);(candidate/policy).write_bytes(b'MAX_VALUE=2\n')
            with self.assertRaisesRegex(ValueError,'FORBIDDEN_PATH'):
                RenameService.inventory_result(stub,candidate,None,operations)


class OwnershipTests(unittest.TestCase):
    def test_complete_warning_set_has_separate_count_and_byte_bounds(self):
        row={'declaration_id':'record','rationale':'External reader retains this allocation.'}
        op={'kind':'warning_baseline','preimage':None,'reason':'Complete diagnostics','entries':[row]*336}
        self.assertEqual(artifact_edits.operations([op]),[op])
        op['entries']=[{'declaration_id':'r','rationale':'x'}]*(artifact_edits.MAX_WARNING_ENTRIES+1)
        with self.assertRaisesRegex(ValueError,'ARTIFACT_EDIT_SCHEMA'):artifact_edits.operations([op])
        op['entries']=[{**row,'rationale':'x'*2000}]*200
        with self.assertRaisesRegex(ValueError,'ARTIFACT_EDIT_SCHEMA'):artifact_edits.operations([op])

    def test_unregistered_suffixes_and_reserved_paths_never_grant_writes(self):
        project='projects/sample/';source=project+'asm/sample.asm'
        for tail in ('new.md','new.csv','new.txt','new.json'):
            self.assertEqual(service.file_ownership(project+'docs/'+tail,project,source),'forbidden')
        for path in ('docs/reverse_engineering/Reviews/new.md','docs/reverse_engineering/Inventory/new.md',
                     'docs/../new.md','docs/.private/new.md'):
            with self.assertRaisesRegex(ValueError,'OWNERSHIP_MANIFEST_INVALID'):ownership.registry([path])
        paths=ownership.registry(['docs/new.md'])['authored_documents']
        self.assertEqual(service.file_ownership(project+'docs/new.md',project,source,paths),'authored')
        self.assertEqual(service.file_ownership(project+'docs/reverse_engineering/inventory/kpis.conf',project,source,paths),'kpi-wrapper')


if __name__=='__main__':unittest.main()
