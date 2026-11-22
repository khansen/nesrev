"""Lossless RAM transport, generation binding and real service read paths."""
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import bridge,evidence_views,ram_evidence,review_pages
from structured_pass.launcher import Corridor
from structured_pass.retained_service import RetainedReviewService
import structured_pass_evidence_test as evidence_fixture
from structured_pass_fixture import prepare,closeout_ops


def expand(page):
    rows=[{**page['constants'],**dict(zip(page['columns'],values))} for values in page['records']]
    if page.get('encoding') in ('ram-columnar-summary-v1','ram-set-columnar-v1'):
        for row in rows:
            for field,values in page['dictionaries'].items():row[field]=values[str(row[field])]
    return rows


class CompactTests(unittest.TestCase):
    setUp=evidence_fixture.EvidenceTests.setUp
    ident=evidence_fixture.EvidenceTests.ident

    def collect(self,view,**args):
        rows=[];offset=0;calls=0
        while True:
            page=ram_evidence.query(self.model,'G-test',view,offset,128,**args);calls+=1
            self.assertLessEqual(review_pages.wire_size(page),24576)
            self.assertFalse(set(page['constants'])&set(page['columns']))
            rows.extend(expand(page));offset=page['next_offset']
            if offset is None:return rows,page,calls

    def test_expansion_equals_all_legacy_facts_across_ranges_and_aliases(self):
        identifiers=set()
        for selector in [{'address':v} for v in (0,0x40,0xFE,0xFF,0x100,0x400,0x6000,0xFFFF)]+[
                {'record_id':self.ident(n)} for n in ('Cell','Alias','ValueMask','DisplacedCell')]:
            with self.subTest(selector=selector):
                own,page,_=self.collect('ram_compact',**selector)
                shared,_,_=self.collect('ram_shared',set_id=page['shared']['set_id'])
                identifiers.add(page['shared']['set_id'])
                expanded=[{**r,**page['selection']} for r in own+shared]
                expected=evidence_views.memory(self.model,**selector)
                self.assertCountEqual(expanded,expected)
                self.assertEqual(len(expanded),page['total_evidence_records'])
                self.assertEqual(len(shared),page['shared']['total_records'])
                self.assertTrue(all(r['category']=='unresolved_indirect_destination' for r in shared))
        self.assertEqual(len(identifiers),1)

    def test_set_expansion_equals_every_per_byte_fact(self):
        addresses=[0,0x40,0xFE,0xFF,0x100,0x400,0x6000,0xFFFF]
        rows,page,_=self.collect('ram_set',address=addresses)
        expanded=[{**{k:v for k,v in row.items() if k!='addresses'},
                   'requested_address':a,'requested_declaration_id':None}
                  for row in rows for a in row['addresses']]
        self.assertCountEqual(expanded,[r for a in addresses for r in evidence_views.memory(self.model,address=a)])
        self.assertEqual(len(expanded),page['total_evidence_records'])
        indirect=[r for r in rows if r['category']=='unresolved_indirect_destination']
        self.assertTrue(indirect)
        self.assertTrue(all(r['addresses']==sorted(addresses) for r in indirect))
        self.assertEqual(len(indirect),len({r['record_id'] for r in indirect}))
        self.assertTrue(all('preimage' in r for r in rows))
        for bad in ([],[1,1],[True],[65536],list(range(129)),1):
            with self.subTest(bad=bad),self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
                self.collect('ram_set',address=bad)

    def test_stale_foreign_and_changed_shared_set_refused(self):
        page=ram_evidence.query(self.model,'G-test','ram_compact',address=0)
        ident=page['shared']['set_id']
        for generation,token in [('G-new',ident),('G-test','R-forged')]:
            with self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
                ram_evidence.query(self.model,generation,'ram_shared',set_id=token)
        with patch.object(self.model,'source',b'changed'):
            with self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
                ram_evidence.query(self.model,'G-test','ram_shared',set_id=ident)
        with patch.object(self.model,'instructions',{}):
            with self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
                ram_evidence.query(self.model,'G-test','ram_shared',set_id=ident)

    def test_summary_preserves_every_access_and_unknown_across_ranges(self):
        omitted={'preimage','span','cpu_address','output_offset','segment_id'}
        for selector in [{'address':a} for a in (0,0x40,0xFF,0x100,0x6000,0xFFFF)]+[
                {'record_id':self.ident('Cell')},{'record_id':self.ident('Alias')}]:
            with self.subTest(selector=selector):
                rows,page,_=self.collect('ram_summary',**selector)
                original=evidence_views.memory(self.model,**selector)
                self.assertEqual(rows,[{k:v for k,v in row.items() if k not in omitted} for row in original])
                self.assertEqual(len(rows),page['total_evidence_records'])
                self.assertEqual(set(page['omitted_fields']),omitted)
                self.assertNotIn('shared',page)
                self.assertEqual(page['generation'],'G-test')
                self.assertIn('not an edit preimage',page['coverage'])
                for row in rows:self.assertIn(row['record_id'],self.model.nodes)
        with patch.object(self.model,'instructions',{}):
            rows,page,_=self.collect('ram_summary',address=0)
            self.assertEqual(rows,[]);self.assertEqual(page['total_evidence_records'],0)

    def test_empty_view_and_shared_set_are_explicit(self):
        with patch.object(self.model,'instructions',{}):
            rows,page,_=self.collect('ram_compact',address=0x6000)
            self.assertEqual(rows,[]);self.assertEqual(page['total_evidence_records'],0)
            self.assertEqual(page['selection']['requested_address'],0x6000)
            shared,part,_=self.collect('ram_shared',set_id=page['shared']['set_id'])
            self.assertEqual(shared,[]);self.assertEqual(part['total_records'],0)
            self.assertIsNone(part['next_offset'])

    def test_summary_pages_carry_complete_dictionaries_under_size_limit(self):
        original=evidence_views.memory(self.model,address=0)[0]
        rows=[{**original,'record_id':'record-'+str(i),'category':'indexed_other_base_possible',
               'memory_access':{'data':{'kind':'write','address':i,'index_register':'X',
                                        'via_pointer':False},'pointer':None}} for i in range(512)]
        offset=0;actual=[];calls=0
        with patch.object(evidence_views,'memory',return_value=rows):
            while offset is not None:
                page=ram_evidence.query(self.model,'G-test','ram_summary',offset,128,address=0)
                self.assertLessEqual(review_pages.wire_size(page),24576)
                decoded=expand(page);actual.extend(decoded);calls+=1
                for field,values in page['dictionaries'].items():
                    encoded=[{**page['constants'],**dict(zip(page['columns'],v))}[field]
                             for v in page['records']]
                    self.assertEqual(set(values),{str(v) for v in encoded})
                offset=page['next_offset']
        self.assertGreater(calls,4)
        self.assertEqual(actual,[{k:v for k,v in r.items() if k not in
            {'preimage','span','cpu_address','output_offset','segment_id'}} for r in rows])

    def test_exact_full_and_later_pages_and_wire_ceiling(self):
        rows=[{'id':i,'text':str(i)+'\\"\n\u263a'*180,'same':None} for i in range(129)]
        observed=[];offset=0;pages=0
        while True:
            page=ram_evidence.packed(rows,{'generation':'G-test'},offset,128);pages+=1
            observed.extend(expand(page));self.assertLessEqual(review_pages.wire_size(page),24576)
            offset=page['next_offset']
            if offset is None:break
        self.assertGreater(pages,1);self.assertEqual(observed,rows)
        full=ram_evidence.packed([{'id':i,'same':True} for i in range(128)],{},0,128)
        self.assertEqual(len(full['records']),128);self.assertIsNone(full['next_offset'])
        self.assertEqual(full['constants'],{'same':True})
        self.assertEqual(full['columns'],['id'])
        with self.assertRaisesRegex(ValueError,'RESPONSE_TOO_LARGE'):
            ram_evidence.packed([{'text':'x'*30000}],{},0,128)
        for invalid in (0,129,True):
            with self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
                ram_evidence.packed(rows,{},0,invalid)

    def test_constants_preserve_json_types_and_duplicate_count(self):
        values=[False,0,0.0,{'nested':True},{'nested':1},None,[],{}]
        for group in (values,[False,0,0.0],[{'nested':True},{'nested':1}]):
            rows=[{'value':v,'shared':'fixed'} for v in group]
            result=ram_evidence.packed(rows,{},0,128)
            self.assertEqual(json.dumps(expand(result),sort_keys=True),json.dumps(rows,sort_keys=True))
            self.assertNotIn('value',result['constants'])
        duplicate=ram_evidence.packed([{'value':None}]*4,{},0,128)
        self.assertEqual(duplicate['columns'],[]);self.assertEqual(duplicate['records'],[[]]*4)
        self.assertEqual(expand(duplicate),[{'value':None}]*4)


class CompactLifecycleTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.tmp=tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='compact-test-');self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)

    def test_corridor_and_retained_generations_use_the_same_public_identity(self):
        c=prepare(self.root);g=c.editor.state['current']
        args={'generation':g,'view':'ram_compact','address':0x40,'limit':128}
        original=c.dispatch('evidence',args,'reviewer')
        requests=[{'jsonrpc':'2.0','id':0,'method':'tools/list'},
            {'jsonrpc':'2.0','id':1,'method':'tools/call','params':{'name':'operation',
             'arguments':{'operation':'evidence','arguments':args}}}]
        output=io.StringIO()
        bridge.mcp(c.root,'reviewer',input_stream=io.StringIO(''.join(json.dumps(r)+'\n' for r in requests)),output_stream=output)
        lines=output.getvalue().splitlines();responses=[json.loads(line) for line in lines]
        self.assertTrue(all(len(line.encode())+1<=24576 for line in lines))
        self.assertIn('ram_compact',responses[0]['result']['tools'][0]['description'])
        delivered=json.loads(responses[1]['result']['content'][0]['text'])
        self.assertEqual(delivered.pop('volume')['response_bytes'],len(lines[1].encode())+1)
        self.assertEqual(delivered,original)
        for role in ('implementer','reviewer'):
            request={'jsonrpc':'2.0','id':2,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':'evidence','arguments':{**args,'view':'ram_summary'}}}}
            output=io.StringIO()
            bridge.mcp(c.root,role,'corridor',io.StringIO(json.dumps(request)+'\n'),output)
            wire=output.getvalue();payload=json.loads(wire)['result']
            self.assertFalse(payload.get('isError'),payload)
            summary=json.loads(payload['content'][0]['text'])
            self.assertEqual(summary.pop('volume')['response_bytes'],len(wire.encode()))
            self.assertEqual(summary,c.dispatch('evidence',{**args,'view':'ram_summary'},role))
        for unsupported in ({'public_generation':'G-forged'},{'analogue_index':0}):
            with self.assertRaises(ValueError):c.dispatch('evidence',{**args,**unsupported},'reviewer')
        old_public=None
        for note in ('First synthetic read publication.','Second synthetic read publication.'):
            g=c.editor.state['current']
            preview=c.dispatch('preview',{'generation':g,'operations':closeout_ops(c,g,notes=note)},'implementer')
            cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
            self.assertEqual(c.dispatch('validate',{'cid':cid},'implementer')['status'],'validated')
            pub=c.dispatch('publish',{'cid':cid},'implementer');ticket=pub['review']['artifact_id']
            c=Corridor(c.root)
            page=c.dispatch('evidence',{**args,'generation':ticket},'reviewer')
            self.assertNotEqual(page['shared']['set_id'],original['shared']['set_id'])
            shared_args={'generation':ticket,'view':'ram_shared','set_id':page['shared']['set_id'],'limit':128}
            first=c.dispatch('evidence',shared_args,'reviewer')
            retained=RetainedReviewService.from_publication(self.root/ticket,c.config['store'],ticket)
            second=retained.dispatch('evidence',shared_args,'reviewer')
            self.assertEqual(first,second)
            self.assertEqual(page,retained.dispatch('evidence',{**args,'generation':ticket},'reviewer'))
            summary_args={**args,'generation':ticket,'view':'ram_summary'}
            summary=c.dispatch('evidence',summary_args,'reviewer')
            self.assertEqual(summary['generation'],ticket)
            self.assertEqual(summary,retained.dispatch('evidence',summary_args,'reviewer'))
            set_args={**args,'generation':ticket,'view':'ram_set','address':[0x40,0x41]}
            grouped=c.dispatch('evidence',set_args,'reviewer')
            self.assertEqual(grouped['generation'],ticket)
            self.assertEqual(grouped,retained.dispatch('evidence',set_args,'reviewer'))
            for stale in [original['shared']['set_id']]+([old_public] if old_public else []):
                with self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
                    c.dispatch('evidence',{**shared_args,'set_id':stale},'reviewer')
            old_public=page['shared']['set_id']


if __name__=='__main__':unittest.main()
