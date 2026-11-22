"""Dense global labels must not make a lexical source span impractical."""
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
from structured_pass import bridge, edit_contract, navigation, operation_contract, paging
from structured_pass.retained_service import RetainedReviewService
import structured_pass_fixture as fixture


def expand(page):
    if page.get('encoding')!='source-records-columnar-v1':return page['records']
    result=[]
    for values in page['records']:
        row={**page['constants'],**dict(zip(page['schemas'][values[0]],values[1:]))}
        if 'layout' in row:
            row['layout']={'length':row['layout'],**{key:row[key] for key in
                ('cpu_address','output_offset','bytes','segment_id')}}
        result.append(row)
    return result


class CompactRecordTests(unittest.TestCase):
    def test_missing_null_and_duplicate_layout_round_trip(self):
        rows=[{'record_id':'a','name':None,'span':[1,1,1,2]},
              {'record_id':'b','span':[2,1,2,2],'cpu_address':10,'output_offset':2,
               'bytes':[234],'segment_id':'g1','layout':{'cpu_address':10,
               'output_offset':2,'bytes':[234],'segment_id':'g1','length':1}}]
        page={'records':rows,'comments':[{'text':'Keep the exact comment.'}]}
        packed=navigation.compact_records(page)
        self.assertEqual(expand(packed),rows)
        self.assertNotIn('name',expand(packed)[1])
        self.assertIsNone(expand(packed)[0]['name'])
        self.assertEqual(packed['comments'],page['comments'])
        for field in ('cpu_address','bytes'):
            changed={**rows[1],'layout':{**rows[1]['layout'],field:None}}
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'SOURCE_MODEL_JOIN'):
                navigation.compact_records({'records':[changed]})
        self.assertEqual(expand(navigation.compact_records({'records':[]})),[])


def dense_source(root, **unused):
    root=Path(root);root.mkdir(parents=True)
    source=root/'dense.asm';reference=root/'reference.nes'
    body=bytes([0xea])*25
    padding=b'A'*(16384-len(body))
    text=b'.ORG $4000\nPadding:\n.DB "'+padding+b'"\n.ORG $8000\n'
    for index in range(8):
        text+=f'L{0x9000+index:04X}:\nNOP\n; Synthetic gap comment.\nNOP\nNOP\n'.encode()
    text+=b'.ORG $8000\nOtherSegment:\nNOP\n.END\n'
    source.write_bytes(text)
    reference.write_bytes(b'NES\x1a'+bytes([1])+bytes(11)+padding+body)
    return source,reference


class NavigationSpanTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.temp=tempfile.TemporaryDirectory(prefix='source-span-',dir=ROOT/'tmp')
        self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name)
        with patch.object(fixture,'fixture',dense_source):self.c=fixture.prepare(self.root)
        self.g=self.c.editor.state['current']

    def read(self,role='implementer',**arguments):
        requests=[{'id':1,'method':'tools/call','params':{'name':'operation',
            'arguments':{'operation':'navigate','arguments':{'generation':self.g,**arguments}}}}]
        output=io.StringIO()
        bridge.mcp(self.c.root,role,'corridor',io.StringIO(json.dumps(requests[0])+'\n'),output)
        wire=output.getvalue();self.assertLessEqual(len(wire.encode()),paging.MAX_BYTES)
        result=json.loads(wire)['result'];value=json.loads(result['content'][0]['text'])
        return result.get('isError',False),value

    def span(self,role='implementer',**selection):
        offset=0;rows=[];pages=[]
        while offset is not None:
            error,page=self.read(role,view='records',span='segment',offset=offset,limit=40,**selection)
            self.assertFalse(error,page);self.assertEqual(page['generation'],self.g)
            self.assertLessEqual(len(page['records']),40)
            if pages:
                self.assertEqual(pages[-1]['next_record_id'],page['records'][0]['record_id'])
            rows+=page['records'];pages.append(page);offset=page['next_offset']
        return rows,pages

    def test_dense_labels_cross_in_two_transport_calls_for_both_roles(self):
        for role in ('implementer','reviewer'):
            with self.subTest(role=role):
                rows,pages=self.span(role,symbol='L9000')
                self.assertEqual([r['name'] for r in rows if r['kind']=='LABEL_NODE'],
                                 [f'L{0x9000+i:04X}' for i in range(8)])
                self.assertEqual(len(rows),32)
                self.assertLessEqual(len(pages),2)
                self.assertIsNone(pages[-1]['next_record_id'])
                self.assertEqual(len({r['segment_id'] for r in rows}),1)
                self.assertNotIn('ORG_NODE',[r['kind'] for r in rows])
                self.assertNotIn('OtherSegment',[r.get('name') for r in rows])

    def test_default_label_view_is_unchanged(self):
        error,page=self.read(view='records',symbol='L9000',limit=40)
        self.assertFalse(error);self.assertEqual(len(page['records']),4)
        self.assertIsNone(page['next_offset'])
        self.assertNotIn('span',page)
        explicit=self.read(view='records',symbol='L9000',span='label',limit=40)[1]
        self.assertEqual(page,explicit)
        following=self.read(view='records',record_id=page['scope']['next_record_id'])[1]
        self.assertEqual(following['records'][0]['name'],'L9001')

    def test_origin_end_and_single_record_selections(self):
        rows,pages=self.span(symbol='OtherSegment')
        self.assertEqual([r['kind'] for r in rows],['LABEL_NODE','INSTRUCTION_NODE'])
        end=pages[-1]['scope']['boundary_record_id']
        self.assertEqual([r['kind'] for r in self.span(record_id=end)[0]],['END_NODE'])
        _,first=self.span(symbol='L9000')
        origin=first[-1]['scope']['boundary_record_id']
        self.assertEqual([r['kind'] for r in self.span(record_id=origin)[0]],['ORG_NODE'])
        self.assertNotEqual(first[0]['scope']['segment_id'],pages[0]['scope']['segment_id'])

    def test_segment_identity_change_without_origin_stops_span(self):
        nav=navigation.Navigation(self.c.editor.model(self.g))
        boundary=nav.select('L9002',None)
        # Isolate the defensive location check from the separately tested ORG
        # stop; this control changes native-layout metadata, not source parsing.
        nav.layout={n:dict(location) for n,location in nav.layout.items()}
        nav.layout[boundary]['segment_id']='different-segment'
        page=nav.query('records',symbol='L9000',span='segment',limit=40)
        self.assertEqual(len(page['records']),8)
        self.assertEqual(page['scope']['boundary_record_id'],nav.m.ids[boundary])

    def test_generation_and_selector_refusals(self):
        for extra,code in [({'generation':'G-unknown'},'UNKNOWN_GENERATION'),
                ({'symbol':None,'record_id':'unknown'},'NAVIGATION_RECORD_REQUIRED'),
                ({'span':'routine'},'REQUEST_SCHEMA'),({'view':'uses'},'REQUEST_SCHEMA'),
                ({'limit':41},'REQUEST_SCHEMA')]:
            with self.subTest(extra=extra):
                error,page=self.read(**({'view':'records','symbol':'L9000','span':'segment'}|extra))
                self.assertTrue(error);self.assertEqual(page['error'],code)

    def test_size_cap_shortens_pages_without_losing_comments(self):
        model=self.c.editor.model(self.g);nav=navigation.Navigation(model)
        start=nav.position[nav.select('L9000',None)]
        selected=nav.statements[start:start+32]
        comments=[{'line':model.facts[n]['span'][0],'text':'\\"'*300,'record_id':'comment-'+str(n)}
                  for n in selected]
        # Large serialized comments exercise whole-record trimming, including
        # the MCP escaping overhead. No source or assembler facts are replaced.
        with patch('structured_pass.rename_service.comments',return_value=comments):
            rows,pages=self.span(symbol='L9000')
        self.assertEqual(len(rows),32)
        self.assertGreater(len(pages),2)
        self.assertEqual([c for page in pages for c in page['comments']],comments)
        huge=[{**comments[0],'text':'x'*paging.MAX_BYTES}]
        with patch('structured_pass.rename_service.comments',return_value=huge):
            error,page=self.read(view='records',symbol='L9000',span='segment',limit=40)
        self.assertTrue(error);self.assertEqual(page['error'],'RESPONSE_TOO_LARGE')

    def test_reference_delivers_span_values_and_counting_rule(self):
        ref=edit_contract.reference()
        self.assertEqual(ref['request_counting'],operation_contract.REQUEST_COUNTING)
        self.assertEqual(ref['question_budget']['text_response_bytes'],409600)
        self.assertIn('409600 bytes',ref['request_counting'])
        self.assertIn('Narrow',ref['request_counting'])
        for role in ('implementer','reviewer','retained-reviewer'):
            entry=ref['arguments'][role]['navigate']
            self.assertIn('span',entry['optional'])
            self.assertEqual(entry['values']['span']['enum'],list(navigation.SPANS))
            self.assertIn('records_compact',entry['values']['view']['enum'])
        self.assertIn('next_offset',ref['view_arguments']['navigate']['records_span']['continuation'])
        self.assertEqual(ref['view_arguments']['navigate']['records_compact']['decode'],navigation.COMPACT_HELP)

    def test_compact_records_preserve_all_fields_and_preimages(self):
        expected,_=self.span(symbol='L9000')
        for role in ('implementer','reviewer'):
            for span in ('label','segment'):
                with self.subTest(role=role,span=span):
                    rows=[];offset=0;previous=None
                    while offset is not None:
                        error,page=self.read(role,view='records_compact',symbol='L9000',
                                             span=span,limit=7,offset=offset)
                        self.assertFalse(error,page);self.assertEqual(page['generation'],self.g)
                        self.assertEqual(page['encoding'],'source-records-columnar-v1')
                        decoded=expand(page)
                        if previous is not None and span=='segment':
                            self.assertEqual(previous,decoded[0]['record_id'])
                        rows+=decoded;offset=page['next_offset'];previous=page.get('next_record_id')
                    self.assertEqual(rows,expected if span=='segment' else expected[:4])
                    self.assertTrue(all('preimage_sha256' in row for row in rows))
                    self.assertNotIn('OtherSegment',[r.get('name') for r in rows])

    def test_compact_size_pagination_keeps_every_record_and_comment(self):
        model=self.c.editor.model(self.g);nav=navigation.Navigation(model)
        start=nav.position[nav.select('L9000',None)]
        selected=nav.statements[start:start+32]
        comments=[{'line':model.facts[n]['span'][0],'text':'\\"'*500,'record_id':'comment-'+str(n)}
                  for n in selected]
        for span,count in [('label',4),('segment',32)]:
            rows=[];seen=[];offset=0;pages=0
            with patch('structured_pass.rename_service.comments',return_value=comments):
                while offset is not None:
                    error,page=self.read(view='records_compact',symbol='L9000',span=span,limit=40,offset=offset)
                    self.assertFalse(error,page);pages+=1;rows+=expand(page);seen+=page['comments']
                    offset=page['next_offset']
            self.assertEqual(len(rows),count);self.assertEqual(seen,comments[:count])
            if span=='segment':self.assertGreater(pages,2)
        with patch('structured_pass.rename_service.comments',return_value=[{**comments[0],'text':'x'*paging.MAX_BYTES}]):
            for span in ('label','segment'):
                error,page=self.read(view='records_compact',symbol='L9000',span=span,limit=40)
                self.assertTrue(error);self.assertEqual(page['error'],'RESPONSE_TOO_LARGE')

    def test_compact_label_continuation_keeps_inter_record_comments(self):
        from structured_pass import review_pages
        wire_size=review_pages.wire_size
        def two_records(page):
            return review_pages.BUDGET if len(page.get('records',[]))>2 else wire_size(page)
        with patch.object(review_pages,'wire_size',side_effect=two_records):
            error,first=self.read(view='records_compact',symbol='L9000',limit=40)
            self.assertFalse(error);self.assertEqual(first['next_offset'],2)
            error,last=self.read(view='records_compact',symbol='L9000',limit=40,offset=2)
            self.assertFalse(error);self.assertIsNone(last['next_offset'])
        self.assertEqual([c['text'] for c in first['comments']+last['comments']],
                         ['; Synthetic gap comment.'])

    def test_restored_review_reads_the_same_generation_span(self):
        c=self.c;m=c.editor.model(self.g);n=m.declarations['L9000']
        operations=[{'kind':'rename','declaration_id':m.ids[n],'old_name':'L9000','new_name':'Entry',
                     'preimage':m.statement(n)['preimage_sha256']},
                    {'kind':'ledger_append','path':c.editor.ledger,
                     'preimage':c.editor.state['generations'][self.g]['manifest'][c.editor.ledger],
                     'rows':[{'old_name':'L9000','new_name':'Entry','reason':'Synthetic entry',
                              'confidence':'high','pass_id':'1'}]},*fixture.closeout_ops(c,self.g)]
        preview=c.dispatch('preview',{'generation':self.g,'operations':operations},'implementer')
        cid=c.dispatch('confirm',{'generation':self.g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
        self.assertEqual(c.dispatch('validate',{'cid':cid},'implementer')['status'],'validated')
        published=c.dispatch('publish',{'cid':cid},'implementer')
        reader=RetainedReviewService.from_publication(self.root/'reader',self.root/'store',published['review']['artifact_id'])
        request={'view':'records','span':'segment','symbol':'Entry','limit':40}
        live=c.dispatch('navigate',{'generation':published['generation'],**request},'reviewer')
        artifact=published['review']['artifact_id']
        restored=reader.dispatch('navigate',{'generation':artifact,**request},'reviewer')
        self.assertEqual({k:v for k,v in live.items() if k!='generation'},
                         {k:v for k,v in restored.items() if k!='generation'})
        with self.assertRaisesRegex(ValueError,'UNKNOWN_GENERATION'):
            reader.dispatch('navigate',{'generation':published['generation'],**request},'reviewer')
        request['view']='records_compact'
        compact=reader.dispatch('navigate',{'generation':artifact,**request},'reviewer')
        def complete(view,page):
            rows=list(expand(page))
            while page['next_offset'] is not None:
                page=reader.dispatch('navigate',{'generation':artifact,**request,
                    'view':view,'offset':page['next_offset']},'reviewer')
                rows+=expand(page)
            return rows
        self.assertEqual(complete('records_compact',compact),complete('records',restored))
        self.assertEqual(compact['generation'],artifact)
        source_args={**request,'view':'source','limit':128}
        reading=reader.dispatch('navigate',{'generation':artifact,**source_args},'reviewer')
        from structured_pass.corridor_capacity import expand as source_expand
        expected=complete('records',restored)
        actual=source_expand(reading)
        self.assertEqual([r['record_id'] for r in actual],[r['record_id'] for r in expected])
        live_read=c.dispatch('navigate',{'generation':published['generation'],**source_args},'reviewer')
        self.assertEqual({k:v for k,v in reading.items() if k!='generation'},
                         {k:v for k,v in live_read.items() if k!='generation'})
        from structured_pass_edit_records_test import decode, full_inputs
        edit_args={'view':'edit','record_id':[r['record_id'] for r in expected],'limit':40}
        editing=reader.dispatch('navigate',{'generation':artifact,**edit_args},'reviewer')
        for role in ('implementer','reviewer'):
            current=c.dispatch('navigate',{'generation':published['generation'],**edit_args},role)
            self.assertEqual({k:v for k,v in editing.items() if k!='generation'},
                             {k:v for k,v in current.items() if k!='generation'})
        current_model=c.editor.model(published['generation'])
        self.assertEqual(decode(editing),[full_inputs(current_model,r['record_id']) for r in expected[:40]])

        with self.assertRaisesRegex(ValueError,'UNKNOWN_GENERATION'):
            reader.dispatch('navigate',{'generation':published['generation'],**request},'reviewer')


if __name__=='__main__':unittest.main()
