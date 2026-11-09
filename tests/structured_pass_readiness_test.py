"""Bounded diagnostics and compact view controls; no provider inference."""
import copy
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import gate_diagnostics,rename_service,review_pages
from structured_pass.service import ServiceError


class ReviewPackingTests(unittest.TestCase):
    def envelope(self, offset, count):
        return {'generation':'new','base_generation':'old','offset':offset,
                'changes':[], 'total_pages':count+1, 'total_changes':count,
                'next_offset':1 if offset==0 and count else None}

    def collect(self, groups, limit):
        offset=1;seen=[];pages=[]
        while offset is not None:
            page=review_pages.pack(self.envelope(offset,len(groups)),iter(groups[offset-1:]),limit)
            self.assertLessEqual(review_pages.wire_size(page),review_pages.BUDGET)
            self.assertTrue(page['changes'])
            self.assertTrue(page['next_offset'] is None or page['next_offset']>offset)
            seen+=page['changes'];pages.append(page);offset=page['next_offset']
        return seen,pages

    def test_cap_and_types_refuse(self):
        for offset,limit in [(-1,1),(True,1),(1.0,1),(0,0),(0,41),(0,True),(0,1.0),(0,None)]:
            with self.subTest(offset=offset,limit=limit):
                with self.assertRaisesRegex(ValueError,'^invalid pagination$'):
                    review_pages.pack(self.envelope(offset,1),iter([[{'id':'a'}]]),limit)
        groups=[[{'id':i}] for i in range(41)]
        page=review_pages.pack(self.envelope(1,41),iter(groups),40)
        self.assertEqual([x['id'] for x in page['changes']],list(range(40)))
        self.assertEqual(page['next_offset'],41)

    def test_metadata_does_not_consume_changes(self):
        def unavailable():
            raise AssertionError('Metadata must not render a change')
            yield
        for limit in (1,12,40):
            page=review_pages.pack(self.envelope(0,5),unavailable(),limit)
            self.assertEqual(page['changes'],[]);self.assertEqual(page['next_offset'],1)
        self.assertIsNone(review_pages.pack(self.envelope(0,0),unavailable(),40)['next_offset'])

    def test_byte_boundaries_preserve_order_and_multirecord_slots(self):
        groups=[[{'id':f'{i}-{j}','text':'quoted " \u2603 '*12} for j in range(1+i%3)] for i in range(23)]
        original=copy.deepcopy(groups)
        with patch.object(review_pages,'BUDGET',2400):
            seen,pages=self.collect(groups,40)
            self.assertEqual(seen,[row for group in groups for row in group])
            self.assertGreater(len(pages),1);self.assertLess(len(pages),len(groups))
            self.assertGreater(len(pages[0]['changes']),1)
            consumed=0
            for page in pages:
                # IDs independently reveal the slot boundaries; use count is not slot count.
                slots=list(dict.fromkeys(int(x['id'].split('-')[0]) for x in page['changes']))
                self.assertEqual(slots,list(range(consumed,consumed+len(slots))))
                consumed+=len(slots)
                self.assertEqual(page['next_offset'],consumed+1 if consumed<len(groups) else None)
        self.assertEqual(groups,original)

    def test_context_trimming_matches_single_slot_exactly(self):
        group=[{'kind':'rename_use','before':{'record':{'record_id':'r'},'before':'x'*5000,'after':'y'*5000}}]
        groups=[[{'id':'first'}],group,[{'id':'last'}]];original=copy.deepcopy(groups)
        with patch.object(review_pages,'BUDGET',1500):
            singles,_=self.collect(groups,1);batched,_=self.collect(groups,40)
        self.assertEqual(batched,singles)
        self.assertTrue(batched[1]['neighbors_omitted'])
        self.assertEqual(batched[1]['before']['record'],{'record_id':'r'})
        self.assertEqual(groups,original)

    def test_continuation_counts_slots_not_flattened_uses(self):
        groups=[[{'id':i} for i in (0,1)],[{'id':i} for i in (2,3,4)],[{'id':5}]]
        first=review_pages.pack(self.envelope(1,3),iter(groups),2)
        self.assertEqual([row['id'] for row in first['changes']],[0,1,2,3,4])
        self.assertEqual(first['next_offset'],3)
        last=review_pages.pack(self.envelope(3,3),iter(groups[2:]),2)
        self.assertEqual(last['changes'],[{'id':5}]);self.assertIsNone(last['next_offset'])

    def test_oversized_middle_slot_delivers_prefix_then_refuses_exact_slot(self):
        groups=[[{'id':'first'}],[{'id':'large','record':'x'*4000}],[{'id':'last'}]]
        with patch.object(review_pages,'BUDGET',1500):
            page=review_pages.pack(self.envelope(1,3),iter(groups),40)
            self.assertEqual(page['changes'],groups[0]);self.assertEqual(page['next_offset'],2)
            with self.assertRaisesRegex(ServiceError,'^RESPONSE_TOO_LARGE$') as caught:
                review_pages.pack(self.envelope(2,3),iter(groups[1:]),40)
            self.assertEqual(caught.exception.details['offset'],2)
            self.assertEqual(caught.exception.details['next_offset'],3)
            last=review_pages.pack(self.envelope(3,3),iter(groups[2:]),40)
            self.assertEqual(last['changes'],groups[2]);self.assertIsNone(last['next_offset'])

    def test_unrelated_failure_is_not_hidden_by_a_prefix(self):
        original=review_pages.fit
        def fail(page):
            if page['offset']==2:raise ServiceError('GENERATION_INPUT_CHANGED')
            return original(page)
        with patch.object(review_pages,'fit',side_effect=fail):
            with self.assertRaisesRegex(ServiceError,'^GENERATION_INPUT_CHANGED$'):
                review_pages.pack(self.envelope(1,2),iter([[{'id':1}],[{'id':2}]]),40)


class ReadinessTests(unittest.TestCase):
    def test_use_groups_obey_byte_limit_and_preserve_every_reference(self):
        refs=['r'+str(i) for i in range(30)];op={'declaration_id':'d','reference_ids':refs}
        model=SimpleNamespace()
        with patch.object(rename_service,'use_view',side_effect=lambda a,b,r,d:{'reference_id':r,'record':'quoted " \u2603 '*180}):
            pages=rename_service.use_pages(None,model,op,'base')
            self.assertEqual([r for page in pages for r in page],refs)
            self.assertTrue(all(len(page)<=8 for page in pages))
            self.assertGreater(len(pages),4)
            for page in pages:
                rows=[rename_service.use_view(None,model,r,'d') for r in page]
                self.assertLessEqual(review_pages.wire_size({'changes':rows}),review_pages.BUDGET-4096)
            with patch.object(rename_service,'use_view',side_effect=AssertionError('Unexpected recomputation')):
                self.assertEqual(rename_service.use_pages(None,model,op,'base'),pages)
        with patch.object(rename_service,'use_view',side_effect=lambda a,b,r,d:{'reference_id':r}):
            pages=rename_service.use_pages(None,SimpleNamespace(),op,'base')
            self.assertEqual([len(page) for page in pages],[8,8,8,6])

    def diagnostic(self,text,**kwargs):
        with tempfile.TemporaryDirectory() as temporary:
            log=Path(temporary)/'gate.log';log.write_text(text)
            model=SimpleNamespace(source=b'Cell .EQU 16\nLDA #Cell\nRTS\n',facts={})
            return gate_diagnostics.explanation(log,'/private/checkouts/project','projects/sample/asm/sample.asm',model,**kwargs)

    def test_failure_lines_survive_json_and_remove_host_paths_and_source(self):
        result=self.diagnostic('FAIL: /private/checkouts/project/projects/sample/docs/note.md: missing condition\nPORTS_MISSING\n'
            'ERROR: /secret/location.txt unavailable\nFAIL: projects/sample/asm/sample.asm:2: LDA #Cell\n'
            '{"summary":"No stale old-symbol references found","residue":[]}\n')
        self.assertEqual(result['failure_line_count_in_tail'],3)
        self.assertEqual(len(result['failure_lines']),3)
        self.assertIn('missing condition',result['failure_lines'][0])
        self.assertIn('projects/sample/docs/note.md',result['failure_lines'][0])
        self.assertEqual(result['report']['residue'],[])
        self.assertTrue(result['failure_context'])
        self.assertEqual(result['failure_context'][0],{'failure_index':0,'lines':['PORTS_MISSING'],'context_truncated':False})
        encoded=json.dumps(result)
        for private in ('/private/checkouts','/secret','LDA #Cell'):self.assertNotIn(private,encoded)
        self.assertIn('[source text omitted',encoded)

    def test_failure_context_lists_are_complete_or_flagged(self):
        for count in (5,120,121):
            with self.subTest(count=count):
                lines=['UnknownSymbol'+str(i) for i in range(count)]
                result=self.diagnostic('FAIL: docs reference unknown symbols:\n'+'\n'.join(lines)+
                    '\n{"summary":"No stale old-symbol references found","residue":[]}\n')
                self.assertEqual(len(result['failure_context']),1)
                context=result['failure_context'][0]
                self.assertEqual(context['lines'],lines[:120])
                self.assertEqual(context['context_truncated'],count>120)
                self.assertEqual(result['truncated'],count>120)
                self.assertFalse(result['failure_lines_truncated'])
                self.assertLessEqual(review_pages.wire_size(result),gate_diagnostics.MAX_OUTPUT)
        for stop in ('\n','  {"summary":"end"}\n','  [next check]\n','FAIL: another failure\n'):
            with self.subTest(stop=stop):
                result=self.diagnostic('FAIL: first\nOne\nTwo\nThree\nFour\nFive\n'+stop+'Not part of first\n')
                self.assertEqual(result['failure_context'][0]['lines'],['One','Two','Three','Four','Five'])
                self.assertFalse(result['failure_context'][0]['context_truncated'])
        result=self.diagnostic('FAIL: long item\n'+('x'*3000)+'\n{}\n')
        self.assertTrue(result['failure_context'][0]['context_truncated'])
        self.assertTrue(result['truncated'])

    def test_failure_context_budget_keeps_prefix_and_marks_every_drop(self):
        first=['EarlySymbol'+str(i) for i in range(5)]
        last=['LaterSymbol'+str(i)+' '+('quoted " \u2603 '*10) for i in range(20)]
        text='FAIL: first list\n'+'\n'.join(first)+'\nFAIL: second list\n'+'\n'.join(last)+'\n{}\n'
        full=self.diagnostic(text)
        self.assertEqual(full['failure_context'][1]['lines'],last)
        self.assertFalse(full['truncated'])
        result=self.diagnostic(text,max_output=2500)
        self.assertLessEqual(review_pages.wire_size(result),2500)
        self.assertEqual(result['failure_lines'],['FAIL: first list','FAIL: second list'])
        self.assertEqual(len(result['failure_context']),2)
        self.assertEqual(result['failure_context'][0]['lines'],first)
        self.assertFalse(result['failure_context'][0]['context_truncated'])
        context=result['failure_context'][1]
        self.assertGreater(len(context['lines']),0);self.assertLess(len(context['lines']),len(last))
        self.assertEqual(context['lines'],last[:len(context['lines'])])
        self.assertTrue(context['context_truncated']);self.assertTrue(result['truncated'])

    def test_empty_context_keeps_omission_flag_for_visible_failures(self):
        text=''.join('FAIL: list '+str(i)+'\nDetail'+str(i)+'\n' for i in range(30))+'{}\n'
        result=self.diagnostic(text,max_output=1800)
        self.assertLessEqual(review_pages.wire_size(result),1800)
        self.assertTrue(result['failure_lines']);self.assertTrue(result['failure_lines_truncated'])
        self.assertEqual([c['failure_index'] for c in result['failure_context']],list(range(len(result['failure_lines']))))
        for context in result['failure_context']:
            self.assertEqual(context['lines'],[]);self.assertTrue(context['context_truncated'])
        self.assertTrue(result['truncated'])

    def test_diagnostics_fit_wire_budget_with_failure_priority(self):
        text=''.join('FAIL: problem '+str(i)+' '+('"\u2603'*900)+'\n' for i in range(100))
        text+=json.dumps({'summary':'Summary that does not override failure','residue':[{'text':'x'*500}]*90})+'\n'
        result=self.diagnostic(text,max_output=3072)
        self.assertLessEqual(review_pages.wire_size(result),3072)
        self.assertTrue(result['truncated']);self.assertTrue(result['failure_lines_truncated'])
        self.assertTrue(result['failure_lines']);self.assertIn('FAIL:',result['failure_lines'][0])
        self.assertTrue(result['log_tail_truncated'])

    def test_residue_json_and_plain_text_still_available(self):
        residue={'summary':'Stale prose','residue':[{'symbol':'OldName','file':'projects/sample/docs/note.md','line':7,'text':'OldName'}]}
        result=self.diagnostic(json.dumps(residue)+'\n')
        self.assertEqual(result['report'],residue);self.assertEqual(result['failure_lines'],[])
        result=self.diagnostic('ordinary output\nFAIL: missing evidence\n')
        self.assertEqual(result['format'],'text');self.assertIn('ordinary output',result['lines'])
        self.assertEqual(result['failure_lines'],['FAIL: missing evidence'])


if __name__=='__main__':unittest.main()
