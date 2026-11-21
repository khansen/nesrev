"""Reading views preserve source and access evidence without edit-record overhead."""
import io
import json
from unittest.mock import patch
import unittest
import structured_pass_navigation_test as nav_fixture
from structured_pass.corridor_capacity import expand
from structured_pass import bridge,edit_contract,navigation,ram_evidence,evidence_views

class ReadingTests(unittest.TestCase):
    setUp=nav_fixture.NavigationSpanTests.setUp
    read=nav_fixture.NavigationSpanTests.read

    def test_source_spans_and_overlapping_owner_batches_are_exact(self):
        m=self.c.editor.model(self.g); nav=navigation.Navigation(m)
        expected=nav.selection(m.declarations['L9000'],'segment')
        for role in ('implementer','reviewer'):
            for args in ({'symbol':'L9000','span':'segment'},
                         {'record_id':[m.ids[m.declarations['L9000']],m.ids[m.declarations['L9001']]]}):
                rows=[];comments=[];offset=0
                while offset is not None:
                    error,page=self.read(role,view='source',limit=3,offset=offset,**args)
                    self.assertFalse(error,page);self.assertEqual(page['generation'],self.g)
                    rows+=expand(page);comments+=page['comments'];offset=page['next_offset']
                nodes=expected if 'symbol' in args else expected[:8]
                self.assertEqual([r['record_id'] for r in rows],[m.ids[n] for n in nodes])
                self.assertEqual([r['text'] for r in rows],[m.source[slice(*m.ranges[n])].decode() for n in nodes])
                self.assertEqual([r['address'] for r in rows],[m.locations[n]['cpu_address'] for n in nodes])
                self.assertEqual([c['text'] for c in comments],['; Synthetic gap comment.']*(len(nodes)//4))
                self.assertTrue(all(set(r)=={'record_id','address','label','text'} for r in rows))
        overlapping=[m.ids[expected[0]],m.ids[expected[1]]]
        error,page=self.read(view='source',record_id=overlapping,limit=40)
        self.assertFalse(error,page);self.assertEqual(len(page['records']),4)
        self.assertEqual(len(page['comments']),1)

    def test_source_size_and_bad_selections_refuse_without_truncation(self):
        m=self.c.editor.model(self.g)
        for args in ({'symbol':'L9000','limit':129},{'record_id':[]},{'record_id':['unknown']},
                     {'record_id':[m.ids[m.declarations['L9000']]],'span':'segment'},
                     {'symbol':'L9000','generation':'G-unknown'}):
            self.assertTrue(self.read(view='source',**args)[0])
        n=m.declarations['L9000']
        with patch('structured_pass.rename_service.comments',return_value=[
                {'line':m.facts[n]['span'][0],'text':'x'*30000}]):
            error,page=self.read(view='source',symbol='L9000')
            self.assertTrue(error);self.assertEqual(page['error'],'RESPONSE_TOO_LARGE')

    def test_set_ram_delivery_for_each_role(self):
        for role in ('implementer','reviewer'):
            args={'generation':self.g,'view':'ram_set','address':[0,1],'limit':128}
            output=io.StringIO()
            request={'id':1,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':'evidence','arguments':args}}}
            bridge.mcp(self.c.root,role,'corridor',io.StringIO(json.dumps(request)+'\n'),output)
            result=json.loads(output.getvalue())['result'];self.assertFalse(result.get('isError'),result)
            page=json.loads(result['content'][0]['text'])
            self.assertEqual(page['generation'],self.g);self.assertEqual(page['selection'],[0,1])

    def test_reference_explains_reading_and_editing_to_every_profile(self):
        ref=edit_contract.reference()
        for profile in ('implementer','reviewer','retained-reviewer'):
            self.assertIn('source',ref['arguments'][profile]['navigate']['values']['view']['enum'])
            self.assertIn('ram_set',ref['arguments'][profile]['evidence']['values']['view']['enum'])
        self.assertIn('preimages',ref['view_arguments']['navigate']['source']['coverage'])
        self.assertIn('requested_address',ref['view_arguments']['ram_set']['decode'])

if __name__=='__main__':unittest.main()
