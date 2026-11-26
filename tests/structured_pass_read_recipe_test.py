"""A price cannot depend on an argument the client has to invent."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from structured_pass import read_recipe


class ReadRecipeTests(unittest.TestCase):
    def setUp(self):
        self.recipe={'reading_rule':read_recipe.READING_RULE,'reads':[
            {'operation':'navigate','arguments':{'view':'source','symbol':'Entry','span':'segment','limit':40},
             'record_count':45}]}
        def call(job,op,args,page):return {'job':job,'operation':op,'arguments':args,'result':page}
        self.calls=[call('startup-status','status',{}, {'generation':'G-test'}),
            call('startup-guide','input',{'generation':'G-test','input_id':'guide','offset':0,'limit':8192},
                 {'generation':'G-test','next_offset':None}),
            call('assigned-evidence','navigate',
                 {'generation':'G-test','view':'source','symbol':'Entry','span':'segment','limit':40,'offset':0},
                 {'generation':'G-test','records':[{}]*30,'next_offset':30}),
            call('assigned-evidence','navigate',
                 {'generation':'G-test','view':'source','symbol':'Entry','span':'segment','limit':15,'offset':30},
                 {'generation':'G-test','records':[{}]*15,'next_offset':45})]

    def test_defaults_literals_and_continuations_with_shortened_page(self):
        got=read_recipe.verify(self.calls,self.recipe,['guide'])
        self.assertEqual(got['arguments'][1]['limit'],'default')
        self.assertEqual(got['arguments'][2]['limit'],'recipe:literal')
        self.assertEqual(got['arguments'][3]['limit'],'recipe:final-page')
        self.assertEqual(got['arguments'][3]['offset'],'response:next_offset')

    def test_unbound_fields_and_missing_recipe_fail(self):
        for field,value in [('limit',128),('span','label'),('symbol','Other'),('generation','G-other'),('offset',1),('analogue_index',1)]:
            calls=copy.deepcopy(self.calls);calls[2]['arguments'][field]=value
            with self.subTest(field=field):
                result=read_recipe.check(calls,self.recipe,['guide'])
                self.assertFalse(result['passed']);self.assertIn(field,[e['field'] for e in result['errors']])
        self.assertFalse(read_recipe.check(self.calls,{},['guide'])['passed'])

    def test_old_assignment_missing_limit_is_not_a_source(self):
        old=copy.deepcopy(self.recipe);del old['reads'][0]['arguments']['limit']
        result=read_recipe.check(self.calls,old,['guide'])
        self.assertFalse(result['passed'])
        self.assertIn('limit',[e['field'] for e in result['errors']])
        # The route default is discovered from the actual implementation.
        self.assertEqual(read_recipe.defaults('navigate',{})['limit'],12)

    def test_future_other_query_or_omitted_offsets_do_not_count(self):
        for fault in ('future','different-query','omit','final-limit','truncate','before-status'):
            calls=copy.deepcopy(self.calls)
            if fault=='future':calls[2]['arguments']['offset']=30
            elif fault=='different-query':calls[3]['arguments']['symbol']='Other'
            elif fault=='omit':del calls[3]['arguments']['offset']
            elif fault=='final-limit':calls[3]['arguments']['limit']=40
            elif fault=='truncate':calls.pop()
            else:calls.pop(0)
            with self.subTest(fault=fault):self.assertFalse(read_recipe.check(calls,self.recipe,['guide'])['passed'])

    def test_startup_ids_must_be_in_delivered_index(self):
        self.assertFalse(read_recipe.check(self.calls,self.recipe,[])['passed'])
        calls=copy.deepcopy(self.calls);calls[1]['arguments']['limit']=4096
        self.assertFalse(read_recipe.check(calls,self.recipe,['guide'])['passed'])


if __name__=='__main__':unittest.main()
