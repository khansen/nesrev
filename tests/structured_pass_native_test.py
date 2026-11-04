#!/usr/bin/env python3
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass_fixture import prepare, SOURCE
from structured_pass_native_support import run_client


class Scenario:
    PROFILE='corridor'
    SOURCE=SOURCE

    def __init__(self,root,controller,role):
        self.HERE=root/role;self.HERE.mkdir();self.BASE=root/'repo'

    def start(self,role):return 7 if role=='implementer' else 3

    def step(self,index,role,result,fixture,base,published_candidate,call):
        if index==0:return call('status')
        generation=result(0)['generation']
        if role=='reviewer':
            if index==1:return call('navigate',generation=generation,view='uses',symbol='Capacity')
            return call('validate',cid='C1')
        if index==1:return call('inspect',generation=generation,symbol='Cell')
        if index==2:return call('documents',generation=generation)
        if index==3:
            d=result(1)['declaration']['record'];docs=result(2);ledger=result(1)['ledger']
            ops=[{'kind':'rename','declaration_id':d['record_id'],'old_name':'Cell','new_name':'Capacity','preimage':d['preimage_sha256']},
                 {'kind':'ledger_append','path':ledger['path'],'preimage':ledger['sha256'],
                  'rows':[{'old_name':'Cell','new_name':'Capacity','reason':'Synthetic client fixture','confidence':'high','pass_id':'1'}]},
                 {'kind':'scorecard_update','pass_id':'1','preimage':docs['scorecard']['preimage'],
                  'fields':{'focus':'Synthetic transport test','notes':'No quality claim.'}},
                 {'kind':'closeout','pass_id':'1','deferrals_preimage':docs['deferrals']['preimage'],'deferrals':[],'rework_items':0}]
            return call('preview',generation=generation,operations=ops)
        if index==4:return call('confirm',generation=generation,preview_digest=result(3)['preview_digest'])
        if index==5:return call('validate',cid=result(4)['candidate'])
        return call('publish',cid=result(4)['candidate'])

    def checks(self,role,result,base,published_candidate):
        if role=='implementer':return {'validated':result(5)['status']=='validated','published':result(6)['status']=='published'}
        return {'uses_visible':result(1)['total']==1,'mutation_denied':result(2).get('error')=='REVIEWER_MUTATION_DENIED'}


@unittest.skipUnless(os.environ.get('STRUCTURED_PASS_CLIENT') and os.environ.get('STRUCTURED_PASS_XASM'),
                     'Opt in with STRUCTURED_PASS_CLIENT and STRUCTURED_PASS_XASM; loopback only')
class NativeTests(unittest.TestCase):
    def test_fixed_role_tools_and_real_bridge(self):
        (ROOT/'tmp').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='native-test-',dir=ROOT/'tmp') as tmp:
            root=Path(tmp);controller=prepare(root);base=controller.editor.state['current']
            for role in ('implementer','reviewer'):
                result=run_client(controller.root,role,base,{},scenario=Scenario(root,controller,role))
                self.assertTrue(result['passed']);self.assertEqual(result['provider_requests'],0)


if __name__=='__main__':unittest.main()
