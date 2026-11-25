"""Paging recovery through the offered role routes, including their subviews."""
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
from structured_pass import bridge, declared_inputs, operation_contract as contract
from structured_pass import corridor_inventory, investigation as inv
from structured_pass.investigation_workflow import Workflow
from structured_pass.investigation_service import Session
from structured_pass_fixture import prepare, rename_ops, closeout_ops
from structured_pass.service import ServiceError
from structured_pass_inputs_test import setup_inputs


class PaginationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.environ.get('STRUCTURED_PASS_XASM'):
            raise unittest.SkipTest('Pinned assembler required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(dir=ROOT/'tmp')
        cls.addClassCleanup(temp.cleanup)
        cls.root = Path(temp.name)
        setup = lambda r, p: setup_inputs(r, p, False, True)
        cls.c = prepare(cls.root/'editing', declared_setup=setup)
        cls.base = cls.c.editor.state['current']
        preview = cls.c.dispatch('preview', {'generation':cls.base,
            'operations':rename_ops(cls.c, cls.base)}, 'implementer')
        cls.preview = preview['preview_digest']
        cls.cid = cls.c.dispatch('confirm', {'generation':cls.base,
            'preview_digest':cls.preview}, 'implementer')['candidate']
        cls.validation = cls.c.dispatch('validate', {'cid':cls.cid}, 'implementer')
        cls.c.dispatch('publish', {'cid':cls.cid}, 'implementer')
        cls.g = cls.c.editor.state['current']
        cls.ticket = cls.c.status('reviewer')['ticket']
        cls.c.dispatch('request-changes', {'ticket':cls.ticket,
            'report':'Verdict: CHANGES_REQUESTED\n\nSynthetic review.\n\n## Learning Candidates\n\n_None._\n'}, 'reviewer')
        pending = cls.c.dispatch('preview', {'generation':cls.g,
            'operations':closeout_ops(cls.c,cls.g,notes='Synthetic rework.')}, 'implementer')
        cls.preview = pending['preview_digest']
        cls.cid = cls.c.dispatch('confirm', {'generation':cls.g,
            'preview_digest':cls.preview}, 'implementer')['candidate']
        with patch.object(cls.c.editor, 'run_gates', side_effect=ServiceError(
                'SOURCE_EDIT_PREIMAGE', records=[{'field':'preimage','expected':'synthetic evidence'}])):
            cls.validation = cls.c.dispatch('validate', {'cid':cls.cid}, 'implementer')
        cls.preview = cls.c.dispatch('preview', {'generation':cls.g,
            'operations':closeout_ops(cls.c,cls.g,notes='Synthetic preview.')}, 'implementer')['preview_digest']
        cls.ic = prepare(cls.root/'investigating', declared_setup=setup)
        cls.ig = cls.ic.editor.state['current']
        model = cls.ic.editor.model(cls.ig)
        inventory = corridor_inventory.build(model, {'roots':[{'symbol':'Entry','through_return':'RTS'}],
            'vector':'Cell','ram_ranges':[[0,2047]],'analogues':[]})
        catalog = inv.catalog(model, cls.ig, inventory)
        cls.flow = Workflow.prepare(cls.root/'workflow', cls.ic, inventory,
            [{'id':'first','sets':list(catalog['sets'])}])
        endpoint = cls.root/'endpoint'; endpoint.mkdir()
        (endpoint/'investigation-profile.json').write_text(json.dumps({
            'workflow':str(cls.flow.root),'entry_id':'first','plan_sha256':inv.sha(cls.flow.root/'plan.json')}))
        cls.flow.begin('first', 'offline-paging-test', {})
        cls.session = Session(endpoint)
        cls.record_id = model.ids[model.declarations['Entry']]
        cls.audit_calls = []
        cls.call('investigator', 'navigate', {'generation':cls.ig,'view':'edit','symbol':'Entry'})

    @classmethod
    def call(cls, profile, operation, arguments):
        role = 'reviewer' if profile == 'reviewer' else 'implementer'
        mode = 'investigation' if profile == 'investigator' else 'corridor'
        instance = cls.session if mode == 'investigation' else cls.c
        target = 'structured_pass.investigation_service.Session' if mode == 'investigation' else 'structured_pass.launcher.Corridor'
        request = {'id':1,'method':'tools/call','params':{'name':'operation',
            'arguments':{'operation':operation,'arguments':arguments}}}
        output = io.StringIO()
        # Reuse the real initialized service; dispatch, transport and diagnostics
        # are unmodified. There are no client processes or model calls.
        with patch(target, return_value=instance):
            bridge.mcp(instance.root if mode == 'corridor' else cls.root/'endpoint', role, mode,
                input_stream=io.StringIO(json.dumps(request)+'\n'), output_stream=output)
        cls.last_response = json.loads(output.getvalue())['result']
        if mode == 'investigation':
            cls.audit_calls.append({'call_id':str(len(cls.audit_calls)), 'position':len(cls.audit_calls),
                'arguments':request['params']['arguments'], 'output':cls.last_response})
        return json.loads(cls.last_response['content'][0]['text'])

    def assert_refusal(self, result, field):
        self.assertEqual(result.get('error_class'), 'correctable', result)
        self.assertEqual(result['details']['field'], field)
        self.assertEqual(result['details']['expected']['type'], 'integer')
        self.assertIn('minimum', result['details']['expected'])
        self.assertNotIn('private-invalid-value', json.dumps(result))

    def test_input_bad_limit_is_correctable_for_every_role(self):
        for profile in ('investigator','editor','reviewer'):
            g = self.ig if profile == 'investigator' else self.g
            with self.subTest(profile=profile):
                result = self.call(profile, 'input', {'generation':g,
                    'input_id':'guidance-startup','limit':20000})
                self.assert_refusal(result, 'limit')
                self.assertEqual(result['details']['expected']['maximum'],8192)

    def cases(self, profile):
        g = self.ig if profile == 'investigator' else self.g
        name = 'Cell' if profile == 'investigator' else 'Capacity'
        cases = [
            ('inputs', {'generation':g}, 40),
            ('input', {'generation':g,'input_id':'operation-reference'},8192),
            ('input', {'generation':g,'input_id':'guidance-startup'},8192),
            ('query', {'generation':g,'symbol':name},64),
            ('q09', {'generation':g,'names':[name]},40),
            ('document', {'generation':g,'path':'projects/sample/docs/reverse_engineering/WORKING_NOTES.md'},80),
            ('search', {'generation':g,'query':{'kind':'catalogue'}},40),
        ]
        for view in ('symbols','comments','records','records_compact','edit','source','uses'):
            args = {'generation':g,'view':view}
            if view not in ('symbols','comments'): args['symbol']='Entry'
            cases.append(('navigate',args,128 if view=='source' else 40))
        for view in ('records','records_compact','source'):
            cases.append(('navigate',{'generation':g,'view':view,'symbol':'Entry','span':'segment'},
                128 if view=='source' else 40))
        for view in ('ram','ram_compact','ram_summary','ram_set'):
            cases.append(('evidence', {'generation':g,'view':view,'address':[7] if view=='ram_set' else 7},
                40 if view=='ram' else 128))
        shared = self.call(profile,'evidence',{'generation':g,'view':'ram_compact','address':7})
        cases.append(('evidence', {'generation':g,'view':'ram_shared','set_id':shared['shared']['set_id']},128))
        if profile == 'investigator':
            cases += [('input',{'generation':g,'input_id':name},8192)
                for name in ('investigation-assignment','investigation-contract')]
            cases.append(('citation',{'generation':g,'kind':'record','record_id':self.record_id},40))
        else:
            cases += [
                ('review', {'generation':self.ticket,'base_generation':self.c.status('reviewer')['handoff']['coverage']['required_edges'][0][0],
                    'ticket':self.ticket},40),
                ('review_report', {'sequence':1},1024),
                ('validation_evidence', {'cid':self.cid,'revision':self.validation['revision'],
                    'attempt':self.validation['attempt']},40),
            ]
            if profile == 'editor':
                cases.append(('preview_page',{'generation':self.g,'preview_digest':self.preview},40))
        return cases

    def test_all_offered_paging_routes_name_the_bad_field(self):
        for profile in ('investigator','editor','reviewer'):
            role = 'reviewer' if profile=='reviewer' else 'implementer'
            mode = 'investigation' if profile=='investigator' else 'corridor'
            cases = self.cases(profile)
            expected = {name for name in contract.offered(role,mode)
                if {'offset','limit'} & set(contract.entry(name,role,mode)['optional'])}
            self.assertEqual({name for name,_,_ in cases}, expected)
            for op,args,maximum in cases:
                args = {**args, 'limit':1}
                with self.subTest(profile=profile,operation=op,selector=args):
                    valid = self.call(profile,op,args)
                    self.assertNotIn('error_class',valid)
                    for field in ('offset','limit'):
                        if field not in contract.entry(op,role,mode)['optional']: continue
                        invalid = [None,True,1.5,'private-invalid-value',[],{},-1]
                        if field=='limit':invalid += [0,maximum+1]
                        else: invalid += [10**9]
                        for value in invalid:
                            with self.subTest(field=field,value=value):
                                self.assert_refusal(self.call(profile,op,{**args,field:value}),field)

    def test_input_default_matches_priced_page_and_integrity_stays_terminal(self):
        for profile in ('investigator','editor','reviewer'):
            g = self.ig if profile=='investigator' else self.g
            for key in ('operation-reference','guidance-startup'):
                args = {'generation':g,'input_id':key}
                self.assertEqual(self.call(profile,'input',args),self.call(profile,'input',{**args,'limit':8192}))
            missing = self.call(profile,'input',{'generation':g,'input_id':'not-declared'})
            self.assertEqual((missing['error'],missing['error_class']),('INPUT_UNKNOWN','correctable'))
        capture = self.c.editor.model(self.g).capture
        item = next(i for i in declared_inputs.load(capture)['items'] if i['id']=='guidance-startup')
        path = capture/item['file']; original=path.read_bytes()
        try:
            path.write_bytes(original+b'changed')
            result=self.call('editor','input',{'generation':self.g,'input_id':'guidance-startup'})
            self.assertEqual(result['error_class'],'terminal')
            self.assertIn(result['error'],('INPUT_CHANGED','CAPTURE_CHANGED'))
        finally:path.write_bytes(original)


    def test_workflow_input_subroutes_and_retained_reader(self):
        ids = sorted({r['record_id'] for r in self.flow.config['catalog']['evidence'].values()
                      if r['kind']=='record'})
        args = {'generation':self.ig,'view':'edit','record_id':ids,'limit':40}
        result = self.call('investigator','navigate',args)
        self.assertNotIn('error_class',result)
        self.assertIsNone(result['next_offset'])
        audit = {'session_id':'offline-paging-test','last_compaction':-1,'calls':self.audit_calls}
        self.flow.stage('first', {'claims':[{'id':'unknown','kind':'unknown','subject':'Synthetic corridor',
            'statement':'No semantic judgment in this fixture.','confidence':'unknown','citations':[],
            'searched_sets':[],'unknowns':'Independent review required.','contrary':[]}], 'decisions':[]})
        self.flow.finalize('first',audit)
        self.flow.admit_editor({'first':audit})
        with patch.object(type(self),'c',self.ic):
            for key in self.flow.editor_inputs():
                args = {'generation':self.ig,'input_id':key}
                maximum = 40 if key=='investigation-edit-targets' else 8192
                good = self.call('editor','input',args)
                self.assertNotIn('error_class',good)
                self.assertEqual(good,self.call('editor','input',{**args,'limit':maximum}))
                for field,value in (('offset',-1),('offset',10**9),('offset',True),
                                    ('limit',None),('limit',0),('limit',maximum+1)):
                    with self.subTest(input_id=key,field=field,value=value):
                        self.assert_refusal(self.call('editor','input',{**args,field:value}),field)
        from structured_pass.retained_service import RetainedReviewService
        restored=RetainedReviewService.from_publication(self.root/'retained',self.c.config['store'],self.ticket)
        with patch('structured_pass.launcher.Corridor',return_value=restored):
            for args in ({'generation':self.ticket,'input_id':'operation-reference'},
                         {'generation':self.ticket,'input_id':'operation-reference','limit':8192}):
                response=restored.dispatch('input',args,'reviewer')
                if 'limit' not in args:default=response
                else:self.assertEqual(default,response)
            with self.assertRaises(contract.RequestError) as caught:
                restored.dispatch('input',{**args,'limit':20000},'reviewer')
            self.assertEqual(caught.exception.details['field'],'limit')


if __name__ == '__main__': unittest.main()
