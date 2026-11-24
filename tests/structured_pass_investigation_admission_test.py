"""Prepared phase artifacts, coverage and reservations decide admission."""
import copy
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import structured_codex_client as client
import structured_pair_launcher as pair
import structured_pass_fixture as fixture
from structured_pass_inputs_test import setup_inputs
from structured_pass import corridor_capacity as capacity, corridor_inventory, editor_admission as editor
from structured_pass import investigation as inv, investigation_admission as admission
from structured_pass.investigation_workflow import Workflow, input_wire_bytes
from structured_pass.investigation_service import Session
from structured_pass import application, bridge, edit_contract, session_plan, subscription_client


class InvestigationAdmissionTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('Pinned assembler required')
        temporary=tempfile.TemporaryDirectory(dir=ROOT/'tmp');self.addCleanup(temporary.cleanup)
        self.root=Path(temporary.name).resolve()
        self.c=fixture.prepare(self.root/'fixture',declared_setup=lambda r,p:setup_inputs(r,p,False,True))
        self.g=self.c.editor.state['current'];model=self.c.editor.model(self.g)
        spec={'roots':[{'symbol':'Entry','through_return':'RTS'}],'vector':'Cell','ram_ranges':[[0,2047]],'analogues':[]}
        inventory=corridor_inventory.build(model,spec);catalog=inv.catalog(model,self.g,inventory)
        self.flow=Workflow.prepare(self.root/'flow',self.c,inventory,[{'id':'first','sets':list(catalog['sets'])}])
        outer=tempfile.TemporaryDirectory();self.addCleanup(outer.cleanup);outside=Path(outer.name).resolve()
        endpoint=outside/'endpoint';endpoint.mkdir()
        (endpoint/'investigation-profile.json').write_text(json.dumps({'workflow':str(self.flow.root),
            'entry_id':'first','plan_sha256':inv.sha(self.flow.root/'plan.json')}))
        prompt=outside/'prompt.md';prompt.write_text('Read and cite the frozen evidence.\n')
        binary=outside/'codex';binary.write_text('offline profile only\n')
        (outside/'codex-code-mode-host').write_text('offline profile only\n')
        self.profile=outside/'profile'
        self.config=client.prepare(self.profile,session=self.c.root,prompt=prompt,model='fixture',effort='high',
            client=binary,interpreter=__import__('sys').executable,service_root=ROOT,
            heavy_lock=outside/'lock',message='Investigate the first partition.',
            service_profile='investigation',bridge_root=endpoint,pair_root=outside/'pair')
        self.envelope=json.loads((ROOT/'tests/fixtures/codex_tool_declaration.json').read_bytes())
        self.captured=editor.artifacts(self.c,self.profile,self.envelope,'investigation')
        self.startup=['operation-reference','guidance-startup','reference','empty','receipt']
        self.session=Session(endpoint);actual=admission.measure(self.session,self.startup)
        self.baseline=copy.deepcopy(actual)
        phase=input_wire_bytes(edit_contract.investigation_reference(),'investigation-contract',self.g)+\
              input_wire_bytes(self.session.assignment(),'investigation-assignment',self.g)
        for job,size in [('checkpoint-output-cap',65536),('phase-contract-and-assignment',max(8192,phase))]:
            self.baseline.append({'job':job,'operation':'input','arguments':{},'wire_bytes':size,'reservation':True})
        self.pricing={'initial_tokens':12678,'overhead_bytes':36751,'overhead_request_bytes':1088}
        self.basis={'initial_tokens':7800,'framing_tokens':2000,'declaration_bytes':256}
        self.previous={k:self.captured[k] for k in ('instructions','message','native_declaration')}
        self.report=admission.bind(self.flow,self.profile,self.baseline,self.pricing,self.basis,self.previous,
                                   self.startup,self.envelope)
        self.path=self.root/'admission.json';self.save(self.report)

    def save(self,value):self.path.write_text(json.dumps(value))

    def test_real_native_workload_and_unchanged_live_start(self):
        before=(self.flow.root/'state.json').read_bytes()
        self.assertTrue(admission.verify(self.flow,self.profile,self.path)['price']['passed'])
        self.assertEqual((self.flow.root/'state.json').read_bytes(),before)
        self.assertEqual(json.loads(before),{'active':None,'sessions':{},'editing':False})
        self.assertEqual(self.report['caps']['checkpoint-output-cap'],65536)
        self.assertEqual(self.report['price']['lifecycle_tokens'],48000)
        self.assertEqual(self.report['price']['margin_tokens'],25840)

    def test_missing_coverage_changed_assignment_or_false_price_refuse(self):
        for fault in ('coverage','assignment','price','cap','prompt'):
            value=copy.deepcopy(self.report)
            if fault=='coverage':value['actual_calls']=[c for c in value['actual_calls'] if c['job']!='assigned-evidence']
            elif fault=='assignment':value['assignment']['reads']=[]
            elif fault=='price':value['price']['estimated_tokens']-=1
            elif fault=='cap':value['caps']['checkpoint-output-cap']-=1
            else:value['artifacts']['instructions']['sha256']='changed'
            self.save(value)
            with self.subTest(fault=fault),self.assertRaises(ValueError):
                admission.verify(self.flow,self.profile,self.path)

    def test_final_prompt_growth_can_refuse_without_borrowing_caps(self):
        changed={**self.previous,'message':editor.stamp(b'x'*400000)}
        result=admission.totals(self.baseline,self.report['actual_calls'],self.captured['budget'],self.pricing,
            changed,self.previous,self.basis,self.session.assignment(),self.g,65536)
        self.assertFalse(result['price']['passed'])
        self.assertEqual(result['caps'],self.report['caps'])

    def test_closed_pair_applies_after_checked_investigation(self):
        from structured_pass_pair_test import admitted_platform
        outside=self.profile.parent; pair_root=outside/'pair'
        lock=Path(os.environ['NESREV_HEAVY_RUN_LOCK'])
        # All profiles share the suite's held lock; no native client is started.
        config=json.loads((self.profile/'launch.json').read_bytes())
        config['heavy_lock']=str(lock)
        client.save(self.profile/'launch.json',config)
        self.report=admission.bind(self.flow,self.profile,self.baseline,self.pricing,
            self.basis,self.previous,self.startup,self.envelope)
        self.save(self.report)
        task=outside/'task.txt';task.write_text('Synthetic offline application check.\n')
        impl=outside/'editor'; rev=outside/'reviewer'
        client.prepare(impl,session=self.c.root,prompt=outside/'prompt.md',model='fixture',effort='high',
            client=outside/'codex',interpreter=sys.executable,service_root=ROOT,heavy_lock=lock,
            message=task.read_text(),auth_home=client.auth_home(self.profile,config),pair_root=pair_root)
        captured=editor.artifacts(self.c,impl,self.envelope,'corridor')
        previous={k:captured[k] for k in ('instructions','message','native_declaration')}
        calls=editor.measure(self.flow,self.startup)
        calls += [{'job':name,'operation':'input','arguments':{},'wire_bytes':size,'reservation':True}
                  for name,size in editor.CAPS.items()]
        baseline={'calls':calls,'charges':editor.CAPS,'pricing':self.pricing,
                  'price':capacity.price(calls,captured['budget'],**self.pricing)}
        report=editor.bind(self.flow,impl,baseline,self.basis,previous,self.startup,self.envelope)
        client.save(self.c.root/'editor-admission.json',report)
        prompts=outside/'prompts';prompts.mkdir()
        for role in ('implementer','reviewer'):
            (prompts/(role+'.md')).write_text('Synthetic offline application check.\n')
        binary=outside/'claude'
        binary.write_text('#!'+sys.executable+'\nimport sys\n'
            'assert sys.argv[1:] == ["--version"], "Native invocation is forbidden"\n'
            'print("offline-version-fixture")\n')
        binary.chmod(0o700)
        reviewer=subscription_client.prepare(rev,self.c.root,prompts,model='fixture',effort='high',
            client=binary,interpreter=sys.executable,heavy_lock=lock,task=task.read_text(),pair_root=pair_root)
        self.addCleanup(shutil.rmtree,Path(reviewer['roles']['reviewer']['workspace']).parent)
        target=self.root/'fixture/repo'
        fixture.git(target,'branch','-m','projects')
        with admitted_platform():
            pair.prepare(pair_root,self.c.root,impl,rev,task,application_repo=target,
                investigators=[{'entry_id':'first','profile':str(self.profile),'admission':str(self.path)}])
            proof=outside/'offline.json';client.save(proof,{'synthetic':True,'native_invocations':0})
            evidence={name:{'path':str(proof),'sha256':client.sha(proof)}
                      for name in ('access_preflight','transition_review')}
            pair.authorize(pair_root,owner_message='Test fixture only; no native invocation',
                deadline=time.time()+120,invocations=6,responses=5,turn_seconds=30,
                purpose='pilot_takeover',evidence=evidence,apply=True)

            self.flow.begin('first','offline-investigator',{})
            ids=sorted({r['record_id'] for r in self.flow.config['catalog']['evidence'].values()
                        if r['kind']=='record'})
            request={'operation':'navigate','arguments':{'generation':self.g,'view':'edit','record_id':ids}}
            page=self.c.dispatch(request['operation'],request['arguments'],'implementer')
            output=io.StringIO()
            bridge.emit(None,1,{'result':{'content':[{'type':'text','text':json.dumps(page)}]}},output,'navigate')
            result=json.loads(output.getvalue())['result']
            self.flow.delivered('first',request,result)
            audit={'session_id':'offline-investigator','last_compaction':-1,'calls':[
                {'call_id':'offline-1','position':1,'arguments':request,'output':result}]}
            self.flow.stage('first',{'claims':[{'id':'unknown','kind':'unknown','subject':'Synthetic corridor',
                'statement':'Semantic naming remains unproven by this scripted test.','confidence':'unknown',
                'citations':[],'searched_sets':[],'unknowns':'Independent evidence required.','contrary':[]}],
                'decisions':[]})
            self.assertEqual(self.flow.finalize('first',audit)['completion'],'complete')
            self.flow.admit_editor({'first':audit})
            preview=self.c.dispatch('preview',{'generation':self.g,
                'operations':fixture.rename_ops(self.c,self.g)},'implementer')
            cid=self.c.dispatch('confirm',{'generation':self.g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
            self.assertEqual(self.c.dispatch('validate',{'cid':cid},'implementer')['status'],'validated')
            self.c.dispatch('publish',{'cid':cid},'implementer')
            ticket=self.c.status('reviewer')['ticket']
            self.c.dispatch('approve',{'ticket':ticket,
                'report':'Verdict: APPROVED\n\nSynthetic lifecycle only.\n\n## Learning Candidates\n\n_None._\n'},'reviewer')
            self.c.dispatch('closeout',{},'implementer')
            state=pair.read(pair_root/'state.json');state['stop']='closed';pair.save(pair_root/'state.json',state)

            # An incorrect plan must fail before application or a child starts.
            launch=pair_root/'launch.json';original=launch.read_bytes();changed=json.loads(original)
            changed['session_plan']['editing_roles']=[];pair.save(launch,changed)
            with patch.object(pair,'supervise',side_effect=AssertionError('Application started')):
                with self.assertRaisesRegex(ValueError,'^INVESTIGATION_PLAN_INVALID$'):
                    pair.apply_closed(pair_root)
            launch.write_bytes(original)
            before=fixture.git(target,'rev-parse','HEAD');expected=application.apply(self.c.root,target,commit=False)
            verify=session_plan.verify
            # Inherit the suite's existing heavy lock; retain real supervision
            # and the real application subprocess and its internal gate lock.
            with patch.object(pair,'heavy_argv',side_effect=lambda root,config,command:command),\
                    patch.object(session_plan,'verify',wraps=verify) as checked:
                applied=pair.apply_closed(pair_root)
            checked.assert_called_once()
            self.assertEqual(applied['status'],'committed')
            self.assertEqual(applied['head'],before)
            self.assertEqual(applied['paths'],expected['paths'])
            for path,digest in expected['paths'].items():
                self.assertEqual(client.sha(target/path) if (target/path).exists() else None,digest)
            self.assertEqual(fixture.git(target,'rev-parse','HEAD'),applied['commit'])
            self.assertEqual(pair.read(pair_root/'state.json')['application'],applied)
            processes=list((pair_root/'application').glob('*/process.json'))
            self.assertEqual(len(processes),1)
            self.assertEqual(pair.read(processes[0])['exit_code'],0)
            self.assertTrue(pair.read(processes[0])['processes_reconciled'])
            self.assertEqual(pair.read(impl/'state.json')['runs'],[])
            self.assertEqual(pair.read(rev/'budget.json')['runs'],[])


if __name__=='__main__':unittest.main()
