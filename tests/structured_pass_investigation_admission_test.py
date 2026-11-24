"""Prepared phase artifacts, coverage and reservations decide admission."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest

import structured_codex_client as client
import structured_pass_fixture as fixture
from structured_pass_inputs_test import setup_inputs
from structured_pass import corridor_capacity as capacity, corridor_inventory, editor_admission as editor
from structured_pass import investigation as inv, investigation_admission as admission
from structured_pass.investigation_workflow import Workflow, input_wire_bytes
from structured_pass.investigation_service import Session
from structured_pass import edit_contract

ROOT=Path(__file__).resolve().parents[1]


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


if __name__=='__main__':unittest.main()
