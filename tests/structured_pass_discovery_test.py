"""Argument discoverability, retained reference bytes and actionable refusals."""
import copy
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import (bridge, declared_inputs, edit_contract, error_policy, guidance,
    operation_contract as contract, service, source_edits, navigation, evidence_views)
from structured_pass import launcher, retained_service, current_project, publication
import structured_pass_inputs_test as input_tests


class DiscoveryTests(unittest.TestCase):
    def assert_complete(self,reference):
        for profile,role,mode in (('implementer','implementer','corridor'),
                ('reviewer','reviewer','corridor'),('retained-reviewer','reviewer','retained')):
            self.assertEqual(set(reference['arguments'][profile]),set(contract.offered(role,mode)))
            for operation,spec in reference['arguments'][profile].items():
                for key in spec['required']:
                    self.assertTrue(key in spec.get('sources',{}) or key in spec.get('values',{}),
                                    (profile,operation,key))
                    if key in spec.get('values',{}):
                        self.assertTrue(set(spec['values'][key]) & {'authored','enum','source','type'})
            tool=bridge.tool_listing(role,mode)['tools'][0]
            self.assertIn(edit_contract.INPUT_ID,tool['inputSchema']['properties']['arguments']['description'])
            self.assertLessEqual(len(tool['description']),4096)
            self.assertLessEqual(len(tool['inputSchema']['properties']['arguments']['description']),4096)
        kinds=set()
        for owner in edit_contract.owners():
            kinds.update(owner.KINDS if hasattr(owner,'KINDS') else ('rename','comment_replace','ledger_append'))
        self.assertEqual(set(reference['operations']),kinds)
        types=reference['types']
        for kind,spec in reference['operations'].items():
            fields=types[spec['fields']]
            required=spec['required']+spec['optional']
            required += [key for condition in spec.get('when',[]) for key in condition.get('required',[])]
            for key in set(required)-{'kind'}:
                self.assertIn(key,fields,(kind,key))
                self.assertTrue(set(fields[key]) & {'authored','enum','source','type'},(kind,key))
        for name,spec in types.items():
            variants=spec.get('one_of',list(spec.get('variants',{}).values()))
            if 'required' in spec:variants=[spec]
            for shape in variants:
                fields=spec['fields'] if name.startswith('search_') and 'fields' in spec else spec
                for key in shape['required']+shape['optional']:
                    self.assertTrue(key in fields or 'values' in spec,(name,key))
                    if key in fields:
                        value=fields[key]
                        self.assertIsInstance(value,dict,(name,key))
                        self.assertTrue(set(value) & {'authored','source','enum','enum_items','type','unary'},(name,key))

    def test_complete_reference_and_missing_entry_controls(self):
        full=edit_contract.reference(['docs/allowed.md']);self.assert_complete(full)
        for profile in full['arguments']:
            bad=copy.deepcopy(full)
            bad['arguments'][profile]['document']['values'].pop('path')
            with self.assertRaises(AssertionError):self.assert_complete(bad)
        bad=copy.deepcopy(full);bad['operations'].pop('declare')
        with self.assertRaises(AssertionError):self.assert_complete(bad)
        for name,key in (('source_edit_fields','expression'),('source_boundary','operand_id'),
                         ('search_query','kind'),('warning_entry','rationale')):
            bad=copy.deepcopy(full)
            fields=bad['types'][name].get('fields',bad['types'][name]);fields.pop(key)
            with self.assertRaises(AssertionError):self.assert_complete(bad)

    def test_owner_shape_change_changes_reference_and_real_shape_check(self):
        op={'kind':'declare','reason':'Describe constant','anchor_id':'n1','preimage':'0'*64,
            'name':'Count','declaration_kind':'equ','expression':{'integer':3}}
        source_edits.shape(op)
        frozen=edit_contract.reference()['operations']['declare']
        changed=copy.deepcopy(source_edits.OPERATION_SCHEMAS['declare'])
        changed['required'].append('new_required_field')
        with patch.dict(source_edits.OPERATION_SCHEMAS,declare=changed):
            with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_SCHEMA'):source_edits.shape(op)
            self.assertNotEqual(frozen,edit_contract.reference()['operations']['declare'])
        label={**op,'declaration_kind':'label'}
        with self.assertRaisesRegex(ValueError,'SOURCE_EDIT_SCHEMA'):source_edits.shape(label)
        label.pop('expression');source_edits.shape(label)

    def test_error_classes_cover_public_codes_and_unknown_fails_closed(self):
        groups=(error_policy.CORRECTABLE,error_policy.TRANSIENT,error_policy.TERMINAL)
        self.assertEqual(sum(map(len,groups)),len(set.union(*(set(g) for g in groups))))
        self.assertEqual(set.union(*(set(g) for g in groups)),
                         service.PUBLIC_ERROR_CODES|{'INVALID_PAGINATION','UNKNOWN_CONSTANT'})
        self.assertEqual(error_policy.classify('NEW_UNCLASSIFIED_FAILURE'),'terminal')
        for code in ('STALE_GENERATION','PREIMAGE_MISMATCH','SOURCE_EDIT_PREIMAGE',
                     'UNKNOWN_OPERATION','OVERLAPPING_EDITS','CORRIDOR_NOT_STARTED'):
            self.assertEqual(error_policy.classify(code),'correctable',code)
        for code in ('FORBIDDEN_PATH','CAPTURE_CHANGED','INTERNAL_SERVICE_ERROR','RESPONSE_TOO_LARGE'):
            self.assertEqual(error_policy.classify(code),'terminal',code)
        with patch.object(service,'PUBLIC_ERROR_CODES',service.PUBLIC_ERROR_CODES|{'NEW_PUBLIC_CODE'}):
            with self.assertRaises(AssertionError):
                self.assertEqual(set.union(*(set(g) for g in groups)),
                                 service.PUBLIC_ERROR_CODES|{'INVALID_PAGINATION','UNKNOWN_CONSTANT'})

    def test_bridge_correction_transient_and_terminal(self):
        from structured_pass.launcher import Corridor
        instance=type('Fixture',(),{'error_context':lambda self,cid:{'generation':'G-test'}})()
        def dispatch(operation,args,role):
            if operation=='validate':
                contract.check(args,contract.BASE['validate'])
                return {'candidate':args['cid'],'validated':True}
            raise ValueError(operation)
        instance.dispatch=dispatch
        cases=[('validate',{'candidate':'private-value'}),('validate',{'cid':'C1'}),
               ('REVIEW_STATE_BUSY',{}),('CAPTURE_CHANGED',{})]
        lines=''.join(json.dumps({'id':i,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':op,'arguments':args}}})+'\n' for i,(op,args) in enumerate(cases))
        out=io.StringIO()
        with patch('structured_pass.launcher.Corridor',return_value=instance):
            bridge.mcp('unused','implementer',input_stream=io.StringIO(lines),output_stream=out)
        rows=[json.loads(json.loads(line)['result']['content'][0]['text']) for line in out.getvalue().splitlines()]
        self.assertEqual(rows[0]['error_class'],'correctable')
        self.assertEqual(rows[0]['details']['missing'],['cid'])
        self.assertNotIn('private-value',out.getvalue())
        self.assertEqual(rows[1],{'candidate':'C1','validated':True})
        self.assertEqual(rows[2]['error_class'],'transient');self.assertTrue(rows[2]['retryable'])
        self.assertEqual(rows[3]['error_class'],'terminal');self.assertFalse(rows[3]['retryable'])

    def test_value_diagnostics_use_dispatch_enums(self):
        with self.assertRaises(contract.RequestError) as caught:guidance.read(None,'index')
        self.assertEqual(caught.exception.details,{'field':'name','accepted_values':list(guidance.NAMES)})
        nav=navigation.Navigation.__new__(navigation.Navigation)
        with self.assertRaises(contract.RequestError) as caught:nav.query('invalid')
        self.assertEqual(caught.exception.details['accepted_values'],list(navigation.VIEWS))
        with self.assertRaises(contract.RequestError) as caught:evidence_views.decode(None,'n1','invalid')
        self.assertEqual(caught.exception.details['accepted_values'],list(evidence_views.DECODERS))
        full=edit_contract.reference()
        for code in ('SOURCE_EDIT_SCHEMA','ARTIFACT_EDIT_SCHEMA','DOCUMENT_SCHEMA','MIXED_DOCUMENT_SCHEMA','SEARCH_SCHEMA'):
            for path in error_policy.diagnostics(code,'preview','implementer','corridor')['contract_sources']:
                self.assertIn(path.split('.types.')[1],full['types'])

    def test_repeated_correctable_refusals_are_friction_without_payloads(self):
        first={'operation':'preview','arguments':{'private':'do not retain'},
               'result':{'error':'PREIMAGE_MISMATCH','error_class':'correctable'}}
        rows=[first,copy.deepcopy(first),{**first,'arguments':{'private':'different'}},
              {**first,'result':{'error':'CAPTURE_CHANGED','error_class':'terminal'}},
              {**first,'result':{'error':'REVIEW_STATE_BUSY','error_class':'transient'}}]
        report=error_policy.repeated_refusals(rows)
        self.assertEqual(len(report),1);self.assertEqual(report[0]['count'],2)
        self.assertNotIn('do not retain',json.dumps(report));self.assertNotIn('private',json.dumps(report))

    def test_stale_generation_and_preimage_corrections_through_lifecycle(self):
        from structured_pass_fixture import prepare, rename_ops, closeout_ops
        def call(c,operation,args):
            stream=io.StringIO(json.dumps({'id':1,'method':'tools/call','params':{'name':'operation',
                'arguments':{'operation':operation,'arguments':args}}})+'\n')
            out=io.StringIO();bridge.mcp(c.root,'implementer',input_stream=stream,output_stream=out)
            return json.loads(json.loads(out.getvalue())['result']['content'][0]['text'])
        (ROOT/'tmp').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=ROOT/'tmp') as directory:
            c=launcher.Corridor(prepare(Path(directory)).root)
            initial=call(c,'status',{})['generation'];ops=rename_ops(c,initial)
            invalid=copy.deepcopy(ops);invalid[0]['preimage']='0'*64
            state=c.editor.state_path.read_bytes()
            refusal=call(c,'preview',{'generation':initial,'operations':invalid})
            self.assertEqual(refusal['error'],'PREIMAGE_MISMATCH')
            self.assertEqual(refusal['error_class'],'correctable')
            self.assertEqual(c.editor.state_path.read_bytes(),state)
            preview=call(c,'preview',{'generation':initial,'operations':ops})
            cid=call(c,'confirm',{'generation':initial,'preview_digest':preview['preview_digest']})['candidate']
            self.assertEqual(call(c,'validate',{'cid':cid})['status'],'validated')
            call(c,'publish',{'cid':cid})
            current=call(c,'status',{})['generation'];self.assertNotEqual(initial,current)
            c=launcher.Corridor(c.root);ops=closeout_ops(c,current,notes='Rework from current facts.')
            state=c.editor.state_path.read_bytes()
            refusal=call(c,'preview',{'generation':initial,'operations':ops})
            self.assertEqual(refusal['error'],'STALE_GENERATION')
            self.assertEqual(refusal['error_class'],'correctable')
            self.assertEqual(c.editor.state_path.read_bytes(),state)
            corrected=call(c,'preview',{'generation':refusal['generation'],'operations':ops})
            self.assertIn('preview_digest',corrected)
            refusal=call(c,'guidance',{'name':'index'})
            self.assertEqual(refusal['error_class'],'correctable')
            self.assertEqual(refusal['details']['field'],'operation')
            self.assertNotIn('guidance',refusal['details']['accepted_values'])

    def test_corridor_guidance_withdrawn_retained_guidance_discoverable(self):
        for role in ('implementer','reviewer'):
            self.assertNotIn('guidance',contract.offered(role))
            self.assertNotIn('guidance',contract.corridor())
        self.assertEqual(contract.complete_entry('guidance','reviewer','retained')['values']['name']['enum'],list(guidance.NAMES))


    def test_review_sources_cover_each_adjacent_published_change(self):
        from structured_pass_fixture import prepare, rename_ops, closeout_ops
        from structured_pass.launcher import Corridor
        from structured_pass import structured_handoff
        (ROOT/'tmp').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=ROOT/'tmp') as directory:
            c=prepare(Path(directory))
            for index in range(2):
                g=c.editor.state['current']
                ops=rename_ops(c,g) if index==0 else closeout_ops(c,g,notes='Reworked notes.')
                preview=c.dispatch('preview',{'generation':g,'operations':ops},'implementer')
                cid=c.dispatch('confirm',{'generation':g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
                c.dispatch('validate',{'cid':cid},'implementer');c.dispatch('publish',{'cid':cid},'implementer')
            status=c.dispatch('status',{},'reviewer')
            edges=status['handoff']['coverage']['required_edges'];self.assertEqual(len(edges),2)
            listing=bridge.tool_listing('reviewer')['tools'][0]
            entry=json.loads(listing['inputSchema']['properties']['arguments']['description'].split(contract.DESCRIPTION_MARKER)[1])['review']
            def arguments(edge):
                result={}
                for key,paths in entry['sources'].items():
                    path=paths[0]
                    if '.required_edges[].' in path:result[key]=edge[int(path.rsplit('.',1)[1])]
                    else:
                        value={'status':status}
                        for field in path.split('.'):value=value[field]
                        result[key]=value
                return result
            for edge in edges:
                args=arguments(edge)
                self.assertEqual((args['base_generation'],args['generation']),tuple(edge))
                c.dispatch('review',{**args,'limit':40},'reviewer')
            with patch.dict(entry['sources'],base_generation=['status.handoff.coverage.pass_base']):
                with self.assertRaisesRegex(ValueError,'MIXED_GENERATION_COMPARISON'):
                    c.dispatch('review',arguments(edges[-1]),'reviewer')


class ReferenceInputTests(unittest.TestCase):
    setUp=input_tests.AdmissionTests.setUp
    admit=input_tests.AdmissionTests.admit

    def test_generated_reference_catalog_pages_and_restoration(self):
        capture=self.admit()
        row=next(r for r in declared_inputs.catalog_page(capture,'G-test',limit=40)['records'] if r['id']==edit_contract.INPUT_ID)
        self.assertEqual(row['kind'],'operation_reference')
        expected=(capture/('input-'+edit_contract.INPUT_ID+'.bin')).read_bytes().decode()
        self.assertLessEqual(len(expected.encode()),declared_inputs.TEXT_LIMIT)
        restored=self.root/'restored';shutil.copytree(capture,restored)
        shutil.rmtree(capture)
        offset=0;chunks=[]
        while offset is not None:
            page=declared_inputs.read(restored,'G-test',edit_contract.INPUT_ID,offset)
            chunks.append(page['text']);offset=page['next_offset']
        self.assertEqual(''.join(chunks),expected)
        self.assertEqual(set(json.loads(expected)['operations']),set(edit_contract.reference()['operations']))
        blob=restored/('input-'+edit_contract.INPUT_ID+'.bin');blob.write_bytes(blob.read_bytes()+b' ')
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):
            declared_inputs.read(restored,'G-test',edit_contract.INPUT_ID)


if __name__=='__main__':unittest.main()
