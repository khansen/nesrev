"""Whole-workload coverage must fail when a cheap subset replaces it."""
import copy
import unittest
import structured_pass_evidence_test as fixture
from structured_pass import corridor_inventory as inventory, corridor_capacity as capacity

class InventoryTests(unittest.TestCase):
    setUp=fixture.EvidenceTests.setUp

    def test_all_ram_operands_pointer_bytes_helpers_and_owners_are_derived(self):
        spec={'roots':[{'symbol':'Entry','through_return':'RTS'}],
              'vector':'Pointers','ram_ranges':[[0,2047]],'analogues':[]}
        actual=inventory.build(self.model,spec)
        self.assertEqual(actual['ram_addresses'],[0,63,64,254,255])
        self.assertEqual([h['choice']['symbol'] for h in actual['helpers']],['Called'])
        # This synthetic root jumps beyond its first return. Pricing cannot
        # certify the lexical selection as closed merely because it is small.
        self.assertTrue(actual['open_root_transfers'])
        owner_ids={r['owner_id'] for r in actual['access_owner_blocks']}
        self.assertIn(self.model.ids[self.model.declarations['Entry']],owner_ids)
        for field in ('ram_addresses','helpers','access_owner_blocks'):
            changed=copy.deepcopy(actual);changed[field].pop()
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'CAPTURE_CHANGED'):
                inventory.verify(self.model,changed)
        self.assertEqual(inventory.verify(self.model,actual),actual)
        jobs=capacity.plan(actual)
        selected=next(j for j in jobs if j['name']=='ram-set')
        self.assertEqual(selected['arguments']['address'],actual['ram_addresses'])
        self.assertEqual(len([j for j in capacity.plan(actual,True) if j['name'].startswith('ram-')]),5)

    def test_generation_missing_pages_or_missing_job_fail_coverage(self):
        spec={'roots':[{'symbol':'Called','through_return':'RTS'}],
              'vector':'Called','ram_ranges':[[0,2047]],'analogues':[]}
        actual=inventory.build(self.model,spec);calls=[{'job':'startup-status','operation':'status',
            'arguments':{},'wire_bytes':100,'result':{'generation':'G-test','next_offset':None,
            'volume':{'response_bytes':100},'records':[]}}]
        for job in capacity.plan(actual):
            args={'generation':'G-test',**job['arguments'],'offset':0}
            page={'generation':'G-test','next_offset':None,
                  'records':[{'record_id':r} for r in job['records']],
                  'volume':{'response_bytes':100}}
            calls.append({'job':job['name'],'operation':job['operation'],
                          'arguments':args,'wire_bytes':100,'result':page})
        capacity.verify_coverage(actual,calls,False,[])
        for kind in ('generation','missing-record','missing-job'):
            changed=copy.deepcopy(calls)
            if kind=='generation':changed[-1]['result']['generation']='G-other'
            if kind=='missing-record':changed[-1]['result']['records'].pop()
            if kind=='missing-job':changed.pop()
            with self.subTest(kind=kind),self.assertRaisesRegex(ValueError,'EVIDENCE_UNAVAILABLE'):
                capacity.verify_coverage(actual,changed,False,[])

class CapacityTests(unittest.TestCase):
    def test_all_charges_and_reserves_are_required(self):
        budget={'window_tokens':258400,'startup_tokens':78000,'lifecycle_tokens':48000,
                'margin_tokens':25840,'bytes_per_1000_tokens':2580}
        args={'initial_tokens':78000,'overhead_bytes':36751,'overhead_request_bytes':1500}
        def call(size):return {'job':'root-0','operation':'navigate','arguments':{},'wire_bytes':size}
        fits=capacity.price([call(100000)],budget,**args)
        self.assertTrue(fits['passed']);self.assertEqual(fits['required_bytes'],161327)
        self.assertEqual(fits['lifecycle_tokens'],48000)
        self.assertFalse(capacity.price([call(250000)],budget,**args)['passed'])
        for changed in ({**budget,'margin_tokens':1},{**budget,'lifecycle_tokens':47999}):
            with self.assertRaises(ValueError):capacity.price([],changed,**args)
        with self.assertRaises(ValueError):capacity.price([],budget,**{**args,'overhead_bytes':0})


class ReportBindingTests(unittest.TestCase):
    setUp=fixture.EvidenceTests.setUp

    def test_task_generation_inventory_and_capacity_are_bound(self):
        from types import SimpleNamespace
        from structured_pass import startup_inputs
        from unittest.mock import patch
        spec={'roots':[{'symbol':'Called','through_return':'RTS'}],
              'vector':'Called','ram_ranges':[[0,2047]],'analogues':[]}
        inv=inventory.build(self.model,spec)
        budget=startup_inputs.allowance({'window_tokens':258400,'startup_tokens':78000,
            'lifecycle_tokens':48000,'margin_tokens':25840,'bytes_per_1000_tokens':2580})
        ids=['operation-reference','guidance-startup']
        jobs=[{'name':'startup-'+i,'operation':'input','arguments':{'input_id':i,'limit':8192}} for i in ids]+capacity.plan(inv)
        calls=[{'job':'startup-status','operation':'status','arguments':{},'wire_bytes':100,
            'result':{'generation':'G-test','next_offset':None,'volume':{'response_bytes':100}}}]
        for job in jobs:
            calls.append({'job':job['name'],'operation':job['operation'],
                'arguments':{'generation':'G-test','offset':0,**job['arguments']},'wire_bytes':100,
                'result':{'generation':'G-test','next_offset':None,'volume':{'response_bytes':100},
                          'records':[{'record_id':r} for r in job.get('records',[])]}})
        selection={'corridor':spec,'budget':budget,'startup_ids':ids,
            'pricing':{'initial_tokens':11000,'overhead_bytes':36751,'overhead_request_bytes':1088}}
        controller=SimpleNamespace(root=self.root,editor=SimpleNamespace(
            state={'pass_start_generation':'G-test'},model=lambda g:self.model))
        report={'schema':'corridor-capacity-v1','session':str(self.root.resolve()),'generation':'G-test',
            'legacy':False,'selection':selection,'inventory':inv,'calls':calls,
            'price':capacity.price(calls,budget,**selection['pricing']),
            'code':capacity.code_pins(),'passed':True}
        catalog={'items':[{'id':i,'kind':'guidance' if i=='guidance-startup' else 'operation_reference'} for i in ids]}
        with patch('structured_pass.declared_inputs.load',return_value=catalog):
            task=capacity.prompt(report)
            capacity.verify_report(controller,report,task,budget)
            for field in ('task','generation','missing-startup','inventory','price','code'):
                changed=copy.deepcopy(report);message=task
                if field=='task':message='No inventory here.'
                if field=='generation':changed['generation']='G-other'
                if field=='missing-startup':
                    changed['selection']['startup_ids']=[]
                    changed['calls']=[c for c in changed['calls'] if c['job']=='startup-status' or not c['job'].startswith('startup-')]
                    changed['price']=capacity.price(changed['calls'],budget,**selection['pricing'])
                if field=='inventory':changed['inventory']['vector_records'].pop()
                if field=='price':changed['price']['allowance_bytes']+=1
                if field=='code':changed['code']={}
                with self.subTest(field=field),self.assertRaises(ValueError):
                    capacity.verify_report(controller,changed,message,budget)

if __name__=='__main__':unittest.main()
