"""Whole-workload coverage must fail when a cheap subset replaces it."""
import copy
import json
import math
from pathlib import Path
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
    def test_startup_rates_are_the_lowest_measured_pages(self):
        witness=json.loads((Path(__file__).parent/'fixtures/structured_startup_rates.json').read_text())
        minima={}
        totals={}
        for values in witness['pages']:
            row=dict(zip(witness['columns'],values))
            self.assertIn(row['run'],witness['sources'])
            self.assertLess(row['output_line'],row['before_token_line'])
            self.assertLess(row['before_token_line'],row['after_token_line'])
            growth=row['after_input_tokens']-row['before_input_tokens']
            self.assertGreater(growth,0)
            rate=row['wire_bytes']*1000//growth
            identity=row['input_id']
            minima[identity]=min(minima.get(identity,rate),rate)
            if row['run']=='r4' and identity!='comparison-document-0':
                totals[identity]=totals.get(identity,0)+growth
        self.assertEqual(sum(totals.values()),52349)
        self.assertEqual(sum(row[-1] for row in witness['pages']
                             if row[0]=='r4' and row[2]!='comparison-document-0'),213830)
        self.assertEqual(minima,{
            'operation-reference':3849,'guidance-0':3331,'guidance-1':2625,
            'guidance-2':3094,'guidance-3':3642,'guidance-startup':3097,
            'manual-text':3293,'faq-text':3718,'intake-receipt':3152,
            'reference-decision':2858,'comparison-document-0':3951})
        self.assertEqual(capacity.STARTUP_RATES,minima)

    def test_measured_startup_prices_include_increases_and_leave_other_rates_alone(self):
        budget={'window_tokens':258400,'startup_tokens':82000,'lifecycle_tokens':48000,
                'margin_tokens':25840,'bytes_per_1000_tokens':2580}
        def priced(identity,startup=True):
            call={'job':('startup-' if startup else 'evidence-')+identity,'operation':'input',
                  'arguments':{'input_id':identity},'wire_bytes':24576}
            request=len(json.dumps({k:call[k] for k in ('operation','arguments')}).encode())
            result=capacity.price([call],budget,initial_tokens=0,overhead_bytes=36751,
                                  overhead_request_bytes=1088)
            return result,request
        for identity,rate in [('operation-reference',3849),('guidance-startup',3097),
                ('manual-text',3293),('faq-text',3718),('intake-receipt',3152),
                ('reference-decision',2858),('guidance-unmeasured',3860),('unmeasured',2580)]:
            result,request=priced(identity)
            self.assertEqual(result['startup_tokens'],math.ceil(24576*1000/rate)+math.ceil(request*1000/2580))
            if identity in ('manual-text','faq-text','guidance-startup'):
                self.assertGreater(result['startup_tokens'],math.ceil(24576*1000/3860)+math.ceil(request*1000/2580))
        # A measured input name does not grant its rate to investigation reads.
        result,request=priced('operation-reference',startup=False)
        self.assertEqual(result['startup_tokens'],0)
        self.assertEqual(result['estimated_tokens'],48000+math.ceil((24576+request)*1000/2580)
                         +math.ceil((36751+1088+24576)*1000/2035))

    def test_format_rates_use_every_measured_page_and_keep_handoff_reservation(self):
        witness=json.loads((Path(__file__).parent/'fixtures/structured_format_rates.json').read_text())
        minima={}
        for row in witness['pages']:
            growth=row['following_input_tokens']-row['preceding_input_tokens']
            self.assertGreater(growth,0)
            rate=min(row['sealed_wire_bytes'],row['delivered_wire_bytes'])*1000//growth
            kind=row['encoding']
            minima[kind]=min(minima.get(kind,rate),rate)
        self.assertEqual({k:minima[k] for k in capacity.FORMAT_RATES},capacity.FORMAT_RATES)
        self.assertEqual(minima['synthetic-handoff'],2826)
        self.assertNotIn('synthetic-handoff',capacity.FORMAT_RATES)
        self.assertEqual(capacity.OVERHEAD_RATE,min(capacity.FORMAT_RATES.values()))
        self.assertEqual(capacity.UNMEASURED_RATE,2580)
        self.assertEqual(len(witness['pages']),17)

    def test_unknown_page_reserve_can_hold_the_densest_measured_response(self):
        budget={'window_tokens':258400,'startup_tokens':82000,'lifecycle_tokens':48000,
                'margin_tokens':25840,'bytes_per_1000_tokens':2580}
        priced=capacity.price([],budget,initial_tokens=0,overhead_bytes=36751,overhead_request_bytes=1088)
        self.assertEqual(priced['estimated_tokens'],48000+30671)
        self.assertEqual(priced['pricing_policy'],'measured-formats-v2')
        for encoding,rate in [('source-text-v1',2113),('ram-set-columnar-v1',2035),('unknown',2580)]:
            call={'job':'read','operation':'navigate','arguments':{},'wire_bytes':20000,
                  'result':{'encoding':encoding}}
            request=len(json.dumps({k:call[k] for k in ('operation','arguments')}).encode())
            prior=math.ceil((20000+request)*1000/2580)
            expected=prior-math.ceil(20000*1000/2580)+math.ceil(20000*1000/rate)
            self.assertEqual(capacity.call_tokens(call)[0],expected)
        with self.assertRaisesRegex(ValueError,'EVIDENCE_REQUEST_INVALID'):
            capacity.price([],{**budget,'bytes_per_1000_tokens':3000},initial_tokens=0,
                           overhead_bytes=36751,overhead_request_bytes=1088)

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
