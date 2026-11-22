"""Measure a complete declared corridor through the same bridge the clients use."""
import argparse
import io
import json
import math
from pathlib import Path

from . import bridge, corridor_inventory, producer, startup_inputs
from .launcher import Corridor


# Lowest page wire-bytes/token rate per measured startup input across the two
# retained runs, rounded down to bytes per 1000 tokens. The token count after
# call N describes its input; output N first contributes to call N+1's count.
# Includes partial pages and assistant/framing growth. Measurement rows and
# rollout hashes are pinned in tests/fixtures/structured_startup_rates.json.
STARTUP_RATES = {
    'operation-reference': 3849,
    'guidance-0': 3331,
    'guidance-1': 2625,
    'guidance-2': 3094,
    'guidance-3': 3642,
    'guidance-startup': 3097,
    'manual-text': 3293,
    'faq-text': 3718,
    'intake-receipt': 3152,
    'reference-decision': 2858,
    'comparison-document-0': 3951,
}


def check_startup(model,identities):
    from . import declared_inputs
    items=declared_inputs.load(model.capture)['items']
    required={'operation-reference','guidance-startup'}|{i['id'] for i in items
        if i['kind'] in ('reference_text','intake_receipt','reference_decision')}
    producer.require(isinstance(identities,list) and all(isinstance(i,str) for i in identities) and
        len(identities)==len(set(identities)) and required<=set(identities)<=set(i['id'] for i in items),
        'PAIR_INPUTS_CHANGED')


def code_pins():
    return {p.name:producer.sha(p) for p in sorted(Path(__file__).resolve().parent.glob('*.py'))}


def prompt(report):
    inv=report['inventory'];price=report['price']
    reading={'generation':report['generation'],'inventory_sha256':inv['inventory_sha256'],
        'roots':[{'symbol':r['choice']['symbol'],'last_record_id':r['records'][-1]} for r in inv['roots']],
        'ram_addresses':inv['ram_addresses'],
        'access_owner_ids':[b['owner_id'] for b in inv['access_owner_blocks']],
        'helpers':[{'symbol':h['choice']['symbol'],'last_record_id':h['records'][-1]} for h in inv['helpers']],
        'analogues':[{'index':a['choice']['index'],'symbol':a['choice']['symbol'],
                      'last_record_id':a['records'][-1]} for a in inv['analogues']]}
    return ('\n## Prepared whole-corridor workload\n'
        'The following inventory comes from the retained assembler model and the operator-selected '
        'boundaries. It is reading coverage, not a naming or ownership conclusion. Read the source '
        'roots, access-owner blocks, helper interfaces and both analogues. Read the entire ram_addresses '
        'set with evidence ram_set, keeping every possible and unresolved access. Use navigate source '
        'for reading; fetch full records and preimages only for edits. Branches outside these bounds '
        'or new essential evidence still require investigation within the allowance, or a decision.\n'
        +json.dumps(reading,sort_keys=True)+'\n'
        +f"Preparation measured {price['investigation_response_bytes']} investigation response bytes. "
        +f"With {price['overhead_bytes']} bytes of observed unscripted overhead and a "
        +f"{price['next_response_bytes']}-byte next response, this uses {price['required_bytes']} "
        +f"of the {price['allowance_bytes']}-byte investigation allowance. "
        'These are preparation measurements, not extra allowances or a guarantee of semantic closure.\n')


def verify_report(controller,report,task,budget):
    producer.require(report.get('schema')=='corridor-capacity-v1' and not report.get('legacy') and
        report['session']==str(controller.root.resolve()) and report['code']==code_pins(), 'PAIR_INPUTS_CHANGED')
    producer.require(report['generation']==controller.editor.state['pass_start_generation'], 'PAIR_INPUTS_CHANGED')
    inventory=report['inventory'];selection=report['selection']
    model=controller.editor.model(report['generation'])
    corridor_inventory.verify(model,inventory)
    check_startup(model,selection['startup_ids'])
    producer.require(selection['corridor']==inventory['spec'] and selection['budget']==budget,
                     'PAIR_INPUTS_CHANGED')
    producer.require(all(c['arguments'].get('generation',report['generation'])==report['generation'] and
        c['result']['generation']==report['generation'] for c in report['calls']),
                     'PAIR_INPUTS_CHANGED')
    verify_coverage(inventory,report['calls'],False,selection['startup_ids'])
    computed=price(report['calls'],budget,**selection['pricing'])
    producer.require(computed==report['price'] and computed['passed'] and report.get('passed') is True and
        not inventory['open_root_transfers'] and prompt(report) in task,'PAIR_INPUTS_CHANGED')
    return report


def expand(page):
    if page.get('encoding')=='source-text-v1':
        return [dict(zip(page['columns'],row)) for row in page['records']]
    if page.get('encoding')=='source-records-columnar-v1':
        rows=[]
        for values in page['records']:
            row={**page['constants'],**dict(zip(page['schemas'][values[0]],values[1:]))}
            if 'layout' in row:
                row['layout']={'length':row['layout'],**{k:row[k] for k in
                    ('cpu_address','output_offset','bytes','segment_id')}}
            rows.append(row)
        return rows
    return page.get('records',[])


def plan(inventory,legacy=False):
    view='records_compact' if legacy else 'source'
    jobs=[]
    def source(name,selector,records,span='label',**extra):
        jobs.append({'name':name,'operation':'navigate','arguments':{
            'view':view,'limit':40 if legacy else min(128,len(records)),
            'span':span,**selector,**extra},'records':records})
    source('vector',{'symbol':inventory['spec']['vector']},inventory['vector_records'])
    for index,root in enumerate(inventory['roots']):
        source('root-'+str(index),{'symbol':root['choice']['symbol']},root['records'],'segment')
    for index,helper in enumerate(inventory['helpers']):
        source('helper-'+str(index),{'symbol':helper['choice']['symbol']},helper['records'],'segment')
    blocks=inventory['access_owner_blocks']
    if legacy:
        for index,block in enumerate(blocks):
            source('owners-'+str(index),{'record_id':block['owner_id']},block['records'])
        for address in inventory['ram_addresses']:
            jobs.append({'name':'ram-'+str(address),'operation':'evidence','arguments':{
                'view':'ram_summary','address':address,'limit':128}})
    else:
        for first in range(0,len(blocks),128):
            part=blocks[first:first+128]
            source('owners-'+str(first),{'record_id':[b['owner_id'] for b in part]},
                   list(dict.fromkeys(r for b in part for r in b['records'])))
        if inventory['ram_addresses']:
            jobs.append({'name':'ram-set','operation':'evidence','arguments':{
                'view':'ram_set','address':inventory['ram_addresses'],'limit':128}})
    for index,analogue in enumerate(inventory['analogues']):
        source('analogue-'+str(index),{'symbol':analogue['choice']['symbol']},analogue['records'],
               'segment',analogue_index=analogue['choice']['index'])
    return jobs


def measure(session,inventory,*,legacy=False,startup_ids=()):
    c=Corridor(session);generation=c.editor.state['current']
    corridor_inventory.verify(c.editor.model(generation),inventory)
    jobs=[{'name':'startup-status','operation':'status','arguments':{} }]+[{'name':'startup-'+identity,'operation':'input','arguments':{
            'input_id':identity,'limit':8192}} for identity in startup_ids]+plan(inventory,legacy)
    calls=[];output=io.StringIO()
    class Stream:
        def __iter__(self):
            for job in jobs:
                offset=0;seen=set()
                while offset is not None:
                    args=({} if job['operation']=='status' else
                          {'generation':generation,**job['arguments'],'offset':offset})
                    request={'operation':job['operation'],'arguments':args}
                    yield json.dumps({'id':len(calls)+1,'method':'tools/call','params':{
                        'name':'operation','arguments':request}})+'\n'
                    wire=output.getvalue();output.seek(0);output.truncate()
                    result=json.loads(wire)['result'];page=json.loads(result['content'][0]['text'])
                    producer.require(not result.get('isError'),'EVIDENCE_UNAVAILABLE')
                    producer.require(len(wire.encode())==page['volume']['response_bytes']<=24576,'RESPONSE_TOO_LARGE')
                    calls.append({'job':job['name'],**request,'wire_bytes':len(wire.encode()),'result':page})
                    seen.update(r['record_id'] for r in expand(page) if isinstance(r,dict) and 'record_id' in r)
                    if job.get('records') and set(job['records'])<=seen:break
                    offset=page.get('next_offset')
                if 'records' in job:producer.require(set(job['records'])<=seen,'EVIDENCE_UNAVAILABLE')
    bridge.mcp(session,'implementer','corridor',Stream(),output)
    verify_coverage(inventory,calls,legacy,startup_ids)
    return calls


def verify_coverage(inventory,calls,legacy,startup_ids):
    jobs=[{'name':'startup-status','operation':'status','arguments':{} }]+[{'name':'startup-'+i,'operation':'input','arguments':{'input_id':i,'limit':8192}}
          for i in startup_ids]+plan(inventory,legacy)
    producer.require(set(c['job'] for c in calls)==set(j['name'] for j in jobs),'EVIDENCE_UNAVAILABLE')
    for job in jobs:
        pages=[c for c in calls if c['job']==job['name']];expected_offset=0;seen=set()
        for call in pages:
            args=call['arguments'];page=call['result']
            if job['operation']=='status':
                producer.require(len(pages)==1 and args=={} and call['operation']=='status','EVIDENCE_UNAVAILABLE')
                expected_offset=None
                continue
            producer.require(call['operation']==job['operation'] and
                {k:v for k,v in args.items() if k not in ('generation','offset')}==job['arguments'] and
                args['offset']==expected_offset and page['generation']==args['generation'], 'EVIDENCE_UNAVAILABLE')
            producer.require(call['wire_bytes']==page['volume']['response_bytes']<=24576,'RESPONSE_TOO_LARGE')
            seen.update(r['record_id'] for r in expand(page) if isinstance(r,dict) and 'record_id' in r)
            expected_offset=page.get('next_offset')
        producer.require(set(job['records'])<=seen if 'records' in job else expected_offset is None,
                         'EVIDENCE_UNAVAILABLE')


def price(calls,budget,*,initial_tokens,overhead_bytes,overhead_request_bytes):
    budget=startup_inputs.allowance({k:budget[k] for k in ('window_tokens','startup_tokens',
        'lifecycle_tokens','margin_tokens','bytes_per_1000_tokens')})
    producer.require(budget['lifecycle_tokens']>=48000 and overhead_bytes>=36751,'EVIDENCE_REQUEST_INVALID')
    worst=budget['bytes_per_1000_tokens'];tokens=lambda size,rate:math.ceil(size*1000/rate)
    startup=initial_tokens;evidence=0;response_bytes=0;request_bytes=0;hash_characters=0
    for call in calls:
        arguments_size=len(json.dumps({k:call[k] for k in ('operation','arguments')}).encode())
        identity=call['arguments'].get('input_id','')
        if call['job'].startswith('startup-'):
            fallback=3860 if identity.startswith('guidance-') or identity in ('manual-text','faq-text') else worst
            rate=STARTUP_RATES.get(identity,fallback)
            startup+=tokens(call['wire_bytes'],rate)+tokens(arguments_size,worst)
        else:
            response_bytes+=call['wire_bytes'];request_bytes+=arguments_size
            hashes=0
            if call.get('result',{}).get('encoding')=='source-edit-v1':
                from . import edit_records
                hashes=edit_records.hash_characters([call['result'],call['arguments']])
                producer.require(hashes<=call['wire_bytes']+arguments_size,'EVIDENCE_REQUEST_INVALID')
            hash_characters+=hashes
            evidence+=tokens(call['wire_bytes']+arguments_size-hashes,worst)+hashes
    required_bytes=response_bytes+overhead_bytes+24576
    total=startup+evidence+budget['lifecycle_tokens']+tokens(overhead_bytes+overhead_request_bytes+24576,worst)
    return {'startup_tokens':startup,'investigation_response_bytes':response_bytes,
        'investigation_request_bytes':request_bytes,'overhead_bytes':overhead_bytes,
        'overhead_request_bytes':overhead_request_bytes,'next_response_bytes':24576,
        'required_bytes':required_bytes,'allowance_bytes':budget['response_bytes'],
        'estimated_tokens':total,'window_tokens':budget['window_tokens'],
        'headroom_tokens':budget['window_tokens']-total,'margin_tokens':budget['margin_tokens'],
        'lifecycle_tokens':budget['lifecycle_tokens'],
        'edit_hash_characters_at_one_token_each':hash_characters,
        'passed':startup<=budget['startup_tokens'] and required_bytes<=budget['response_bytes'] and
                 total+budget['margin_tokens']<=budget['window_tokens']}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--session',type=Path,required=True)
    parser.add_argument('--selection',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--legacy',action='store_true')
    args=parser.parse_args();selection=json.loads(args.selection.read_bytes())
    producer.require(not args.output.exists(),'PREPARATION_EXISTS')
    c=Corridor(args.session);generation=c.editor.state['current']
    inventory=corridor_inventory.build(c.editor.model(generation),selection['corridor'])
    check_startup(c.editor.model(generation),selection['startup_ids'])
    calls=measure(args.session,inventory,legacy=args.legacy,startup_ids=selection['startup_ids'])
    result={'schema':'corridor-capacity-v1','session':str(args.session.resolve()),'generation':generation,
        'legacy':args.legacy,'selection':selection,'inventory':inventory,'calls':calls,
        'price':price(calls,selection['budget'],**selection['pricing']),
        'code':code_pins(),
        'provider_calls':0,'native_invocations':0}
    result['passed']=result['price']['passed'] and not inventory['open_root_transfers']
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'price':result['price'],'calls':len(calls),'inventory':inventory['inventory_sha256']}))
    return 0 if result['passed'] else 3

if __name__=='__main__':raise SystemExit(main())
