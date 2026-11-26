"""Bind the editor's capacity decision to the actual prepared client artifacts.

The native declaration envelope is a preparation candidate until recaptured.
Pricing it cannot admit a new native pin. Positive growth is charged without
credit for shrinking another input or moving text between instructions/message.
"""
import copy
import io
import json
import math
from pathlib import Path

from . import bridge, corridor_capacity as capacity, declared_inputs, investigation as inv
from . import input_delivery, read_recipe
from .producer import require, sha

CAPS = {'handoff-wire-cap':65536, 'transition-index-and-receipt-wire-cap':8192,
        'phase-contract-extension-wire-cap':8192}


def read(path):
    return json.loads(Path(path).read_bytes())


def native_candidate(envelope, service_profile='corridor'):
    value=copy.deepcopy(envelope)
    groups=[g for g in value if g.get('name')=='mcp__facts']
    require(len(groups)==1 and len(groups[0]['tools'])==1,'PAIR_INPUTS_CHANGED')
    tool=groups[0]['tools'][0]; listing=bridge.tool_listing('implementer',service_profile)['tools'][0]
    require(tool['name']==listing['name']=='operation','PAIR_INPUTS_CHANGED')
    tool['description']=listing['description']; tool['parameters']=listing['inputSchema']
    # The pinned native client materializes this empty object in its schema.
    tool['parameters']['properties']['arguments'].setdefault('properties',{})
    return value


def stamp(data):
    return {'bytes':len(data),'sha256':inv.digest(data)}


def artifacts(controller, profile, native_envelope, service_profile='corridor'):
    config=read(Path(profile)/'launch.json')
    require(config['session']==str(controller.root) and config['service_profile']==service_profile,
            'PAIR_INPUTS_CHANGED')
    assembly=input_delivery.verify(controller.root,config['input_assembly'])
    require(assembly['role']=='implementer','PAIR_INPUTS_CHANGED')
    task=(Path(profile)/'message.txt').read_bytes()
    require(assembly['task'].encode()==task,'PAIR_TASK_CHANGED')
    instructions=(Path(profile)/'prompt.md').read_bytes()
    suffix=input_delivery.prompt(assembly,Path(config['workspace']),facts_images=True,
                                 images_enabled=service_profile=='corridor').encode()
    require(instructions.endswith(suffix),'PAIR_TASK_CHANGED')
    declaration=native_candidate(native_envelope,service_profile)
    model=controller.editor.model(controller.checked_editor()['pass_start_generation'])
    catalog=declared_inputs.load(model.capture)
    return {'instructions':stamp(instructions),'message':stamp(task),
        'native_declaration':stamp(inv.canonical(declaration)),
        'native_declaration_sha256':__import__('structured_codex_client').declaration_hash(declaration),
        'service_listing':stamp(inv.canonical(bridge.tool_listing('implementer',service_profile))),
        'assembly':stamp(Path(config['input_assembly']).read_bytes()),
        'startup_inputs':{i['id']:i['sha256'] for i in catalog['items'] if i['kind']!='reference_image'},
        'budget':assembly['startup']['budget']}


def emit(calls,job,operation,arguments,page):
    stream=io.StringIO()
    bridge.emit(None,len(calls)+1,{'result':{'content':[{'type':'text','text':json.dumps(page)}]}},stream,operation)
    wire=stream.getvalue(); result=json.loads(wire)['result']
    require(not result.get('isError'),'EVIDENCE_UNAVAILABLE')
    answer=json.loads(result['content'][0]['text'])
    require(answer['volume']['response_bytes']==len(wire.encode())<=24576,'RESPONSE_TOO_LARGE')
    calls.append({'job':job,'operation':operation,'arguments':arguments,
                  'wire_bytes':len(wire.encode()),'result':answer})


def measure(flow, startup_ids):
    from . import analogue_inputs, navigation
    controller=flow.controller; flow.checked()
    generation=flow.config['catalog']['binding']['generation']
    model=controller.editor.model(generation); calls=[]
    capacity.check_startup(model,startup_ids)
    emit(calls,'startup-status','status',{},controller.dispatch('status',{},'implementer'))
    for ident in startup_ids:
        offset=0
        while offset is not None:
            args={'generation':generation,'input_id':ident,'limit':8192,'offset':offset}
            page=controller.dispatch('input',args,'implementer')
            emit(calls,'startup-'+ident,'input',args,page); offset=page['next_offset']
    for job in flow.editor_recipe()['reads']:
        offset=0;seen=0
        while offset is not None:
            request=read_recipe.arguments(job,generation,offset,seen)
            args={k:v for k,v in request.items() if k!='generation'}
            if job['operation']=='input':
                page=inv.record_page(flow.config['catalog'],model,flow.config['edit_targets'],
                    offset=offset,limit=args['limit'],view='edit')
            else:
                source=analogue_inputs.project(model,args.pop('analogue_index')) if 'analogue_index' in args else model
                page={'generation':generation,**navigation.Navigation(source).query(**args)}
            emit(calls,job['name'],job['operation'],request,page)
            seen+=len(page.get('records',[]));offset=page.get('next_offset')
            if 'record_count' in job:
                require(offset is not None or seen>=job['record_count'],'EVIDENCE_UNAVAILABLE')
                if seen>=job['record_count']:break
    return calls


def bound_price(baseline, actual, budget, initial_basis, current, previous):
    """Keep the approved reservations and charge every unreserved increase."""
    require(baseline['charges']==CAPS,'PAIR_INPUTS_CHANGED')
    require(set(current)==set(previous)=={'instructions','message','native_declaration'},'PAIR_INPUTS_CHANGED')
    require(initial_basis['initial_tokens']>=0 and initial_basis['framing_tokens']>=0 and
            initial_basis['declaration_bytes']>=0,'PAIR_INPUTS_CHANGED')
    worst=budget['bytes_per_1000_tokens']
    growth={key:max(0,current[key]['bytes']-previous[key]['bytes']) for key in current}
    initial=initial_basis['initial_tokens']+initial_basis['framing_tokens']+math.ceil(
        (growth['instructions']+growth['message']+max(initial_basis['declaration_bytes'],
         growth['native_declaration']))*1000/worst)
    pricing=baseline['pricing']; initial=max(initial,pricing['initial_tokens'])
    base=capacity.price(baseline['calls'],budget,**pricing)
    require(base==baseline['price'],'PAIR_INPUTS_CHANGED')
    old_jobs={c['job'] for c in baseline['calls'] if not c.get('reservation')}
    require({c['job'] for c in actual}==old_jobs,'PAIR_INPUTS_CHANGED')
    calls=[]; deltas={}
    for job in sorted(old_jobs):
        old=[c for c in baseline['calls'] if c['job']==job]
        new=[c for c in actual if c['job']==job]
        # The reference's entire extension reservation is already charged at
        # the worst rate. Other smaller deliveries cannot subsidize growth.
        if job=='startup-operation-reference':
            delta=max(0,sum(c['wire_bytes'] for c in new)-sum(c['wire_bytes'] for c in old))
            require(delta<=CAPS['phase-contract-extension-wire-cap'],'PAIR_INPUTS_CHANGED')
            calls.extend(old); deltas[job]={'reserved_growth_bytes':delta}; continue
        def charge(rows):
            p=capacity.price(rows,budget,initial_tokens=0,overhead_bytes=pricing['overhead_bytes'],
                             overhead_request_bytes=pricing['overhead_request_bytes'])
            return p['estimated_tokens'],sum(c['wire_bytes'] for c in rows)
        before=charge(old); after=charge(new)
        # Retaining the more expensive prior delivery also retains its request
        # framing. Both current and baseline pages remain in the binding.
        chosen=new if after[0]>before[0] else old
        calls.extend(chosen)
        deltas[job]={'tokens':max(0,after[0]-before[0]),'wire_bytes':after[1]-before[1]}
    calls.extend(c for c in baseline['calls'] if c.get('reservation'))
    result=capacity.price(calls,budget,**{**pricing,'initial_tokens':initial})
    # A token-cheaper representation must not hide a larger byte allowance.
    actual_bytes=sum(c['wire_bytes'] for c in actual if not c['job'].startswith('startup-'))
    reserved=sum(CAPS.values())
    if result['investigation_response_bytes']<actual_bytes+reserved:
        result['investigation_response_bytes']=actual_bytes+reserved
        result['required_bytes']=actual_bytes+reserved+pricing['overhead_bytes']+24576
        result['passed']=result['passed'] and result['required_bytes']<=result['allowance_bytes']
    return {'price':result,'initial_tokens':initial,'positive_initial_growth_bytes':growth,
            'deltas':deltas,'priced_calls':calls}


def bind(flow, profile, baseline, initial_basis, previous, startup_ids, native_envelope):
    captured=artifacts(flow.controller,profile,native_envelope)
    actual=measure(flow,startup_ids)
    recipe=flow.editor_recipe()
    argument_check=read_recipe.verify(actual,recipe,captured['startup_inputs'])
    transition_bytes=flow.prepared_transition_wire_bytes()
    require(transition_bytes<=CAPS['transition-index-and-receipt-wire-cap'],'PAIR_INPUTS_CHANGED')
    totals=bound_price(baseline,actual,captured['budget'],initial_basis,
                       {k:captured[k] for k in previous},previous)
    return {'schema':'editor-admission-v1','session':str(flow.controller.root),
        'profile':str(Path(profile).resolve()),'plan_sha256':sha(flow.root/'plan.json'),
        'generation':flow.config['catalog']['binding']['generation'],
        'edit_targets':flow.config['edit_targets'],'artifacts':captured,
        'baseline':baseline,'initial_basis':initial_basis,'previous_artifacts':previous,
        'startup_ids':startup_ids,'actual_calls':actual,'read_recipe':recipe,
        'argument_check':argument_check,'transition_wire_bytes':transition_bytes,**totals,
        'native_envelope':native_envelope,'native_capture_pending':True}


def verify(controller, config, *, require_capture=True):
    from .investigation_workflow import Workflow
    gate=controller.checked_editor()['investigation_gate']; flow=Workflow(gate['root'],controller)
    report=read(controller.root/'editor-admission.json')
    profile=Path(config['input_assembly']).parent.parent
    require(report['schema']=='editor-admission-v1' and report['session']==str(controller.root) and
        report['profile']==str(profile) and report['plan_sha256']==sha(flow.root/'plan.json') and
        report['generation']==controller.editor.state['pass_start_generation'] and
        report['edit_targets']==flow.config['edit_targets'],'PAIR_INPUTS_CHANGED')
    captured=artifacts(controller,profile,report['native_envelope'])
    require(captured==report['artifacts'],'PAIR_INPUTS_CHANGED')
    recipe=flow.editor_recipe()
    require(report.get('read_recipe')==recipe and report.get('argument_check')==
        read_recipe.verify(report['actual_calls'],recipe,captured['startup_inputs']),'PAIR_INPUTS_CHANGED')
    require(report.get('transition_wire_bytes')==flow.prepared_transition_wire_bytes()<=
        CAPS['transition-index-and-receipt-wire-cap'],'PAIR_INPUTS_CHANGED')
    totals=bound_price(report['baseline'],report['actual_calls'],captured['budget'],report['initial_basis'],
        {k:captured[k] for k in report['previous_artifacts']},report['previous_artifacts'])
    require(all(report[k]==v for k,v in totals.items()) and totals['price']['passed'],'PAIR_INPUTS_CHANGED')
    if require_capture:
        require(config['tool_declaration_sha256']==captured['native_declaration_sha256'],
                'CODEX_TOOL_DECLARATION_CHANGED')
    return report
