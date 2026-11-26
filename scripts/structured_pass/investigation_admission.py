"""Bind whole-partition admission to the final readonly profile and native data."""
import math
from pathlib import Path

from . import analogue_inputs, corridor_capacity as capacity, edit_contract, editor_admission as editor
from . import investigation as inv, navigation, ram_evidence, read_recipe
from .investigation_service import Session
from .investigation_workflow import input_wire_bytes, read
from .producer import require, sha


def task(entry_id):
    return (
        'Investigate the frozen corridor partition '+entry_id+'. Use only the facts service and declared evidence. '
        'Start with status: its transition receipt identifies the predecessor checks performed before this context. '
        'Read investigation-assignment and investigation-contract completely, then the declared startup inputs. '
        'Retrieve the assignment\'s handoff_inputs, if any, and recheck their claims against your assigned evidence. '
        'Follow every assigned source and RAM read to its stated boundary. These are coverage obligations, '
        'not conclusions about names, ownership or behavior. Keep possible aliases and unresolved accesses unknown.\n\n'
        'Use source for reading and edit records only when their identities or expressions are needed. '
        'Cite service record, fact or input identities for every supported claim. An absence claim requires '
        'complete coverage of its searched sets. Proposed names must identify their local supporting evidence '
        'and any contrary evidence. Submit claims, decisions and unresolved questions through checkpoint; '
        'the service determines completion from the final native audit. A final prose answer is not a checkpoint. '
        'This phase cannot edit, validate, publish, approve or apply a candidate.\n\n'
        'Respect the delivered byte allowance, next-response reservation and eight logical requests per question; '
        'unchanged-query continuation pages are one logical request but all their bytes count. '
        'Correct your own correctable refusals, retry transient busy responses within the deadline, and stop on '
        'terminal refusals. If a boundary or allowance prevents completion, submit a truthful partial checkpoint '
        'with the remaining evidence unknown. Do not expand the plan or start another context. '
        'After compaction, re-read evidence before claiming coverage: earlier deliveries no longer count.\n')


def measure(session, startup_ids):
    flow=session.workflow;flow.checked();generation=flow.config['catalog']['binding']['generation']
    model=flow.controller.editor.model(generation);calls=[];capacity.check_startup(model,startup_ids)
    editor.emit(calls,'startup-status','status',{},session.status())
    for ident in startup_ids:
        offset=0
        while offset is not None:
            args={'generation':generation,'input_id':ident,'limit':8192,'offset':offset}
            page=flow.controller.dispatch('input',args,'implementer')
            editor.emit(calls,'startup-'+ident,'input',args,page);offset=page['next_offset']
    covered=set()
    for job in session.assignment()['reads']:
        offset=0;seen=0
        while offset is not None:
            args=read_recipe.arguments(job,generation,offset,seen)
            if job['operation']=='evidence':page=ram_evidence.query(model,**args)
            else:
                source=analogue_inputs.project(model,args['analogue_index']) if 'analogue_index' in args else model
                page={'generation':generation,**navigation.Navigation(source).query(**{
                    k:v for k,v in args.items() if k not in ('generation','analogue_index')})}
            editor.emit(calls,'assigned-evidence',job['operation'],args,page)
            covered.update(flow.units(job['operation'],args,page))
            seen+=len(page.get('records',[]));offset=page.get('next_offset')
            if 'record_count' in job and seen>=job['record_count']:break
    require(set(session.entry['units'])<=covered,'INVESTIGATION_COVERAGE_INCOMPLETE')
    return calls


def totals(baseline, actual, budget, pricing, current, previous, basis, assignment, generation, cap,
           parent_caps=None):
    """Keep old startup charges; measure all phase growth without borrowing caps."""
    require(set(current)==set(previous)=={'instructions','message','native_declaration'},'PAIR_INPUTS_CHANGED')
    require(capacity.price(baseline,budget,**pricing)['passed'],'PAIR_INPUTS_CHANGED')
    expected={c['job'] for c in baseline if not c.get('reservation')}
    require({c['job'] for c in actual}==expected,'PAIR_INPUTS_CHANGED')
    growth={k:max(0,current[k]['bytes']-previous[k]['bytes']) for k in current}
    initial=max(pricing['initial_tokens'],basis['initial_tokens']+basis['framing_tokens']+math.ceil(
        (growth['instructions']+growth['message']+max(basis['declaration_bytes'],growth['native_declaration']))
        *1000/capacity.UNMEASURED_RATE))
    calls=[];reference_growth=0
    for job in sorted(expected):
        before=[c for c in baseline if c['job']==job];after=[c for c in actual if c['job']==job]
        if job=='startup-operation-reference':
            reference_growth=max(0,sum(c['wire_bytes'] for c in after)-sum(c['wire_bytes'] for c in before))
            calls.extend(before)
        elif job.startswith('startup-'):
            old=capacity.price(before,budget,**pricing)['estimated_tokens']
            new=capacity.price(after,budget,**pricing)['estimated_tokens']
            calls.extend(after if new>old else before)
        else:calls.extend(after)
    phase_bytes=reference_growth+input_wire_bytes(edit_contract.investigation_reference(),
        'investigation-contract',generation)+input_wire_bytes(assignment,'investigation-assignment',generation)
    old_caps={c['job']:c['wire_bytes'] for c in baseline if c.get('reservation')}
    require(set(old_caps)=={'checkpoint-output-cap','phase-contract-and-assignment'} and
            old_caps['checkpoint-output-cap']==cap,'PAIR_INPUTS_CHANGED')
    caps={'checkpoint-output-cap':cap,
          'phase-contract-and-assignment':max(8192,phase_bytes,old_caps['phase-contract-and-assignment'])}
    if parent_caps:caps['predecessor-handoff-wire-cap']=sum(parent_caps.values())
    for job,size in caps.items():
        calls.append({'job':job,'operation':'input','arguments':{},'wire_bytes':size,'reservation':True})
    return {'price':capacity.price(calls,budget,**{**pricing,'initial_tokens':initial}),
            'initial_tokens':initial,'positive_initial_growth_bytes':growth,'phase_wire_bytes':phase_bytes,
            'caps':caps,'priced_calls':calls}


def bind(flow, profile, baseline, pricing, basis, previous, startup_ids, native_envelope):
    config=read(Path(profile)/'launch.json');session=Session(config['bridge_root'])
    require(session.workflow.root==flow.root,'PAIR_PROFILE_MISMATCH')
    captured=editor.artifacts(flow.controller,profile,native_envelope,'investigation')
    actual=measure(session,startup_ids);assignment=session.assignment()
    generation=flow.config['catalog']['binding']['generation'];entry=session.entry['id']
    result=totals(baseline,actual,captured['budget'],pricing,
        {k:captured[k] for k in previous},previous,basis,assignment,generation,flow.config['checkpoint_caps'][entry],
        {p:flow.config['checkpoint_caps'][p] for p in flow.config.get('handoff_dependencies',{}).get(entry,[])})
    argument_check=read_recipe.verify(actual,assignment,captured['startup_inputs'])
    return {'schema':'investigation-admission-v1','profile':str(Path(profile).resolve()),'entry_id':entry,
        'plan_sha256':sha(flow.root/'plan.json'),'artifacts':captured,'baseline':baseline,'pricing':pricing,
        'initial_basis':basis,'previous_artifacts':previous,'startup_ids':startup_ids,
        'actual_calls':actual,'assignment':assignment,'native_envelope':native_envelope,
        'argument_check':argument_check,**result}


def verify(flow, profile, report_path, *, require_capture=True):
    config=read(Path(profile)/'launch.json');report=read(report_path);session=Session(config['bridge_root'])
    require(report['schema']=='investigation-admission-v1' and report['profile']==str(Path(profile).resolve()) and
            report['entry_id']==session.entry['id'] and session.workflow.root==flow.root and
            report['plan_sha256']==sha(flow.root/'plan.json'),'PAIR_INPUTS_CHANGED')
    captured=editor.artifacts(flow.controller,profile,report['native_envelope'],'investigation')
    require(captured==report['artifacts'] and session.assignment()==report['assignment'],'PAIR_INPUTS_CHANGED')
    require(report.get('argument_check')==read_recipe.verify(report['actual_calls'],session.assignment(),
        captured['startup_inputs']),'PAIR_INPUTS_CHANGED')
    coverage=set()
    for call in report['actual_calls']:
        coverage.update(flow.units(call['operation'],call['arguments'],call['result']))
    require(set(session.entry['units'])<=coverage,'INVESTIGATION_COVERAGE_INCOMPLETE')
    result=totals(report['baseline'],report['actual_calls'],captured['budget'],report['pricing'],
        {k:captured[k] for k in report['previous_artifacts']},report['previous_artifacts'],report['initial_basis'],
        session.assignment(),flow.config['catalog']['binding']['generation'],
        flow.config['checkpoint_caps'][session.entry['id']],
        {p:flow.config['checkpoint_caps'][p] for p in
         flow.config.get('handoff_dependencies',{}).get(session.entry['id'],[])})
    require(all(report[k]==v for k,v in result.items()) and result['price']['passed'],'PAIR_INPUTS_CHANGED')
    if require_capture:
        require(config['tool_declaration_sha256']==captured['native_declaration_sha256'],
                'CODEX_TOOL_DECLARATION_CHANGED')
    return report
