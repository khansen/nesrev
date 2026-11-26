"""Read recipes shared by delivery, measurement and argument admission.

An admission check proves discoverability, not that a model followed the recipe.
Historical price floors remain accounting rows; the ordered actual calls are
the executable workload whose argument provenance is checked here.
"""
import inspect

from . import declared_inputs, investigation as inv, navigation, ram_evidence
from .producer import require

EDITOR_INPUT = 'investigation-read-recipe'
READING_RULE = ('Add generation from status and offset from next_offset (initially 0). '
    'Keep the listed limit, reducing only the final page to the remaining record_count. '
    'Stop at record_count or next_offset=null. Lexical boundaries are not proof of semantics.')


def editor_recipe(inventory, edit_targets):
    from . import corridor_capacity
    reads=[]
    for job in corridor_capacity.plan(inventory):
        if job['name'].startswith('owners-') or job['name']=='ram-set':continue
        reads.append({'name':'editor-reread-'+job['name'],'operation':job['operation'],
            'arguments':job['arguments'],'record_count':len(job['records'])})
    reads.append({'name':'editor-lean-records','operation':'input',
        'arguments':{'input_id':'investigation-edit-targets','limit':40}})
    return {'reading_rule':READING_RULE,'reads':reads,'edit_target_count':len(edit_targets)}


def arguments(job, generation, offset=0, seen=0):
    args={'generation':generation,**job['arguments'],'offset':offset}
    if 'record_count' in job:
        args['limit']=min(args['limit'],job['record_count']-seen)
    return args


def defaults(operation, arguments):
    if operation=='navigate':function=navigation.Navigation.query
    elif operation=='evidence':function=ram_evidence.query
    elif operation=='input':
        if arguments.get('input_id')=='investigation-edit-targets':
            from .investigation_workflow import Workflow
            function=Workflow.editor_records
        else:function=declared_inputs.read
    elif operation=='status':return {}
    else:return {}
    return {key:p.default for key,p in inspect.signature(function).parameters.items()
            if p.default is not inspect.Parameter.empty}


def check(calls, recipe, declared_ids):
    """Name every unbound field; require prior same-query continuation results.

    Recipes are obtained from the service's fixed input, identified to the
    model before evidence reads. Startup IDs occur literally in its assembled
    input index. No value in the pricing report itself establishes a source.
    """
    errors=[];proof=[];generation=None;progress={};completed=set()
    reads=recipe.get('reads',[])
    def fault(index, field, reason):
        errors.append({'call':index,'operation':calls[index]['operation'],'field':field,'reason':reason})
    for index,call in enumerate(calls):
        op=call['operation'];args=call['arguments'];page=call['result'];sources={}
        if op=='status':
            for key in args:fault(index,key,'no default or delivered recipe')
            if index!=0:fault(index,'operation','unexpected status in fixed workload')
            generation=page.get('generation');proof.append(sources);continue
        startup=call['job'].startswith('startup-')
        if startup:
            if op!='input' or any(k[0]=='recipe' for k in progress):
                fault(index,'operation','startup input must precede evidence')
            ident=args.get('input_id');literal={'input_id':ident} if ident in declared_ids else {}
            key=('startup',ident);job={}
        else:
            # Matching never uses pagination: missing or guessed limits must
            # be diagnosed, not make the priced call disappear from the sweep.
            candidates=[(n,r) for n,r in enumerate(reads) if r['operation']==op and
                all(args.get(k)==v for k,v in r['arguments'].items() if k not in ('limit','offset'))]
            if len(candidates)!=1:
                for field in args:
                    if field not in ('generation','offset'):fault(index,field,'no matching delivered read recipe')
                proof.append(sources);continue
            n,job=candidates[0];literal=job['arguments'];key=('recipe',n)
        prior=progress.get(key);route=defaults(op,args)
        if key in completed:fault(index,'offset','read already complete')
        for field,value in args.items():
            if field=='generation':
                if generation is None or value!=generation:fault(index,field,'not copied from earlier status')
                else:sources[field]='response:status.generation'
            elif field=='offset':
                expected=prior['next_offset'] if prior else route.get('offset')
                if value!=expected:fault(index,field,'not the default or prior same-query next_offset')
                else:sources[field]='response:next_offset' if prior else 'default'
            elif field in literal:
                expected=literal[field]
                if field=='limit' and 'record_count' in job:
                    expected=min(expected,job['record_count']-(prior['seen'] if prior else 0))
                if value!=expected:fault(index,field,'differs from literal recipe or final-page rule')
                else:sources[field]='recipe:final-page' if expected!=literal[field] else 'recipe:literal'
            elif field in route and value==route[field]:sources[field]='default'
            else:fault(index,field,'no default, literal recipe or earlier result')
        for field in set(literal)-set(args):
            if field not in route or literal[field]!=route[field]:fault(index,field,'recipe argument omitted')
        if 'generation' not in args:fault(index,'generation','missing status identity')
        if 'offset' not in args and prior and prior['next_offset']!=route.get('offset'):
            fault(index,'offset','continuation offset omitted')
        if page.get('generation')!=generation:fault(index,'generation','response generation changed')
        seen=(prior['seen'] if prior else 0)+len(page.get('records',[]))
        progress[key]={'next_offset':page.get('next_offset'),'seen':seen}
        if page.get('next_offset') is None or ('record_count' in job and seen==job['record_count']):completed.add(key)
        if 'record_count' in job and seen>job['record_count']:fault(index,'limit','read crossed recipe boundary')
        proof.append(sources)
    for n,job in enumerate(reads):
        if ('recipe',n) not in completed:
            errors.append({'recipe':n,'field':'reads','reason':'recipe not completely priced'})
    for key in progress:
        if key not in completed:errors.append({'field':'offset','reason':'unfinished priced read','read':list(key)})
    return {'passed':not errors,'recipe_sha256':inv.identity(recipe),'calls':len(calls),
            'arguments':proof,'errors':errors}


def verify(calls, recipe, declared_ids):
    result=check(calls,recipe,declared_ids)
    require(result['passed'],'PAIR_INPUTS_CHANGED')
    return result
