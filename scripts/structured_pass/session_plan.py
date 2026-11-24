"""Sequential investigation entries followed by the existing review pair.

All entries spend the pair's persisted invocation count and wall deadline.
Recovery can accept a finished, audited checkpoint after a coordinator crash;
it cannot repeat a client or turn an interrupted invocation into a success.
"""
import time
import uuid
from pathlib import Path

from . import investigation as inv, session_slots
from .investigation_workflow import Workflow, read
from .producer import require, sha


def bind(root, controller, investigators, editor, reviewer, files):
    import structured_codex_client as codex
    from . import investigation_admission
    flow=Workflow(controller.editor.state['investigation_gate']['root'],controller)
    flow.checked()
    require(isinstance(investigators,list) and investigators and
            all(set(r)=={'entry_id','profile','admission'} for r in investigators), 'PAIR_PROFILE_MISMATCH')
    rows=[{**r,'profile':str(Path(r['profile']).resolve()),
           'admission':str(Path(r['admission']).resolve(strict=True))} for r in investigators]
    require([r['entry_id'] for r in rows]==[e['id'] for e in flow.config['partitions']['entries']],
            'INVESTIGATION_PLAN_INVALID')
    require(len({r['profile'] for r in rows})==len(rows) and
            editor.get('pair_root')==reviewer.get('pair_root')==str(root),'PAIR_PROFILE_MISMATCH')
    for row in rows:
        profile=Path(row['profile']);config=codex.verify(profile)
        endpoint=read(Path(config['bridge_root'])/'investigation-profile.json')
        require(config.get('pair_root')==str(root) and config['service_profile']=='investigation' and
                endpoint['entry_id']==row['entry_id'] and endpoint['workflow']==str(flow.root) and
                all(config[k]==editor[k] for k in ('session','auth_home','heavy_lock','model','effort')),
                'PAIR_PROFILE_MISMATCH')
        require(not read(profile/'state.json')['runs'],'PAIR_PROFILES_NOT_FRESH')
        investigation_admission.verify(flow,profile,row['admission'])
        for path in (profile/'launch.json',Path(row['admission'])):files[str(path)]=sha(path)
    require(len({editor['auth_home'],*[codex.verify(Path(r['profile']))['auth_home'] for r in rows]})==1,
            'PAIR_PROFILE_MISMATCH')
    files[str(flow.root/'plan.json')]=sha(flow.root/'plan.json')
    return {'workflow':str(flow.root),'investigators':rows,
            'editing_roles':['implementer','reviewer','implementer','reviewer','implementer']}


def verify(root, config, controller):
    import structured_codex_client as codex
    from . import investigation_admission
    plan=config['session_plan'];flow=Workflow(plan['workflow'],controller);flow.checked(historical=True)
    require(set(plan)=={'workflow','investigators','editing_roles'} and
            plan['editing_roles']==['implementer','reviewer','implementer','reviewer','implementer'] and
            [r['entry_id'] for r in plan['investigators']]==
            [e['id'] for e in flow.config['partitions']['entries']], 'INVESTIGATION_PLAN_INVALID')
    editor=read(Path(config['profiles']['implementer'])/'launch.json')
    reviewer=read(Path(config['profiles']['reviewer'])/'launch.json')
    require(editor.get('pair_root')==reviewer.get('pair_root')==str(root),'PAIR_PROFILE_MISMATCH')
    for row in plan['investigators']:
        profile=Path(row['profile']);client=codex.verify(profile)
        endpoint=read(Path(client['bridge_root'])/'investigation-profile.json')
        require(client.get('pair_root')==str(root) and client['service_profile']=='investigation' and
                endpoint['entry_id']==row['entry_id'] and endpoint['workflow']==str(flow.root) and
                all(client[k]==editor[k] for k in ('session','auth_home','heavy_lock','model','effort')),
                'PAIR_PROFILE_MISMATCH')
        investigation_admission.verify(flow,profile,row['admission'])


def finished_audit(profile):
    import structured_codex_client as codex
    profile=Path(profile);config=codex.verify(profile);state=read(profile/'state.json')
    require(not state.get('halted') and len(state['runs'])==1 and
            state['runs'][0]['status']=='finished' and not state['runs'][0]['continuation'] and
            state['thread_id'], 'PAIR_RECOVERY_REQUIRED')
    codex.require_quiescent_runs(state,config)
    return codex.investigation_audit(codex.auth_home(profile,config),state['thread_id'],
                                     expected=config['tool_declaration_sha256'])


def audits(config, identifiers):
    result={row['entry_id']:finished_audit(row['profile'])
            for row in config['session_plan']['investigators'] if row['entry_id'] in identifiers}
    require(set(result)==set(identifiers) and
            len({audit['session_id'] for audit in result.values()})==len(result),'PAIR_RECOVERY_REQUIRED')
    return result


def admit_editor(config):
    flow=Workflow(config['session_plan']['workflow'])
    checked=audits(config,[e['id'] for e in flow.config['partitions']['entries']])
    with flow.controller.editor.transaction(write=True):
        state=flow.checked(historical=True)
        if not state['editing']:return flow.admit_editor(checked)
        # Later turns remain in the same editor context, after publication.
        # The old handoffs stay historical; they are never rebound to new facts.
        for ident,audit in checked.items():flow.check_saved(ident,audit,state)
        require(flow.controller.editor.state['investigation_gate']['editing_admitted']==
                inv.identity(state['editing']),'INVESTIGATION_CHANGED')
        flow.check_handoff_cap(state)
        return state['editing']


def complete(root, config, row):
    """Reconcile an already finished invocation, including after a crash."""
    import structured_pair_launcher as pair
    process=read(root/'turns'/row['id']/'process.json')
    require(process.get('exit_code')==0 and process.get('processes_reconciled') is True and
            not process.get('error') and not process.get('cleanup_error'),'PAIR_RECOVERY_REQUIRED')
    pair.processes.require_quiescent({'runs':[process]})
    session_slots.finish(root,row)
    flow=Workflow(config['session_plan']['workflow']);audit=finished_audit(row['profile'])
    with flow.controller.editor.transaction(write=True):
        state=flow.checked();session=state['sessions'].get(row['entry_id'])
        require(session and session['session_id']==row['id'],'INVESTIGATION_TRANSITION_INVALID')
        if session['accepted']:
            checkpoint=inv.handoff(flow.check_saved(row['entry_id'],audit,state),flow.config['catalog'])
        else:checkpoint=flow.finalize(row['entry_id'],audit)
    row.update(result='checkpoint',checkpoint_sha256=checkpoint['sha256'],
               completion=checkpoint['completion'],native_thread=audit['session_id'],finished=time.time())
    return row


def investigate(root):
    import structured_pair_launcher as pair
    root=Path(root).resolve();config=pair.verify(root);grant=pair.authority(root,config)
    with pair.turn_lock(root,grant['deadline']):
        state=read(root/'state.json');require(state['stop'] is None,'PAIR_RECOVERY_REQUIRED')
        # A clean coordinator interruption may be reconciled, never re-spawned.
        if state['turns'] and state['turns'][-1]['result']=='running':
            row=state['turns'][-1]
            require(row.get('phase')=='investigation','PAIR_RECOVERY_REQUIRED')
            complete(root,config,row);pair.save(root/'state.json',state)
        count=len(config['session_plan']['investigators'])
        while len(state['turns'])<count:
            pair.verify(root);grant=pair.authority(root,config)
            require(len(state['turns'])<grant['max_invocations'],'INVOCATION_LIMIT')
            slot=session_slots.expected(config,state);profile=Path(slot['profile'])
            require(sha(profile/'authorization.json')==grant['profile_authorizations'][str(profile)],
                    'PAIR_AUTHORIZATION_CHANGED')
            flow=Workflow(config['session_plan']['workflow'])
            parents=audits(config,[t['entry_id'] for t in state['turns']])
            identifier=uuid.uuid4().hex;message=root/'messages'/(identifier+'.txt')
            message.write_bytes((profile/'message.txt').read_bytes())
            pair.save(message.with_suffix('.json'),{'run_id':config['run_id'],'role':'implementer',
                'kind':'investigation','launch_sha256':sha(profile/'launch.json'),'thread_id':None,
                'message_sha256':sha(message),'authority_sha256':sha(root/'authorization.json')})
            deadline=min(grant['deadline'],time.time()+grant['turn_seconds'])
            row={'id':identifier,'role':'implementer','kind':'investigation','phase':'investigation',
                 'entry_id':slot['entry_id'],'profile':str(profile),'message':str(message),
                 'message_sha256':sha(message),'result':'running','started':time.time(),'deadline':deadline}
            state['turns'].append(row);pair.save(root/'state.json',state)
            try:
                flow.begin(slot['entry_id'],identifier,parents)
                command=[pair.sys.executable,'-B',str(pair.HERE/'structured_codex_client.py'),'run',
                    '--root',str(profile),'--message-record',str(message.with_suffix('.json'))]
                result=pair.supervise(pair.heavy_argv(root,config,command,'implementer'),pair.HERE,
                    deadline,root/'turns'/identifier,stop=lambda:(root/'halt.json').exists())
                require(result==0,'CLIENT_RUN_FAILED')
                complete(root,config,row)
            except BaseException as exc:
                row.update(result='stopped',error=str(exc),finished=time.time())
                state['stop']='recovery-required'
                raise
            finally:pair.save(root/'state.json',state)
        if len(state['turns'])==count:admit_editor(config)
