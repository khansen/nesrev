"""One-use client admissions under the pair's persistent, finite session plan.

The coordinator saves a running slot before spawning its adapter. Each adapter
claims that slot once before authentication or inference. An interrupted claim
consumes the slot; it never becomes an automatic replacement invocation.
"""
import json
import os
from pathlib import Path
import time

from .producer import require, sha


def read(path):
    return json.loads(Path(path).read_bytes())


def entries(config):
    plan=config['session_plan']
    return [dict(row,role='implementer',phase='investigation') for row in plan['investigators']]+[
        {'role':role,'phase':'editing','profile':config['profiles'][role]}
        for role in plan['editing_roles']]


def expected(config, state):
    slots=entries(config)
    require(len(state['turns'])<len(slots),'INVOCATION_LIMIT')
    require(all(row['result'] in ('checkpoint','handoff') for row in state['turns']),
            'PAIR_RECOVERY_REQUIRED')
    return slots[len(state['turns'])]


def prior_runs(root, row, *, finished=False):
    profile=Path(row['profile']);state=read(root/'state.json')
    prior=[r for r in state['turns'][:-1] if r['profile']==str(profile)]
    native=read(profile/('state.json' if row['role']=='implementer' else 'budget.json'))
    require(not native.get('halted') and len(native['runs'])==len(prior)+int(finished) and
            all(r['status']=='finished' and not r.get('usage_uncertain') for r in native['runs']),
            'PAIR_RECOVERY_REQUIRED')
    for index,previous in enumerate(prior):
        require(previous.get('client_run_id')==native['runs'][index]['id'],'PAIR_RECOVERY_REQUIRED')
    if row['role']=='implementer':
        require((not prior and (finished or native['thread_id'] is None)) or
                (prior and native['thread_id']==prior[-1]['native_thread']), 'PAIR_RECOVERY_REQUIRED')
        if finished:require(bool(native['thread_id']),'PAIR_RECOVERY_REQUIRED')
    return native


def finish(root, row):
    root=Path(root);receipt=read(root/'claims'/(row['id']+'.json'))
    require(receipt['slot_id']==row['id'] and receipt['profile']==row['profile'] and
            receipt['message_sha256']==row['message_sha256'] and
            receipt['grant_sha256']==sha(root/'authorization.json'),'PAIR_RECOVERY_REQUIRED')
    native=prior_runs(root,row,finished=True)
    row['client_run_id']=native['runs'][-1]['id']
    if row['role']=='implementer':row['native_thread']=native['thread_id']


def claim(profile, config, message_record, message, role):
    """Called by both pinned adapters; bypassing the pair cannot mint a slot."""
    if config.get('pair_root') is None:return None
    root=Path(config['pair_root']);profile=Path(profile).resolve()
    require(message_record is not None,'PAIR_MESSAGE_CHANGED')
    record_path=Path(message_record).resolve(strict=True)
    require(record_path.parent==root/'messages' and not Path(message_record).is_symlink(),
            'PAIR_MESSAGE_CHANGED')
    launch=read(root/'launch.json');grant=read(root/'authorization.json')
    state=read(root/'state.json');record=read(record_path)
    require(grant.get('authorized') is True and grant.get('owner_message') and
            grant['launch_sha256']==sha(root/'launch.json') and
            record['authority_sha256']==sha(root/'authorization.json'), 'PAIR_AUTHORIZATION_CHANGED')
    require(not (root/'halt.json').exists() and state['stop'] is None,'PAIR_RECOVERY_REQUIRED')
    if role=='implementer':
        require(grant['profile_authorizations'].get(str(profile))==sha(profile/'authorization.json'),
                'PAIR_AUTHORIZATION_CHANGED')
    else:
        budget=read(profile/'budget.json')
        require(budget['deadline']==grant['deadline'] and budget['max_responses']==grant['claude_responses'],
                'PAIR_AUTHORIZATION_CHANGED')
    require(0<len(state['turns'])<=grant['max_invocations'],'INVOCATION_LIMIT')
    row=state['turns'][-1];slot=expected(launch,{'turns':state['turns'][:-1]})
    require(row['result']=='running' and row['role']==role==slot['role'] and
            row['phase']==slot['phase'] and row.get('entry_id')==slot.get('entry_id') and
            row['profile']==str(profile)==slot['profile'] and
            row['message']==str(record_path.with_suffix('.txt')) and
            record['launch_sha256']==sha(profile/'launch.json') and
            launch['files'][str(profile/'launch.json')]==record['launch_sha256'] and
            record['run_id']==launch['run_id'], 'PAIR_MESSAGE_CHANGED')
    require(row['message_sha256']==record['message_sha256']==
            __import__('hashlib').sha256(message).hexdigest(),'PAIR_MESSAGE_CHANGED')
    require(time.time()<row['deadline']<=grant['deadline'],'RUN_TIME_LIMIT')
    prior_runs(root,row)
    claims=root/'claims';claims.mkdir(exist_ok=True)
    receipt={'slot_id':row['id'],'slot_index':len(state['turns'])-1,'profile':str(profile),
             'phase':slot['phase'],'role':role,'deadline':row['deadline'],
             'grant_sha256':sha(root/'authorization.json'),'message_sha256':record['message_sha256'],
             'pid':os.getpid(),'claimed_at':time.time()}
    path=claims/(row['id']+'.json')
    # immutable_file permits an identical existing artifact. A slot never does.
    require(not path.exists(),'PAIR_ALREADY_STARTED')
    try:
        with path.open('xb') as stream:
            stream.write((json.dumps(receipt,sort_keys=True)+'\n').encode())
            stream.flush();os.fsync(stream.fileno())
    except FileExistsError:raise ValueError('PAIR_ALREADY_STARTED') from None
    return receipt
