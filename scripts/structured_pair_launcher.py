"""Supervise the existing Codex/Claude adapters and session-local watch protocol.

Preparation is offline. A separate owner record authorizes a bounded window;
neither a watcher nor a successful client exit authorizes a replacement turn.
"""
import argparse
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time
import uuid

import agent_review as review
import structured_codex_client as codex
import structured_client_processes as processes
from structured_client_workspace import require_source_free
from structured_pass import subscription_client as claude
from structured_pass.launcher import Corridor
from structured_pass.usage_budget import Budget, require
from structured_pass.bridge import tool_listing

HERE = Path(__file__).resolve().parent
ROLES = ('implementer', 'reviewer')
save = codex.save
sha = codex.sha


def declarations():
    return {name:codex.hashlib.sha256(json.dumps(tool_listing(role,profile),sort_keys=True).encode()).hexdigest()
            for name,role,profile in (('implementer','implementer','corridor'),
                ('reviewer','reviewer','corridor'),('retained','reviewer','retained'))}


def check_inputs(controller, ci, cr, task):
    if controller.checked_editor().get('declared_inputs_sha256') is None:return
    left=read(ci['input_assembly']);right=read(cr['roles']['reviewer']['input_assembly'])
    require(left['role']=='implementer' and right['role']=='reviewer', 'PAIR_INPUTS_CHANGED')
    require(left['task']==right['task']==task.decode(), 'PAIR_TASK_CHANGED')
    require(all(left[key]==right[key] for key in ('items','manifest_sha256','pass_id','objective','historical_label')),
            'PAIR_INPUTS_CHANGED')


def read(path):
    return json.loads(Path(path).read_bytes())


def prepare(root, session, implementer, reviewer, task, application_repo=None):
    root = Path(root).resolve()
    require(not root.exists(), 'PAIR_ALREADY_PREPARED')
    require_source_free(root)
    session, implementer, reviewer, task = (Path(p).resolve(strict=True) for p in (session, implementer, reviewer, task))
    ci, cr = codex.verify(implementer), claude.verify(reviewer)
    controller = Corridor(session)
    require(ci['session'] == cr['session'] == str(session) and ci['role'] == 'implementer', 'PAIR_PROFILE_MISMATCH')
    require(ci['heavy_lock'] == cr['heavy_lock'], 'PAIR_PROFILE_MISMATCH')
    require((implementer/'message.txt').read_bytes() == task.read_bytes(), 'PAIR_TASK_CHANGED')
    check_inputs(controller,ci,cr,task.read_bytes())
    require(not read(implementer/'state.json')['runs'] and not read(reviewer/'budget.json')['runs'], 'PAIR_PROFILES_NOT_FRESH')
    require(platform.system() == 'Darwin' and platform.machine() == 'arm64', 'PAIR_PLATFORM_UNADMITTED')
    root.mkdir(parents=True)
    (root/'messages').mkdir()
    (root/'task.txt').write_bytes(task.read_bytes())
    notify = root/'notify'
    notify.write_text('#!/bin/sh\nexec ' + shlex.join([sys.executable, '-B', str(Path(__file__).resolve()),
        '--root', str(root), 'notify']) + ' "$@"\n')
    notify.chmod(0o700)
    files = [Path(__file__).resolve(), HERE/'structured_client_workspace.py', HERE/'structured_client_processes.py',
             HERE/'agent_review.py', HERE/'agent_review_tmux.py', HERE/'structured_pass_heavy_run.py',
             session/'session.json', implementer/'launch.json', reviewer/'launch.json', root/'task.txt', notify]
    config = {'schema': 'structured-pair-v1', 'session': str(session),
        'run_id': controller.config['run_id'], 'handoff': str(session/'handoff'),
        'profiles': {'implementer': str(implementer), 'reviewer': str(reviewer)},
        'clients': {'implementer': 'codex', 'reviewer': 'claude'},
        'selections': {'implementer': {k: ci[k] for k in ('model','effort')},
                       'reviewer': {k: cr[k] for k in ('model','effort')}},
        'heavy_lock': ci['heavy_lock'], 'poll_seconds': 2,
        'application_repo': str(Path(application_repo).resolve(strict=True)) if application_repo is not None else None,
        'platform': [platform.system(), platform.machine()],
        'declarations': declarations(),
        'files': {str(p): sha(p) for p in files}}
    save(root/'launch.json', config)
    save(root/'state.json', {'turns': [], 'stop': None})
    return config


def verify(root):
    root = Path(root).resolve()
    config = read(root/'launch.json')
    require(config.get('schema') == 'structured-pair-v1' and
            config.get('clients') == {'implementer':'codex','reviewer':'claude'}, 'PAIR_PROFILE_MISMATCH')
    require(config['platform'] == [platform.system(), platform.machine()] == ['Darwin','arm64'], 'PAIR_PLATFORM_UNADMITTED')
    require(all(sha(p) == h for p,h in config['files'].items()), 'PAIR_CONFIGURATION_CHANGED')
    require(config['declarations'] == declarations(), 'PAIR_DECLARATIONS_CHANGED')
    require_source_free(root)
    ci, cr = codex.verify(Path(config['profiles']['implementer'])), claude.verify(Path(config['profiles']['reviewer']))
    require(ci['session'] == cr['session'] == config['session'] and ci['heavy_lock'] == cr['heavy_lock'] == config['heavy_lock'],
            'PAIR_PROFILE_MISMATCH')
    controller = Corridor(config['session'])
    check_inputs(controller,ci,cr,(root/'task.txt').read_bytes())
    require(controller.config['run_id'] == config['run_id'] and config['handoff'] == str(controller.root/'handoff'), 'PAIR_RUN_CHANGED')
    return config


def authority(root, config):
    path = root/'authorization.json'
    require(path.is_file(), 'INFERENCE_NOT_AUTHORIZED')
    grant = read(path)
    require(grant.get('authorized') is True and grant.get('owner_message'), 'INFERENCE_NOT_AUTHORIZED')
    require(grant.get('launch_sha256') == sha(root/'launch.json'), 'PAIR_AUTHORIZATION_CHANGED')
    require(not (root/'halt.json').exists(), 'PAIR_RECOVERY_REQUIRED')
    require(time.time() < grant['deadline'], 'RUN_TIME_LIMIT')
    return grant


@contextmanager
def turn_lock(root, deadline):
    with (root/'turn.lock').open('a+b') as lock:
        while True:
            require(time.time() < deadline, 'RUN_TIME_LIMIT')
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                time.sleep(min(.1, max(0, deadline-time.time())))
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def authorize(root, *, owner_message, deadline, invocations, responses, turn_seconds, purpose, evidence=None, apply=False):
    """Explicit operator action, never called by preparation or a watcher."""
    root = Path(root).resolve(); config = verify(root)
    require(owner_message.strip() and time.time() < deadline and type(invocations) is int and invocations > 0
            and type(responses) is int and responses > 0 and turn_seconds > 0, 'INVALID_BUDGET')
    require(purpose in ('access_preflight','pilot_takeover'), 'CODEX_AUTHORIZATION_PURPOSE')
    require(type(apply) is bool and (not apply or (purpose=='pilot_takeover' and config['application_repo'] is not None)),
            'PAIR_APPLICATION_NOT_AUTHORIZED')
    with turn_lock(root, deadline):
        require(not (root/'authorization.json').exists(), 'PAIR_ALREADY_AUTHORIZED')
        require(not read(root/'state.json')['turns'], 'PAIR_ALREADY_STARTED')
        ci = Path(config['profiles']['implementer']); cr = Path(config['profiles']['reviewer'])
        require(not read(ci/'state.json')['runs'] and not read(cr/'budget.json')['runs'], 'PAIR_PROFILES_NOT_FRESH')
        evidence = evidence or {}
        if purpose == 'pilot_takeover':
            for name in ('access_preflight','transition_review'):
                record = evidence.get(name,{})
                require(record.get('path') and sha(record['path']) == record.get('sha256'), 'CODEX_ADMISSION_EVIDENCE_REQUIRED')
        grant = {'authorized': True, 'owner_message': owner_message, 'deadline': deadline,
                 'max_invocations': invocations, 'claude_responses': responses, 'turn_seconds': turn_seconds,
                 'purpose': purpose, 'apply':apply, 'launch_sha256': sha(root/'launch.json'), 'authorized_at': time.time()}
        save(ci/'authorization.json', {**evidence, 'authorized': True, 'owner_message': owner_message,
            'launch_sha256': sha(ci/'launch.json'), 'purpose': purpose,
            'token_response_caps': 'none_usage_reporting_only', 'deadline': deadline,
            'message_directory': str(root/'messages'), 'run_id': config['run_id']})
        with Budget(cr,sha(cr/'launch.json')).transaction() as budget:
            require(not budget['runs'], 'PAIR_PROFILES_NOT_FRESH')
            budget.update(authorized=True, max_responses=responses, max_seconds=deadline-time.time(), deadline=deadline)
        grant['adapter_authorization_sha256'] = sha(ci/'authorization.json')
        save(root/'authorization.json', grant)
    return grant


def service_status(config, role, deadline=None, events=None):
    while True:
        try:return Corridor(config['session']).status(role)
        except ValueError as exc:
            if deadline is None or str(exc) not in ('REVIEW_STATE_BUSY','VALIDATION_IN_PROGRESS','REVIEW_RESTORE_IN_PROGRESS'):
                raise
            if events is not None:events.append({'code':str(exc),'at':time.time()})
            require(time.time()<deadline,'RUN_TIME_LIMIT')
            time.sleep(min(2,max(0,deadline-time.time())))


def identity(status, role):
    handoff = status['handoff']
    if handoff is None:
        return None
    return [handoff['run_id'], handoff['status'], handoff['round'], handoff['coverage']['pass_head'], role]


def classify(before, after, role, closed):
    if closed:
        return 'closed'
    handoff = after['handoff']
    actor = review.next_actor_for(handoff) if handoff else None
    if actor is not None and actor != role and identity(before,role) != identity(after,role):
        return 'handoff'
    return 'unfinished'


def supervise(argv, cwd, deadline, folder, *, stop=None):
    """Arm signal/deadline supervision before spawn; retain and reconcile descendants."""
    folder.mkdir(parents=True, exist_ok=True)
    row = {'argv': argv, 'deadline': deadline, 'guard_armed_at': time.time()}
    persist = lambda: save(folder/'process.json',row)
    process = None
    offsets = {'stdout':0,'stderr':0}
    def display():
        for name in offsets:
            path=folder/(name+'.log')
            if not path.exists():continue
            with path.open('rb') as stream:
                stream.seek(offsets[name]);chunk=stream.read(65536);offsets[name]=stream.tell()
            if chunk:print(chunk.decode('utf-8','replace'),end='',flush=True)
    persist()
    with codex.termination_handlers() as signals:
        try:
            require(time.time() < deadline, 'RUN_TIME_LIMIT')
            with (folder/'stdout.log').open('wb') as output, (folder/'stderr.log').open('wb') as error:
                with codex.defer_termination(signals):
                    process = subprocess.Popen(argv, cwd=cwd, stdout=output, stderr=error, start_new_session=True)
                    row.update(client_pgid=process.pid, launched_at=time.time())
                    persist()
                    processes.observe(row,None); persist()
                while process.poll() is None:
                    display()
                    if processes.observe(row,None)[0]:persist()
                    require(time.time() < deadline, 'RUN_TIME_LIMIT')
                    if stop is not None and stop():
                        raise ValueError('PAIR_STOPPED')
                    time.sleep(.1)
                row['exit_code'] = process.returncode
                return process.returncode
        except BaseException as exc:
            row['error'] = str(exc)
            raise
        finally:
            signals['cleaning']=True
            try:
                processes.stop_tree(process,row,None,persist)
                row['processes_reconciled'] = True
            except BaseException as exc:
                row['cleanup_error'] = str(exc)
                raise
            finally:
                display()
                row['finished'] = time.time();persist()


def adapter_argv(root, config, role, message, deadline):
    profile = Path(config['profiles'][role])
    if role == 'implementer':
        command = [sys.executable,'-B',str(HERE/'structured_codex_client.py'),'run','--root',str(profile),
                   '--message-record',str(message.with_suffix('.json'))]
    else:
        command = [sys.executable,'-B','-m','structured_pass.subscription_client','--root',str(profile),
                   'run','reviewer','--message-file',str(message),'--deadline',str(deadline)]
    return heavy_argv(root,config,command,role)


def heavy_argv(root,config,command,role='coordinator'):
    return [sys.executable,'-B',str(HERE/'structured_pass_heavy_run.py'),'--lock',config['heavy_lock'],
            '--agent',role,'--session',config['run_id'],'--estimate-mib','1024','--reserve-mib','2048',
            '--volume',str(root),'--',*command]


def apply_closed(root):
    root=Path(root).resolve();config=verify(root);grant=authority(root,config)
    require(grant.get('apply') is True and config['application_repo'] is not None,'PAIR_APPLICATION_NOT_AUTHORIZED')
    with turn_lock(root,grant['deadline']):
        state=read(root/'state.json');require(state['stop']=='closed','PAIR_NOT_CLOSED')
        Corridor(config['session']).closeout()
        command=[sys.executable,'-B','-m','structured_pass.application','--session',config['session'],
                 '--repo',config['application_repo'],'--commit']
        code=supervise(heavy_argv(root,config,command),HERE,grant['deadline'],root/'application'/uuid.uuid4().hex)
        require(code==0,'PAIR_APPLICATION_FAILED')
        result=read(Path(config['session'])/'application.json')
        require(result['status']=='committed','PAIR_APPLICATION_FAILED')
        state['application']=result;save(root/'state.json',state)
        return result


def deliver(root, role, path, *, kind='notify', notified_status=None):
    root = Path(root).resolve(); config = verify(root); grant = authority(root,config)
    require(role in ROLES and kind in ('initial','notify','owner'), 'PAIR_TURN_INVALID')
    with turn_lock(root,grant['deadline']):
        config = verify(root); grant = authority(root,config); state = read(root/'state.json')
        require(state['stop'] is None and not any(t['result']=='running' for t in state['turns']), 'PAIR_RECOVERY_REQUIRED')
        require(len(state['turns']) < grant['max_invocations'], 'INVOCATION_LIMIT')
        busy=[]
        before = service_status(config,role,grant['deadline'],busy)
        data = Path(path).read_bytes()
        require(bool(data.strip()), 'PAIR_MESSAGE_EMPTY')
        if kind == 'notify':
            saved = review.read_state(Path(config['handoff']))
            require(saved['run_id'] == config['run_id'] and saved['status'] == notified_status
                    and review.next_actor_for(saved) == role, 'PAIR_STALE_NOTIFICATION')
            source = Path(config['handoff'])/saved['prompts'][role]
            require(Path(path).resolve() == source.resolve() and data == source.read_bytes(), 'PAIR_MESSAGE_CHANGED')
            token = review.notify_token(saved,role)
            require(not any(t.get('notification')==token for t in state['turns']), 'PAIR_DUPLICATE_NOTIFICATION')
        else:
            token = None
            if kind == 'initial':
                require(role == 'implementer' and not state['turns'] and before['handoff'] is None
                        and data == (root/'task.txt').read_bytes(), 'PAIR_ALREADY_STARTED')
        identifier = uuid.uuid4().hex
        message = root/'messages'/(identifier+'.txt');message.write_bytes(data)
        profile = Path(config['profiles'][role])
        thread = read(profile/'state.json')['thread_id'] if role=='implementer' else None
        save(message.with_suffix('.json'), {'run_id':config['run_id'],'role':role,'kind':kind,
            'launch_sha256':sha(profile/'launch.json'),'thread_id':thread,'message_sha256':sha(message),
            'notification':token,'authority_sha256':sha(root/'authorization.json')})
        row = {'id':identifier,'role':role,'kind':kind,'message':str(message),'message_sha256':sha(message),
               'notification':token,'before':before,'result':'running','started':time.time(),'coordinator_busy':busy}
        state['turns'].append(row); save(root/'state.json',state)
        deadline = min(grant['deadline'],time.time()+grant['turn_seconds'])
        try:
            require(sha(Path(config['profiles']['implementer'])/'authorization.json') == grant['adapter_authorization_sha256'],
                    'PAIR_AUTHORIZATION_CHANGED')
            budget = read(Path(config['profiles']['reviewer'])/'budget.json')
            require(budget['deadline']==grant['deadline'] and budget['max_responses']==grant['claude_responses'], 'PAIR_AUTHORIZATION_CHANGED')
            code = supervise(adapter_argv(root,config,role,message,deadline),HERE,deadline,root/'turns'/identifier,
                             stop=lambda:(root/'halt.json').exists())
            row['exit_code'] = code
            require(code == 0, 'CLIENT_RUN_FAILED')
            after = service_status(config,role,grant['deadline'],busy);row['after'] = after
            closed_path = Path(config['session'])/'closed.json'
            closed = False
            if closed_path.exists():
                # The existing controller rechecks approval, coverage and closeout evidence.
                Corridor(config['session']).closeout(); closed = True
            row['result'] = classify(before,after,role,closed)
            if row['result'] != 'handoff':state['stop'] = row['result']
        except BaseException as exc:
            row.update(result='stopped',error=str(exc))
            state['stop'] = 'budget' if str(exc) in ('RUN_TIME_LIMIT','INVOCATION_LIMIT') else 'recovery-required'
            raise
        finally:
            row['finished'] = time.time(); save(root/'state.json',state)
            print(json.dumps(row),flush=True)
        return row


def continue_turn(root, role, message):
    """Owner steering after an ordinary unfinished return; never repairs uncertain runs."""
    root=Path(root).resolve();config=verify(root);grant=authority(root,config)
    with turn_lock(root,grant['deadline']):
        state=read(root/'state.json')
        require(state['stop']=='unfinished' and state['turns'][-1]['role']==role, 'PAIR_RECOVERY_REQUIRED')
        state['stop']=None;save(root/'state.json',state)
    return deliver(root,role,message,kind='owner')


def extend(root, *, owner_message, deadline, invocations=0, responses=0):
    """Extend an idle allowance without clearing failed/uncertain evidence."""
    root=Path(root).resolve();config=verify(root)
    require(owner_message.strip() and deadline>time.time() and type(invocations) is int and invocations>=0
            and type(responses) is int and responses>=0,'INVALID_BUDGET')
    with turn_lock(root,deadline):
        old=read(root/'authorization.json');state=read(root/'state.json')
        require(old['launch_sha256']==sha(root/'launch.json') and deadline>old['deadline'],'PAIR_AUTHORIZATION_CHANGED')
        require(not (root/'halt.json').exists() and state['stop'] in (None,'unfinished','budget')
                and not any(t['result'] in ('running','stopped') for t in state['turns']),'PAIR_RECOVERY_REQUIRED')
        for row in state['turns']:
            processes.require_quiescent({'runs':[read(root/'turns'/row['id']/'process.json')]})
        ci=Path(config['profiles']['implementer']);cr=Path(config['profiles']['reviewer'])
        require(not read(ci/'state.json').get('halted') and not read(cr/'budget.json').get('halted'),'PAIR_RECOVERY_REQUIRED')
        history=root/'extensions';history.mkdir(exist_ok=True)
        save(history/(sha(root/'authorization.json')+'.json'),old)
        value=read(ci/'authorization.json');value['deadline']=deadline;save(ci/'authorization.json',value)
        with Budget(cr,sha(cr/'launch.json')).transaction() as budget:
            require(not any(r['status']=='running' for r in budget['runs']),'PAIR_RECOVERY_REQUIRED')
            budget['deadline']=deadline;budget['max_responses']+=responses
        grant={**old,'deadline':deadline,'max_invocations':old['max_invocations']+invocations,
            'claude_responses':old['claude_responses']+responses,'previous_authorization_sha256':sha(root/'authorization.json'),
            'extension_owner_message':owner_message,'extended_at':time.time(),
            'adapter_authorization_sha256':sha(ci/'authorization.json')}
        save(root/'authorization.json',grant)
        return grant


def worker(root, role):
    root=Path(root).resolve();config=verify(root);grant=authority(root,config)
    if role=='implementer' and not read(root/'state.json')['turns']:
        deliver(root,role,root/'task.txt',kind='initial')
    if read(root/'state.json')['stop'] is not None:return 0
    argv=[sys.executable,'-B',str(HERE/'agent_review.py'),'--repo',config['handoff'],
          '--expected-run-id',config['run_id'],'watch','--role',role,'--worker-id','structured-pair',
          '--interval',str(config['poll_seconds']),'--timeout',str(max(.001,grant['deadline']-time.time())),
          '--notify',str(root/'notify')]
    try:
        result=supervise(argv,Path(config['session']),grant['deadline'],root/'watchers'/role/uuid.uuid4().hex,
                         stop=lambda:read(root/'state.json')['stop'] is not None or (root/'halt.json').exists())
        if result not in (0,4):
            save(root/'halt.json',{'role':role,'error':'WATCH_FAILED','exit_code':result,'at':time.time()})
        return result
    except ValueError as exc:
        if str(exc) not in ('PAIR_STOPPED','RUN_TIME_LIMIT'):raise
        print(str(exc),flush=True);return 4 if str(exc)=='RUN_TIME_LIMIT' else 0


def resume_watchers(root, tmux):
    root=Path(root).resolve();config=verify(root);authority(root,config)
    state=read(root/'state.json')
    require(state['stop'] is None and state['turns'] and state['turns'][-1]['result']=='handoff', 'PAIR_RECOVERY_REQUIRED')
    panes=read(root/'tmux.json')['panes']
    for role,pane in panes.items():
        result=tmux('display-message','-p','-t',pane,'#{pane_dead}')
        require(result.stdout.strip()=='1', 'PAIR_WORKER_ALREADY_RUNNING')
    for role,pane in panes.items():
        authority(root,config)
        command=shlex.join([sys.executable,'-B',str(Path(__file__).resolve()),'--root',str(root),'worker',role])
        tmux('respawn-pane','-k','-t',pane,command)


def tmux_launch(args, tmux, connect):
    root=args.prepared.resolve();config=verify(root)
    if args.check:
        print(json.dumps({'prepared':True,'config':config,'inference_admitted':False}));return 0
    authority(root,config)
    require(not read(root/'state.json')['turns'], 'PAIR_ALREADY_STARTED')
    require(not (root/'tmux.json').exists(), 'PAIR_TMUX_ALREADY_CREATED')
    require(review.re.fullmatch(r'[A-Za-z0-9_-]+',args.session), 'PAIR_SESSION_NAME')
    session=None
    try:
        # Start placeholders; workers are admitted only after both panes and the record exist.
        result=tmux('new-session','-d','-P','-F','#{session_id}\t#{pane_id}', '-s',args.session,'-n','structured','sleep 3600')
        session, first=result.stdout.strip().split('\t')
        second=tmux('split-window','-h','-P','-F','#{pane_id}','-t',first,'sleep 3600').stdout.strip()
        panes=dict(zip(ROLES,(first,second)))
        tmux('set-option','-t',session,'remain-on-exit','on')
        save(root/'tmux.json',{'session':session,'panes':panes,'root':str(root)})
        for role,pane in panes.items():
            authority(root,config)  # Includes time spent creating tmux.
            command=shlex.join([sys.executable,'-B',str(Path(__file__).resolve()),'--root',str(root),'worker',role])
            tmux('respawn-pane','-k','-t',pane,command)
        return connect(session,args.session,args.no_attach)
    except BaseException:
        if session is not None:tmux('kill-session','-t',session,check=False)
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    sub=parser.add_subparsers(dest='action',required=True)
    prep=sub.add_parser('prepare')
    for name in ('session','implementer','reviewer','task'):prep.add_argument('--'+name,type=Path,required=True)
    prep.add_argument('--application-repo',type=Path)
    sub.add_parser('check')
    sub.add_parser('status')
    sub.add_parser('resume-watchers')
    sub.add_parser('apply')
    auth=sub.add_parser('authorize');auth.add_argument('--record',type=Path,required=True)
    extra=sub.add_parser('extend');extra.add_argument('--record',type=Path,required=True)
    work=sub.add_parser('worker');work.add_argument('role',choices=ROLES)
    note=sub.add_parser('notify');note.add_argument('role',choices=ROLES);note.add_argument('status');note.add_argument('message',type=Path)
    cont=sub.add_parser('continue');cont.add_argument('role',choices=ROLES);cont.add_argument('--message-file',type=Path,required=True)
    args=parser.parse_args()
    if args.action=='prepare':answer=prepare(args.root,args.session,args.implementer,args.reviewer,args.task,args.application_repo)
    elif args.action=='check':verify(args.root);answer={'prepared':True,'inference_admitted':False}
    elif args.action=='authorize':answer=authorize(args.root,**read(args.record))
    elif args.action=='extend':answer=extend(args.root,**read(args.record))
    elif args.action=='apply':answer=apply_closed(args.root)
    elif args.action=='status':
        config=verify(args.root)
        answer={'service':service_status(config,'implementer'),'launcher':read(args.root/'state.json'),
                'halt':read(args.root/'halt.json') if (args.root/'halt.json').exists() else None}
    elif args.action=='resume-watchers':
        from agent_review_tmux import tmux
        resume_watchers(args.root,tmux);answer={'watchers_resumed':True}
    elif args.action=='worker':return worker(args.root,args.role)
    elif args.action=='continue':answer=continue_turn(args.root,args.role,args.message_file)
    else:answer=deliver(args.root,args.role,args.message,notified_status=args.status)
    print(json.dumps(answer));return 0


if __name__=='__main__':
    try:raise SystemExit(main())
    except (ValueError,OSError,KeyError) as exc:
        print('error: '+str(exc),file=sys.stderr);raise SystemExit(2)
