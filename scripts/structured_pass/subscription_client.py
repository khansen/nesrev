"""Restricted subscription role launcher. Preparation never authorizes inference."""
import argparse
import json
import os
from pathlib import Path
import selectors
import shlex
import subprocess
import sys
import tempfile
import time
import uuid

from .launcher import Corridor,common,HERE,SCRIPTS
from .usage_budget import Budget,require

BRIDGE=HERE.parent/'structured_pass_bridge.py'
TOOL='mcp__facts__operation'


def environment(root):
    result={k:v for k,v in os.environ.items() if k in ('PATH','HOME','TMPDIR','USER','SHELL','LANG')}
    result.update(CLAUDE_CONFIG_DIR=str(root/'auth-config'),CLAUDE_CODE_DISABLE_AUTO_MEMORY='1',
                  CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC='1',PYTHONPATH=SCRIPTS,PYTHONDONTWRITEBYTECODE='1')
    return result


def command(config,role,turns,prompt,continuation):
    item=config['roles'][role]
    args=[config['client'],'--restricted','--tools','Read','--setting-sources','','--settings',item['settings'],
        '--strict-mcp-config','--mcp-config',item['mcp'],'--disable-slash-commands','--no-chrome',
        '--permission-mode','dontAsk','--permission-prompts','none','--include-hook-events',
        '--model',config['model'],'--effort',config['effort'],'--max-turns',str(turns),
        '--output-format','stream-json','--verbose','--system-prompt',Path(item['prompt']).read_text()]
    args+=['--resume' if continuation else '--session-id',item['session_id']]
    return args+['-p',prompt]


def check_initialization(event,model):
    # init omits the deferred placeholder on this client build; API requests
    # may include it. Neither representation grants another executable tool.
    require(set(event.get('tools',[])) in ({'Read',TOOL},{'Read',TOOL,'DeferredToolPlaceholder'}),'UNEXPECTED_CLIENT_TOOLS')
    require(event.get('additional_directories')==[],'UNEXPECTED_CLIENT_DIRECTORIES')
    require(event.get('model')==model and event.get('permissionMode')=='dontAsk','CLIENT_PROFILE_CHANGED')


def prepare(root,session,prompts,*,model,effort,client,interpreter,heavy_lock,media=()):
    client=Path(client).resolve();interpreter=str(Path(interpreter).resolve())
    require(all(isinstance(x,str) and x.strip() for x in (model,effort)), 'MODEL_CONFIGURATION_CHANGED')
    root=Path(root).resolve();root.mkdir(exist_ok=True)
    require(not (root/'launch.json').exists(),'LAUNCH_ALREADY_PREPARED')
    controller=Corridor(session);require(not controller.editor.state['candidates'],'EDITOR_NOT_EMPTY')
    workspace_root=Path(tempfile.mkdtemp(prefix='nesrev-live-clients-')).resolve()
    references=[]
    for path in media:
        path=Path(path).resolve();data=path.read_bytes()
        require(data.startswith(b'\x89PNG\r\n\x1a\n') or data.startswith(b'%PDF-'), 'REFERENCE_MEDIA_INVALID')
        references.append((path.name,data))
    require(len({name for name,_ in references})==len(references),'REFERENCE_MEDIA_INVALID')
    config={'schema':'subscription-corridor-v1','session':str(Path(session).resolve()),'model':model,'effort':effort,
        'client':str(client),'client_sha256':common.producer.sha(client),
        'client_version':subprocess.check_output([str(client),'--version'],text=True).strip(),
        'heavy_lock':str(Path(heavy_lock).resolve()),
        'code_sha256':{str(p):common.producer.sha(p) for p in (
            Path(__file__),HERE/'usage_budget.py',HERE/'launcher.py',HERE/'current_project.py',HERE/'application.py',BRIDGE,
            HERE/'structured_handoff.py',HERE/'verdict_bridge.py',HERE.parent/'agent_review.py')},
        'roles':{},'phase_response_cap':30}
    for role in ('implementer','reviewer'):
        folder=root/role;folder.mkdir();workspace=workspace_root/role;workspace.mkdir()
        settings=folder/'settings.json';policy=folder/'policy.json';mcp=folder/'mcp.json';prompt=folder/'prompt.md'
        prompt.write_text((Path(prompts)/(role+'.md')).read_text())
        for name,data in references:(workspace/name).write_bytes(data)
        media_hashes={str(workspace/name):common.digest(data) for name,data in references}
        common.write_json(policy,{'reads':list(media_hashes),'log':str(folder/'hooks.jsonl')})
        common.write_json(settings,{'permissions':{'defaultMode':'dontAsk','deny':['Bash','Grep','Glob','Edit','Write','Agent','WebFetch','WebSearch']},
            'hooks':{'PreToolUse':[{'matcher':'','hooks':[{'type':'command','command':shlex.join([interpreter,str(BRIDGE),'--hook',str(policy)])}]}]}})
        common.write_json(mcp,{'mcpServers':{'facts':{'command':interpreter,'args':[str(BRIDGE),'--mcp',str(Path(session).resolve()),role,'corridor'],
            'env':{'PYTHONPATH':SCRIPTS,'PYTHONDONTWRITEBYTECODE':'1'}}}})
        config['roles'][role]={'workspace':str(workspace),'settings':str(settings),'mcp':str(mcp),'prompt':str(prompt),
            'media':media_hashes,
            'session_id':str(uuid.uuid4()),'files':{str(p):common.producer.sha(p) for p in (settings,policy,mcp,prompt)}}
    common.write_json(root/'launch.json',config)
    common.write_json(root/'budget.json',{'configuration_sha256':common.producer.sha(root/'launch.json'),
        'authorized':False,'max_responses':None,'max_seconds':None,'deadline':None,'runs':[]})
    return config


def authenticate(root):
    client=json.loads((root/'launch.json').read_text())['client']
    result=subprocess.run([str(client),'auth','status','--json'],env=environment(root),capture_output=True,text=True,check=False)
    value=json.loads(result.stdout)
    require(value.get('loggedIn') is True and value.get('authMethod')=='claude.ai','ISOLATED_SUBSCRIPTION_LOGIN_REQUIRED')
    return {k:value.get(k) for k in ('loggedIn','authMethod','apiProvider','subscriptionType')}


def verify(root):
    config=json.loads((root/'launch.json').read_text())
    require(common.producer.sha(Path(config['client']))==config['client_sha256'],'CLIENT_CHANGED')
    files={**config['code_sha256']}
    for role in config['roles'].values():files.update(role['files'])
    require(all(common.producer.sha(Path(p))==h for p,h in files.items()),'LAUNCH_CONFIGURATION_CHANGED')
    for role in config['roles'].values():
        workspace=Path(role['workspace'])
        expected=role.get('media',{})
        require(workspace.is_dir() and {str(p) for p in workspace.iterdir()}==set(expected),'CLIENT_WORKSPACE_NOT_EMPTY')
        require(all(not Path(p).is_symlink() and common.producer.sha(Path(p))==h for p,h in expected.items()),'LAUNCH_CONFIGURATION_CHANGED')
    Corridor(config['session'])  # Running service readers/config must still match.
    return config


def owner_extension(root,responses,minutes,reason):
    config=verify(root)
    require(os.environ.get('NESREV_HEAVY_RUN_LOCK')==config['heavy_lock'],'SHARED_HEAVY_RUN_REQUIRED')
    # Check the inherited lock context, not just an environment string. The
    # shared runner's orphan check has already ruled out live earlier children.
    import fcntl
    try:
        fd=int(os.environ['NESREV_HEAVY_RUN_FD']);actual=os.fstat(fd);expected=Path(config['heavy_lock']).stat()
        require((actual.st_dev,actual.st_ino)==(expected.st_dev,expected.st_ino),'SHARED_HEAVY_RUN_REQUIRED')
        fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        run_id=os.environ['NESREV_HEAVY_RUN_ID']
        require(run_id.isalnum(),'SHARED_HEAVY_RUN_REQUIRED')
        lock=Path(config['heavy_lock'])
        receipt=json.loads((lock.with_name(lock.name+'.runs')/(run_id+'.json')).read_text())
        require(receipt['status']=='running' and receipt['run_id']==run_id,'SHARED_HEAVY_RUN_REQUIRED')
    except (KeyError,OSError,ValueError) as exc:
        raise ValueError('SHARED_HEAVY_RUN_REQUIRED') from exc
    require(type(minutes) is int and minutes>=0,'INVALID_BUDGET')
    return Budget(root,common.producer.sha(root/'launch.json')).extend(responses,minutes*60,reason,recover_interrupted=True)


def run_role(root,role,prompt):
    # The documented entry point is inside the shared heavy runner. It owns
    # and reaps the whole client/MCP process group, including timeout leftovers.
    config=verify(root)
    require(os.environ.get('NESREV_HEAVY_RUN_LOCK')==config['heavy_lock'],'SHARED_HEAVY_RUN_REQUIRED')
    auth=authenticate(root)
    budget=Budget(root,common.producer.sha(root/'launch.json'))
    prior=json.loads((root/'budget.json').read_text())
    continuation=any(r['role']==role for r in prior['runs'])
    reservation=budget.reserve(role,config['phase_response_cap'])
    current_budget=json.loads((root/'budget.json').read_text())
    limits=('Coordinator allowance: '+str(reservation['reserved'])+' responses for this invocation; '
            +str(current_budget['max_responses'])+' responses authorized across both roles. Wall deadline: '
            +time.strftime('%Y-%m-%d %H:%M:%S UTC',time.gmtime(reservation['deadline']))
            +'. Batch independent reads; keep mutations sequential. Only the owner can extend these limits.\n\n')
    folder=root/'runs'/reservation['id'];folder.mkdir(parents=True)
    common.write_json(folder/'auth.json',auth)
    events=[];timed_out=False;failure=None;accounting=None
    try:
        with (folder/'stderr.log').open('wb') as stderr,(folder/'stdout.jsonl').open('w') as stdout:
            process=subprocess.Popen(command(config,role,reservation['reserved'],limits+prompt,continuation),
                cwd=config['roles'][role]['workspace'],env=environment(root),stdout=subprocess.PIPE,stderr=stderr)
            # Nonblocking byte reads keep the wall limit effective even when
            # the client has not emitted a complete JSON line.
            selector=selectors.DefaultSelector();selector.register(process.stdout,selectors.EVENT_READ)
            pending=b'';initialized=False
            while selector.get_map():
                if time.time()>=reservation['deadline']:timed_out=True;break
                for key,_ in selector.select(.25):
                    chunk=os.read(key.fileobj.fileno(),65536)
                    if not chunk:selector.unregister(key.fileobj);continue
                    pending+=chunk
                    while b'\n' in pending:
                        line,pending=pending.split(b'\n',1)
                        if not line:continue
                        event=json.loads(line);events.append(event);stdout.write(line.decode()+'\n');stdout.flush()
                        if event.get('subtype')=='init':
                            initialized=True
                            check_initialization(event,config['model'])
                        elif event.get('type')=='assistant':
                            require(initialized,'MISSING_CLIENT_INITIALIZATION')
                            budget.observe(reservation['id'],event)
            selector.close()
            if timed_out:process.terminate()
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:process.kill();process.wait()
            require(initialized,'MISSING_CLIENT_INITIALIZATION')
    except BaseException as exc:
        failure=type(exc).__name__+': '+str(exc)
        if 'process' in locals() and process.poll() is None:
            process.terminate()
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:process.kill();process.wait()
        budget.interrupt(reservation['id'])
    else:accounting=budget.finish(reservation['id'],events,timeout=timed_out)
    final=next((e for e in reversed(events) if e.get('type')=='result'),None)
    error=('CLIENT_RUN_FAILED' if failure is not None else 'RUN_TIME_LIMIT' if timed_out
           else 'CLIENT_RUN_FAILED' if process.returncode!=0
           else 'CLIENT_STREAM_INCOMPLETE' if accounting['status']!='finished'
           else 'CLIENT_RUN_FAILED' if final.get('subtype')!='success' or final.get('is_error') is not False
           else None)
    common.write_json(folder/'run.json',{'role':role,'reservation':reservation,'failure':failure,'timeout':timed_out,
        'exit_code':process.returncode if 'process' in locals() else None,'error':error,'accounting':accounting})
    require(error is None,error)
    return {'run_id':reservation['id'],'role':role,'exit_code':process.returncode,'result':final.get('result')}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True)
    sub=parser.add_subparsers(dest='action',required=True)
    prep=sub.add_parser('prepare');prep.add_argument('--session',type=Path,required=True);prep.add_argument('--prompts',type=Path,required=True)
    for name in ('model','effort','client','interpreter','heavy-lock'):
        prep.add_argument('--'+name,required=True)
    prep.add_argument('--media',type=Path,action='append',default=[],help='Operator-selected PNG or PDF; copied and pinned')
    sub.add_parser('check')
    approve=sub.add_parser('authorize');approve.add_argument('--responses',type=int,required=True);approve.add_argument('--minutes',type=int,required=True)
    extend=sub.add_parser('extend');extend.add_argument('--responses',type=int,required=True)
    extend.add_argument('--minutes',type=int,required=True);extend.add_argument('--reason',required=True)
    run=sub.add_parser('run');run.add_argument('role',choices=('implementer','reviewer'));run.add_argument('--message',required=True)
    args=parser.parse_args();root=args.root.resolve()
    if args.action=='prepare':answer=prepare(root,args.session,args.prompts,model=args.model,effort=args.effort,client=args.client,interpreter=args.interpreter,heavy_lock=args.heavy_lock,media=args.media);answer={'prepared':True,'model':answer['model'],'effort':answer['effort'],'authorized':False}
    elif args.action=='check':verify(root);answer={'profile_valid':True,'auth':authenticate(root)}
    elif args.action=='authorize':
        verify(root);require(args.responses>0 and args.minutes>0,'INVALID_BUDGET')
        budget=Budget(root,common.producer.sha(root/'launch.json'))
        with budget.transaction() as state:
            require(not state['runs'],'BUDGET_ALREADY_STARTED')
            state.update(authorized=True,max_responses=args.responses,max_seconds=args.minutes*60,owner_approved_at=time.time())
        answer={'authorized':True,'responses':args.responses,'minutes':args.minutes}
    elif args.action=='extend':answer=owner_extension(root,args.responses,args.minutes,args.reason)
    else:answer=run_role(root,args.role,args.message)
    print(json.dumps(answer))

if __name__=='__main__':main()
