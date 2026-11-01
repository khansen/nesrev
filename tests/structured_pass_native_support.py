"""Opt-in native-client checks against loopback only; no subscription or inference.

The scripted API controls the tool calls. These tests check access and transport,
not model decisions. Every artifact is inside the test's disposable directory.
"""
import base64,hashlib,http.server,json,os,shlex,subprocess,sys,tempfile,threading,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass.service import write_json
INTERPRETER=sys.executable
SCRIPT=ROOT/'scripts/structured_pass_bridge.py'
TOOL='mcp__facts__operation'
def without_scripted_inputs(value):
    """Only the fake model's tool inputs may contain deliberate probe text."""
    if isinstance(value, dict):
        return {k:without_scripted_inputs(v) for k,v in value.items()
                if not (value.get('type')=='tool_use' and k=='input')}
    if isinstance(value, list):
        return [without_scripted_inputs(v) for v in value]
    return value

def pdf_bytes():
    objects = [b'<< /Type /Catalog /Pages 2 0 R >>',
        b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
        b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 120 120] /Contents 4 0 R >>',
        b'<< /Length 0 >>\nstream\n\nendstream']
    data = b'%PDF-1.4\n'; offsets = [0]
    for i, obj in enumerate(objects, 1):
        offsets.append(len(data)); data += f'{i} 0 obj\n'.encode()+obj+b'\nendobj\n'
    xref = len(data)
    data += b'xref\n0 5\n0000000000 65535 f \n'
    data += b''.join(f'{offset:010d} 00000 n \n'.encode() for offset in offsets[1:])
    return data + f'trailer\n<< /Size 5 /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n'.encode()

def decode(result):
    content = result.get('content',[])
    # The client flattens MCP error content to a string, but keeps successful
    # results as content blocks. Both are native-client shapes, not mock data.
    if isinstance(content,str):
        return json.loads(content)
    for part in content:
        if isinstance(part,dict) and part.get('type')=='text':
            try:
                return json.loads(part['text'])
            except json.JSONDecodeError:
                pass
    raise AssertionError('No structured bridge result: '+str(result)[:200])


def run_client(root, role, base, fixture, published_candidate=None, scenario=None):
    output = scenario.HERE/'client-integration'/role;output.mkdir(parents=True,exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix='native-client-',dir=scenario.HERE))
    workspace = scratch/'workspace';workspace.mkdir()
    config = scratch/'client-config';config.mkdir()
    outside = scratch/'outside.asm';outside.write_text('; WORKFLOW_SOURCE_SENTINEL\nRTS\n')
    markers = ('WORKFLOW_PARENT_CLAUDE_SENTINEL','WORKFLOW_PARENT_AGENTS_SENTINEL','WORKFLOW_SOURCE_SENTINEL')
    for filename,marker in zip(('CLAUDE.md','AGENTS.md'),markers):
        (scratch/filename).write_text(marker+'\n@'+str(outside)+'\n')
    png = workspace/'reference.png';pdf = workspace/'reference.pdf'
    png.write_bytes(base64.b64decode('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+a3ioAAAAASUVORK5CYII='))
    pdf.write_bytes(pdf_bytes())
    policy = scratch/'policy.json';hooklog = output/'hooks.jsonl';hooklog.write_text('')
    write_json(policy,{'reads':[str(png),str(pdf)],'log':str(hooklog)})
    settings = scratch/'settings.json'
    write_json(settings,{'permissions':{'defaultMode':'dontAsk','deny':[
        'Bash','Grep','Glob','Edit','Write','Agent','WebFetch','WebSearch']},
        'hooks':{'PreToolUse':[{'matcher':'','hooks':[{'type':'command',
            'command':shlex.join([INTERPRETER,str(SCRIPT),'--hook',str(policy)])}]}]}})
    mcp_config = scratch/'mcp.json'
    write_json(mcp_config,{'mcpServers':{'facts':{'command':INTERPRETER,
        'args':[str(SCRIPT),'--mcp',str(root),role,'corridor']}}})
    state = {'requests':0,'offered_tool_sets':[],'results':{},'steps':[],
             'payload_sentinel_checks':[],'errors':[]}

    def result(index):
        return decode(state['results'][f'toolu_workflow_{index}'])

    def call(operation, **arguments):
        return TOOL,{'operation':operation,'arguments':arguments}

    def step(index):
        start = scenario.start(role)
        if index<start:return scenario.step(index,role,result,fixture,base,published_candidate,call)
        extras=[('Read',{'file_path':str(Path(scenario.BASE)/scenario.SOURCE)}),
                ('Read',{'file_path':str(outside)}),('Bash',{'command':'git show HEAD:'+scenario.SOURCE}),
                ('Read',{'file_path':str(png)}),('Read',{'file_path':str(pdf),'pages':'1'})]
        return extras[index-start] if index-start<len(extras) else None

    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self,*args):
            pass

        def do_POST(self):
            payload = json.loads(self.rfile.read(int(self.headers['Content-Length'])))
            scanned = json.dumps(without_scripted_inputs(payload),sort_keys=True)
            state['payload_sentinel_checks'].append({'path':self.path,
                'leaks':[m for m in markers if m in scanned],
                'sha256':hashlib.sha256(scanned.encode()).hexdigest()})
            if 'count_tokens' in self.path:
                self.send_response(200);self.end_headers();self.wfile.write(b'{"input_tokens":1}');return
            if not self.path.startswith('/v1/messages'):
                self.send_error(404);return
            state['offered_tool_sets'].append([t['name'] for t in payload.get('tools',[])])
            for message in payload.get('messages',[]):
                for item in message.get('content',[]) if isinstance(message.get('content'),list) else []:
                    if item.get('type')=='tool_result':
                        state['results'][item['tool_use_id']] = item
            index = state['requests'];state['requests']+=1
            try:
                action = step(index)
            except Exception as exc:
                state['errors'].append(repr(exc));action = None
            if action:
                tool,args = action
                state['steps'].append({'index':index,'tool':tool,'arguments':args})
                block = {'type':'tool_use','id':f'toolu_workflow_{index}','name':tool,'input':args}
                reason = 'tool_use'
            else:
                block = {'type':'text','text':'LOCAL WORKFLOW COMPLETE'};reason = 'end_turn'
            message = {'id':f'msg_workflow_{index}','type':'message','role':'assistant',
                'model':payload.get('model','fixture'),'content':[block],'stop_reason':reason,
                'stop_sequence':None,'usage':{'input_tokens':0,'output_tokens':0}}
            if not payload.get('stream'):
                self.send_response(200);self.send_header('Content-Type','application/json');self.end_headers()
                self.wfile.write(json.dumps(message).encode());return
            self.send_response(200);self.send_header('Content-Type','text/event-stream');self.end_headers()
            start = dict(block,input={}) if action else dict(block,text='')
            delta = {'type':'input_json_delta','partial_json':json.dumps(block['input'])} if action else {'type':'text_delta','text':block['text']}
            events = [('message_start',{'type':'message_start','message':dict(message,content=[],stop_reason=None)}),
                ('content_block_start',{'type':'content_block_start','index':0,'content_block':start}),
                ('content_block_delta',{'type':'content_block_delta','index':0,'delta':delta}),
                ('content_block_stop',{'type':'content_block_stop','index':0}),
                ('message_delta',{'type':'message_delta','delta':{'stop_reason':reason,'stop_sequence':None},'usage':{'output_tokens':0}}),
                ('message_stop',{'type':'message_stop'})]
            for event,data in events:
                self.wfile.write(f'event: {event}\ndata: {json.dumps(data)}\n\n'.encode())
            self.wfile.flush()

    server = http.server.ThreadingHTTPServer(('127.0.0.1',0),Handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    env = {k:v for k,v in os.environ.items() if k in {'PATH','HOME','TMPDIR','SHELL','LANG','USER'}}
    env.update(PYTHONPATH=str(ROOT/'scripts'),PYTHONDONTWRITEBYTECODE='1',CLAUDE_CONFIG_DIR=str(config),ANTHROPIC_BASE_URL=f'http://127.0.0.1:{server.server_port}',
        ANTHROPIC_API_KEY='local-fixture-not-a-credential',CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC='1',
        CLAUDE_CODE_DISABLE_AUTO_MEMORY='1')
    command = [os.environ['STRUCTURED_PASS_CLIENT'],'--restricted','--tools','Read','--setting-sources','','--settings',str(settings),
        '--strict-mcp-config','--mcp-config',str(mcp_config),'--no-session-persistence',
        '--disable-slash-commands','--no-chrome','--permission-mode','dontAsk','--permission-prompts','none',
        '--include-hook-events','--output-format','stream-json','--verbose',
        '--system-prompt','Execute the local scripted workflow. Use the structured bridge.',
        '-p','Run the local workflow integration test; no external provider calls.']
    started = time.monotonic()
    try:
        completed = subprocess.run(command,cwd=workspace,env=env,capture_output=True,text=True,timeout=240)
        (output/'stdout.jsonl').write_text(completed.stdout);(output/'stderr.txt').write_text(completed.stderr)
        state['exit_code'] = completed.returncode
    finally:
        server.shutdown();server.server_close()
    events = [json.loads(line) for line in completed.stdout.splitlines()]
    init = [e for e in events if e.get('subtype')=='init']
    hooks = [e for e in events if e.get('subtype')=='hook_response']
    start = scenario.start(role) if scenario else (9 if role=='implementer' else 4)
    checks = {
        'exit_zero':completed.returncode==0,'all_steps':len(state['results'])==start+5,
        'script_succeeded':not state['errors'],
        'additional_directories_empty':len(init)==1 and init[0].get('additional_directories')==[],
        'tool_surface':bool(state['offered_tool_sets']) and all(set(t)=={'Read','DeferredToolPlaceholder',TOOL} for t in state['offered_tool_sets']),
        'whole_payload_clean':bool(state['payload_sentinel_checks']) and all(not c['leaks'] for c in state['payload_sentinel_checks']),
        'hooks_invoked':len(hooks)==start+4 and all(e.get('exit_code')==0 for e in hooks),
        'source_free_workspace':set(p.name for p in workspace.iterdir())=={'reference.png','reference.pdf'}}
    for index in (start,start+1):
        r = state['results'].get(f'toolu_workflow_{index}',{})
        checks[f'read_denied_{index}'] = bool(r.get('is_error')) and 'STRUCTURED_PASS_DENY' in json.dumps(r)
    checks['shell_absent'] = 'No such tool available' in json.dumps(state['results'].get(f'toolu_workflow_{start+2}',{}))
    for index in (start+3,start+4):
        checks[f'media_{index}'] = any(c.get('type')=='image' for c in state['results'].get(f'toolu_workflow_{index}',{}).get('content',[]) if isinstance(c,dict))
    if not state['errors'] and checks['all_steps']:
        if scenario:
            checks.update(scenario.checks(role,result,base,published_candidate))
    state.update(checks=checks,passed=all(checks.values()),seconds=time.monotonic()-started,
        state_root=str(root),workspace=str(workspace),command=command,provider_requests=0,
        client_version=subprocess.check_output([os.environ['STRUCTURED_PASS_CLIENT'],'--version'],text=True).strip(),
        hook_exit_codes=[e.get('exit_code') for e in hooks])
    write_json(output/'results.json',state)
    print(role,json.dumps(checks),flush=True)
    assert state['passed'],(checks,state['errors'],state['results'])
    return state
