"""Prepare and supervise a restricted Codex client for an existing corridor.

This adapter lives outside structured_pass so adding a client does not change
the source-reader identity. Preparation grants no inference permission. Usage
is reported in Codex's native units, never converted to Claude responses.
"""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import selectors
import signal
import shlex
import subprocess
import sys
import time
import uuid
import structured_client_processes as process_tree


TOOL = 'mcp__facts__operation'
FORBIDDEN_TOOLS = frozenset('functions__' + name for name in
    ('exec', 'wait', 'request_user_input', 'request_user_input_async'))
OFFERED_TOOLS = FORBIDDEN_TOOLS | {TOOL}
DECLARATION_SHA256 = '8df1bc0a8356e4d28df87aba94957298f5113bc1264763d99b70174bb2e1d6ba'
STARTUP_WARNINGS = {
    '`--dangerously-bypass-hook-trust` is enabled. Enabled hooks may run without review for this invocation.': 2,
    'Code Mode is unavailable because code-mode host is disabled. Code mode will fail closed; '
    'enable `features.code_mode_host` and install `codex-code-mode-host`.': 1,
}
DISABLED = (
    'shell_tool', 'shell_snapshot', 'multi_agent', 'multi_agent_v2',
    'unified_exec', 'unified_exec_tty', 'daemon_auto_start', 'guardian_approval',
    'apps', 'plugins', 'remote_plugin', 'plugin_discovery_prefetch',
    'browser_use', 'browser_use_external', 'browser_use_full_cdp_access',
    'computer_use', 'image_generation', 'code_mode', 'code_mode_host',
    'code_mode_only', 'memories', 'skill_search', 'skill_mcp_dependency_install',
    'goals', 'request_permissions_tool', 'in_app_local_automation',
    'in_app_browser', 'in_app_chat', 'artifact', 'rollout_budget',
    'auth_elicitation', 'tool_suggest', 'sleep_tool',
)

# Exact native inventory for the pinned 0.167 client; changes require review.
# Removed flags remain in its list. These are not extra model tool grants.
ENABLED_FEATURES = frozenset('''
content_item_kinds code_mode_interrupt instant_interrupt terminal_resize_reflow
sqlite write_stdin_approval hooks api_key_model_discovery cli_daybreak
api_key_cyber_access_programs enable_request_compression unbounded_connection_retries
worktrees system_proxy_fallback mcp_oauth_refresh_coordination
tool_search_always_defer_mcp_tools deferred_tool_world_state incremental_tools unified_exec
prediction_preserve_parent_tools skip_host_skill_discovery browser_annotation_api
in_app_dictation in_app_voice in_app_updates plugin_sharing resize_all_images
item_ids mentions_v2 steer guardian_reuse_parent_compaction reasoning_effort_override
collaboration_modes tool_call_mcp_elicitation bedrock_setup_wizard fast_mode
ultrafast_mode realtime_conversation tui_app_server compaction_image_budget
workspace_dependencies
'''.split())


def check_native_features(rows, media=False):
    require(isinstance(rows, list) and all(isinstance(r, dict) and isinstance(r.get('name'), str)
            and type(r.get('enabled')) is bool for r in rows), 'CODEX_FEATURE_SCHEMA')
    require(len({r['name'] for r in rows}) == len(rows), 'CODEX_FEATURE_SCHEMA')
    enabled = {r['name'] for r in rows if r['enabled']}
    require(enabled == ENABLED_FEATURES | ({'view_image'} if media else set()), 'CODEX_FEATURE_SET_CHANGED')
    return sorted(enabled)


def require(ok, code):
    if not ok:
        raise ValueError(code)


def offered_tool_names(rows, prefix=''):
    """Names only, from native request/rollout tool declarations, not prose."""
    require(isinstance(rows, list), 'CODEX_TOOL_SCHEMA')
    names = []
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get('name'), str) and bool(row['name']),
                'CODEX_TOOL_SCHEMA')
        name = prefix + row['name']
        if row.get('type') == 'namespace':
            names.extend(offered_tool_names(row.get('tools'), name + '__'))
        else:
            require(row.get('type') in ('function', 'custom'), 'CODEX_TOOL_SCHEMA')
            names.append(name)
    return names


def check_offered_tools(rows):
    names = offered_tool_names(rows)
    require(len(names) == len(OFFERED_TOOLS) and set(names) == OFFERED_TOOLS,
            'CODEX_OFFERED_TOOLS_CHANGED')
    require(declaration_hash(rows) == DECLARATION_SHA256, 'CODEX_TOOL_DECLARATION_CHANGED')
    return names


def declaration_hash(rows):
    # Match the reviewed canonicalization exactly, including default separators.
    return hashlib.sha256(json.dumps(rows, sort_keys=True).encode('utf-8')).hexdigest()


def checkpoint_history(payload):
    """The two observed 0.167 compaction paths; unfamiliar shapes stop review."""
    keys = {'message', 'replacement_history', 'replacement_history_metadata',
            'retained_context', 'window_number', 'first_window_id', 'previous_window_id',
            'window_id', 'compaction_response_id', 'latest_token_usage_record', 'resume_metadata'}
    require(isinstance(payload, dict) and set(payload) == keys, 'CODEX_COMPACTION_SHAPE')
    history = payload['replacement_history']
    require(isinstance(history, list) and bool(history) and
            isinstance(payload['replacement_history_metadata'], list) and
            len(payload['replacement_history_metadata']) == len(history) and
            all(isinstance(v, dict) for v in payload['replacement_history_metadata']) and
            isinstance(payload['message'], str) and type(payload['window_number']) is int and
            payload['window_number'] > 0, 'CODEX_COMPACTION_SHAPE')
    for key in ('first_window_id', 'previous_window_id', 'window_id', 'compaction_response_id'):
        require(isinstance(payload[key], str) and bool(payload[key]), 'CODEX_COMPACTION_SHAPE')
    for key in ('retained_context', 'latest_token_usage_record', 'resume_metadata'):
        require(isinstance(payload[key], dict), 'CODEX_COMPACTION_SHAPE')
    opaque = []
    for item in history:
        require(isinstance(item, dict) and item.get('type') in (
            'additional_tools', 'message', 'compaction', 'function_call', 'custom_tool_call',
            'function_call_output', 'custom_tool_call_output'), 'CODEX_COMPACTION_ITEM')
        if item['type'] == 'compaction':
            metadata_key = 'internal_chat_message_metadata_passthrough'
            required_keys = {'type', 'id', 'encrypted_content'}
            require(set(item) in (required_keys, required_keys | {metadata_key}) and
                    all(isinstance(item[k], str) and bool(item[k]) for k in ('id', 'encrypted_content')),
                    'CODEX_COMPACTION_ITEM')
            if metadata_key in item:
                metadata = item[metadata_key]
                require(isinstance(metadata, dict) and set(metadata) == {'turn_id'} and
                        isinstance(metadata['turn_id'], str) and bool(metadata['turn_id']),
                        'CODEX_COMPACTION_ITEM')
            opaque.append(item)
    # Fallback keeps a textual summary; remote v2 keeps one opaque wire item.
    require((bool(payload['message']) and not opaque) or
            (payload['message'] == '' and len(opaque) == 1), 'CODEX_COMPACTION_PATH')
    return history


def session_items(home, thread_id=None, pending=False):
    """Read only the matching private rollout; never export raw payloads."""
    require(thread_id is None or isinstance(thread_id, str) and bool(thread_id), 'CODEX_THREAD_INVALID')
    found = []
    for path in sorted((Path(home) / 'sessions').rglob('rollout-*.jsonl')):
        data = path.read_bytes()
        if pending:
            data = data[:data.rfind(b'\n')+1]
        events = [json.loads(line) for line in data.splitlines() if line]
        if pending and not events:
            continue
        ids = {e.get('payload', {}).get('id') for e in events if e.get('type') == 'session_meta'}
        if thread_id is not None and thread_id not in ids:
            continue
        require(len(ids) == 1 and all(isinstance(i, str) and i for i in ids), 'CODEX_SESSION_INVALID')
        found.append((next(iter(ids)), events))
    if pending and not found:
        return None, []
    require(len(found) == 1, 'CODEX_SESSION_MISSING_OR_AMBIGUOUS')
    identifier, events = found[0]
    items = []
    for event in events:
        if event.get('type') == 'response_item':
            require(event['payload'].get('type') != '_compaction_checkpoint', 'CODEX_COMPACTION_SHAPE')
            items.append(event['payload'])
        elif event.get('type') == 'compacted':
            checkpoint_history(event.get('payload'))
            # Append a checkpoint: never replace the audit's earlier calls.
            items.append({'type': '_compaction_checkpoint', 'payload': event['payload']})
        else:
            require('compact' not in event.get('type', ''), 'CODEX_COMPACTION_SHAPE')
    return identifier, items


def session_tool_records(home, thread_id):
    """Export only offered names; raw rollouts stay in the private client home."""
    require(isinstance(thread_id, str) and bool(thread_id), 'CODEX_THREAD_INVALID')
    records = []
    _, items = session_items(home, thread_id)
    for item in items:
        candidates = checkpoint_history(item['payload']) if item.get('type') == '_compaction_checkpoint' else [item]
        for candidate in candidates:
            if candidate.get('type') == 'additional_tools':
                records.append({'thread_id': thread_id, 'item_id': candidate.get('id'),
                                'names': offered_tool_names(candidate.get('tools')),
                                'declaration_sha256': declaration_hash(candidate.get('tools'))})
    require(bool(records), 'CODEX_TOOL_LIST_MISSING')
    return records


def resolve_call(item, declaration):
    """Resolve native spelling and kind against one exact tool declaration.

    The session scanner checks the declaration pin before calling this helper.
    A bare name must be unique even when the duplicate has a different kind.
    Joined names are output labels only, never an authorization comparison.
    """
    kind = item.get('type')
    name, namespace = item.get('name'), item.get('namespace')
    require(kind in ('function_call', 'custom_tool_call') and
            isinstance(name, str) and bool(name) and
            ('namespace' not in item or isinstance(namespace, str) and bool(namespace)),
            'CODEX_SESSION_CALL_INVALID')
    entries = []
    for group in declaration:
        require(isinstance(group, dict) and group.get('type') == 'namespace' and
                isinstance(group.get('name'), str) and bool(group['name']) and
                isinstance(group.get('tools'), list), 'CODEX_TOOL_SCHEMA')
        for tool in group['tools']:
            require(isinstance(tool, dict) and isinstance(tool.get('name'), str) and
                    bool(tool['name']) and tool.get('type') in ('custom', 'function'),
                    'CODEX_TOOL_SCHEMA')
            if tool['name'] == name and (namespace is None or namespace == group['name']):
                entries.append((group['name'], tool['name'], tool['type']))
    require(bool(entries), 'CODEX_SESSION_CALL_UNDECLARED')
    require(len(entries) == 1, 'CODEX_SESSION_CALL_AMBIGUOUS')
    namespace, name, declared_type = entries[0]
    require(kind == {'custom': 'custom_tool_call', 'function': 'function_call'}[declared_type],
            'CODEX_SESSION_CALL_TYPE')
    return {'call_id': item.get('call_id'), 'namespace': namespace, 'tool': name,
            'declared_type': declared_type, 'name': namespace + '__' + name,
            'observed': {key: item[key] for key in ('type', 'namespace', 'name') if key in item},
            'allowed': (namespace, name, kind) == ('mcp__facts', 'operation', 'function_call')}


def session_calls(items, require_declaration=False):
    calls = []
    declaration = None
    for item in items:
        kind = item.get('type', '')
        if kind == 'additional_tools':
            declaration = item.get('tools')
            check_offered_tools(declaration)
        elif kind == '_compaction_checkpoint':
            require(declaration is not None, 'CODEX_TOOL_LIST_MISSING')
            history = checkpoint_history(item['payload'])
            retained = session_calls([v for v in history if v['type'] != 'compaction'], require_declaration=True)
            require(all(v['allowed'] for v in retained), 'CODEX_FORBIDDEN_SESSION_CALL')
        elif kind in ('function_call', 'custom_tool_call'):
            require(declaration is not None, 'CODEX_TOOL_LIST_MISSING')
            calls.append(resolve_call(item, declaration))
        elif kind not in ('function_call_output', 'custom_tool_call_output'):
            require('compact' not in kind, 'CODEX_COMPACTION_ITEM')
            require('call' not in kind, 'CODEX_SESSION_CALL_UNSUPPORTED')
    require(not require_declaration or declaration is not None, 'CODEX_TOOL_LIST_MISSING')
    return calls


def audit_session(home, thread_id=None, offered_path=None):
    identifier, items = session_items(home, thread_id)
    tools = session_tool_records(home, identifier)
    if offered_path is not None:
        # The private session can precede thread.started on public stdout.
        # Preserve its offered set before a resolver/declaration refusal.
        save(offered_path, tools)
    return {'thread_id': identifier, 'tools': tools,
            'calls': session_calls(items, require_declaration=True)}


def poll_session(home, thread_id=None, required=False):
    identifier, items = session_items(home, thread_id, pending=True)
    require(not required or identifier is not None, 'CODEX_SESSION_MISSING_OR_AMBIGUOUS')
    require(all(c['allowed'] for c in session_calls(items, require_declaration=required)),
            'CODEX_FORBIDDEN_SESSION_CALL')


def enforce_session(audit):
    require(all(c['allowed'] for c in audit['calls']), 'CODEX_FORBIDDEN_SESSION_CALL')
    require(all(len(r['names']) == len(OFFERED_TOOLS) and set(r['names']) == OFFERED_TOOLS
                for r in audit['tools']), 'CODEX_OFFERED_TOOLS_CHANGED')
    require(all(r['declaration_sha256'] == DECLARATION_SHA256 for r in audit['tools']),
            'CODEX_TOOL_DECLARATION_CHANGED')


class HookMonitor:
    """Poll append-only hook evidence even when the native stdout is silent."""
    def __init__(self, path):
        self.path = Path(path)
        self.seen = b''

    def poll(self, final=False):
        data = self.path.read_bytes() if self.path.exists() else b''
        require(data.startswith(self.seen), 'CODEX_HOOK_LOG_CHANGED')
        tail = data[len(self.seen):]
        complete, _, pending = tail.rpartition(b'\n')
        if b'\n' not in tail:
            complete, pending = b'', tail
        for line in complete.splitlines():
            row = json.loads(line)
            require(isinstance(row, dict) and row.get('decision') in ('allow', 'deny'), 'CODEX_HOOK_LOG_INVALID')
            require(row['decision'] != 'deny', 'CODEX_HOOK_DENIED')
            require(row.get('tool') == TOOL, 'CODEX_HOOK_UNEXPECTED_ALLOW')
        self.seen = data[:len(data)-len(pending)]
        require(not final or not pending, 'CODEX_HOOK_LOG_PARTIAL')


def stop_group(process):
    if process is None:
        return
    process.poll()
    if not group_alive(process.pid):
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    except PermissionError:
        process.poll()
        if group_alive(process.pid):
            raise
    try:
        process.wait(timeout=.5)
    except subprocess.TimeoutExpired:
        pass
    # Reap surviving children even when their group leader has already exited.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        process.poll()
        if group_alive(process.pid):
            raise
    process.wait(timeout=5)


def group_alive(pgid):
    require(type(pgid) is int and pgid > 1, 'CODEX_CLIENT_GROUP_INVALID')
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # Uncertain ownership/liveness never authorizes another run.


def require_quiescent_runs(state, config=None):
    process_tree.require_quiescent(state, config)


class ClientSignal(BaseException):
    pass


@contextmanager
def termination_handlers():
    status = {'signal': None, 'cleaning': False, 'deferring': False}
    def interrupt(signum, frame):
        status['signal'] = signum
        if not status['cleaning'] and not status['deferring']:
            raise ClientSignal('CODEX_TERMINATED:' + signal.Signals(signum).name)
    previous = {s: signal.signal(s, interrupt) for s in (signal.SIGTERM, signal.SIGHUP, signal.SIGINT)}
    try:
        yield status
    finally:
        for s, handler in previous.items():
            signal.signal(s, handler)


@contextmanager
def defer_termination(status):
    # Defer raising until PGID capture without giving the child a blocked mask.
    status['deferring'] = True
    try:
        yield
    finally:
        status['deferring'] = False
        if status['signal'] is not None:
            raise ClientSignal('CODEX_TERMINATED:' + signal.Signals(status['signal']).name)


def phase_expiry(authority, started):
    return min(authority['deadline'], started + 180) if authority['purpose'] == 'access_preflight' and authority.get('probe') is not None else authority['deadline']


def phase_message(root, authority, thread_id, probe_message):
    probe = authority.get('probe')
    if probe_message is not None or probe is not None:
        require(authority['purpose'] == 'access_preflight', 'CODEX_PROBE_FORBIDDEN')
        require(probe_message is not None and isinstance(probe, dict), 'CODEX_PROBE_AUTHORIZATION')
        path = Path(probe_message).resolve(strict=True)
        require(probe.get('path') == str(path) and probe.get('sha256') == sha(path)
                and probe.get('tool') in FORBIDDEN_TOOLS and type(probe.get('resume')) is bool
                and probe['resume'] == (thread_id is not None), 'CODEX_PROBE_AUTHORIZATION')
        return path.read_bytes()
    return (Path(root) / 'message.txt').read_bytes()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    try:
        temporary.write_text(json.dumps(value, indent=2) + '\n')
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def toml(value):
    """Encode the small JSON-compatible config subset used by this adapter."""
    if isinstance(value, str):
        return json.dumps(value)
    if type(value) is bool:
        return 'true' if value else 'false'
    if type(value) is int:
        return str(value)
    if isinstance(value, list):
        return '[' + ', '.join(toml(v) for v in value) + ']'
    if isinstance(value, dict):
        return '{' + ', '.join(json.dumps(k) + ' = ' + toml(v) for k, v in value.items()) + '}'
    raise ValueError('CODEX_CONFIG_VALUE')


def settings(root, workspace, bridge, session, interpreter, prompt, model, effort, media):
    hook = shlex.join([interpreter, '-B', str(Path(__file__).resolve()),
                      'hook', '--policy', str(root / 'policy.json')])
    features = {name: False for name in DISABLED}
    features.update(hooks=True, view_image=bool(media), skip_host_skill_discovery=True)
    features['code_mode'] = {'enabled': False, 'direct_only_tool_namespaces': ['mcp__facts']}
    return {
        'model': model, 'model_reasoning_effort': effort,
        'cli_auth_credentials_store': 'file',
        'approval_policy': 'never', 'default_permissions': 'structured',
        'agents': {'enabled': False}, 'include_collaboration_mode_instructions': False,
        'suppress_unstable_features_warning': True,
        'web_search': 'disabled', 'project_doc_max_bytes': 0,
        'skills': {'bundled': {'enabled': False}},
        'model_instructions_file': str(prompt),
        'check_for_update_on_startup': False, 'analytics': {'enabled': False},
        'features': features,
        'permissions': {'structured': {
            'filesystem': {':root': 'deny', ':minimal': 'read', str(workspace): 'read'},
            'network': {'enabled': False}}},
        'hooks': {'PreToolUse': [{'matcher': '', 'hooks': [
            {'type': 'command', 'command': hook, 'timeout': 10}]}]},
        'mcp_servers': {'facts': {
            'command': interpreter,
            'args': ['-B', str(bridge), '--mcp', str(session), 'implementer', 'corridor'],
            'env': {'PYTHONPATH': str(bridge.parent), 'PYTHONDONTWRITEBYTECODE': '1'},
            'enabled_tools': ['operation'], 'required': True,
            'tools': {'operation': {'approval_mode': 'approve'}},
            'omit_tools_from': ['deferred', 'code_mode'],
            'startup_timeout_sec': 120, 'tool_timeout_sec': 3600}},
    }


def prepare(root, *, session, prompt, model, effort, client, interpreter,
            service_root, heavy_lock, message, media=(), compaction_probe=False):
    root = Path(root).resolve()
    require(not root.exists(), 'CODEX_PROFILE_EXISTS')
    require(all(isinstance(v, str) and v.strip() for v in (model, effort)), 'MODEL_CONFIGURATION_REQUIRED')
    require(isinstance(message, str) and bool(message.strip()), 'CODEX_MESSAGE_REQUIRED')
    session, client, service_root = (Path(p).resolve(strict=True) for p in (session, client, service_root))
    code_host = client.parent / 'codex-code-mode-host'
    require(code_host.is_file(), 'CODEX_CODE_HOST_MISSING')
    bridge = service_root / 'scripts/structured_pass_bridge.py'
    require(bridge.is_file(), 'CODEX_SERVICE_MISSING')
    require(Path(heavy_lock).is_absolute(), 'SHARED_HEAVY_RUN_REQUIRED')
    # Do not open the live corridor here: its reviewer cache is not preparation
    # scratch. Reading these files only records a handoff precondition.
    state_path = session / 'editor/state.json'
    state = json.loads(state_path.read_text())
    require(isinstance(state.get('reader_hashes'), dict), 'CODEX_SESSION_INVALID')
    selected = []
    for path in media:
        path = Path(path).resolve(strict=True)
        data = path.read_bytes()
        require(data.startswith(b'\x89PNG\r\n\x1a\n'), 'CODEX_MEDIA_REQUIRES_PNG')
        selected.append((path.name, data))
    require(len({name for name, _ in selected}) == len(selected), 'CODEX_MEDIA_DUPLICATE')
    root.mkdir(parents=True)
    (root / 'auth-config').mkdir(mode=0o700)
    workspace = root / 'workspace'
    workspace.mkdir()
    images = {}
    for name, data in selected:
        target = workspace / name
        target.write_bytes(data)
        images[str(target)] = sha(target)
    prompt_path = root / 'prompt.md'
    prompt_path.write_bytes(Path(prompt).read_bytes())
    (root / 'message.txt').write_text(message)
    save(root / 'policy.json', {'tool': TOOL, 'media': images, 'log': str(root / 'hooks.jsonl'),
                              'session_home': str(root / 'auth-config')})
    configuration = settings(root, workspace, bridge, session, str(Path(interpreter).resolve()),
                             prompt_path, model, effort, images)
    require(type(compaction_probe) is bool, 'CODEX_COMPACTION_CONFIGURATION')
    if compaction_probe:
        configuration['model_auto_compact_token_limit'] = 16384
    save(root / 'config.json', configuration)
    pins = {str(p): sha(p) for p in (
        Path(__file__).resolve(), Path(process_tree.__file__).resolve(), bridge, prompt_path,
        root / 'message.txt', root / 'policy.json', root / 'config.json')}
    pins.update({str(p): sha(p) for p in (service_root / 'scripts/structured_pass').glob('*.py')})
    config = {
        'schema': 'structured-codex-client-preparation-v1', 'client': str(client),
        'client_sha256': sha(client), 'service_root': str(service_root),
        'code_host': str(code_host), 'code_host_sha256': sha(code_host),
        'tool_declaration_sha256': DECLARATION_SHA256,
        'session': str(session), 'role': 'implementer', 'model': model, 'effort': effort,
        'workspace': str(workspace), 'media': images, 'files': pins,
        'heavy_lock': str(Path(heavy_lock).resolve()),
        'initial_editor_sha256': sha(state_path),
        'initial_reader_hashes': state['reader_hashes'],
        'configuration_sha256': sha(root / 'config.json'),
        'usage_policy': 'report_native_turns_and_tokens_no_response_equivalence',
    }
    if compaction_probe:
        config['compaction_probe'] = True
    save(root / 'launch.json', config)
    save(root / 'state.json', {'authorized': False, 'thread_id': None, 'runs': []})
    return config


def compaction_configuration(config, settings, authority=None):
    probe = config.get('compaction_probe', False)
    require(type(probe) is bool, 'CODEX_COMPACTION_CONFIGURATION')
    keys = {k for k in settings if k.startswith('model_auto_compact_') or k == 'model_context_window'}
    require(keys == ({'model_auto_compact_token_limit'} if probe else set()),
            'CODEX_COMPACTION_CONFIGURATION')
    if probe:
        threshold = settings['model_auto_compact_token_limit']
        require(type(threshold) is int and threshold == 16384, 'CODEX_COMPACTION_CONFIGURATION')
        if authority is not None:
            require(authority.get('purpose') == 'access_preflight' and
                    authority.get('compaction_probe') is True, 'CODEX_COMPACTION_AUTHORIZATION')
            record = authority.get('compaction_protocol', {})
            require(isinstance(record, dict) and isinstance(record.get('path'), str) and
                    Path(record['path']).is_file() and sha(record['path']) == record.get('sha256'),
                    'CODEX_COMPACTION_AUTHORIZATION')


def verify(root):
    root = Path(root).resolve()
    config = json.loads((root / 'launch.json').read_text())
    require(sha(config['client']) == config['client_sha256'], 'CODEX_CLIENT_CHANGED')
    require(sha(config['code_host']) == config['code_host_sha256'], 'CODEX_CODE_HOST_CHANGED')
    require(config['tool_declaration_sha256'] == DECLARATION_SHA256, 'CODEX_TOOL_DECLARATION_CHANGED')
    require(all(sha(p) == expected for p, expected in config['files'].items()), 'CODEX_CONFIGURATION_CHANGED')
    require(sha(root / 'config.json') == config['configuration_sha256'], 'CODEX_CONFIGURATION_CHANGED')
    compaction_configuration(config, json.loads((root / 'config.json').read_text()))
    workspace = Path(config['workspace'])
    require(workspace.is_dir() and {str(p) for p in workspace.iterdir()} == set(config['media']),
            'CODEX_WORKSPACE_CHANGED')
    require(all(not Path(p).is_symlink() and sha(p) == expected for p, expected in config['media'].items()),
            'CODEX_MEDIA_CHANGED')
    # The client installs bundled skills even when their loading is disabled.
    # Permit only its real .system directory, never user skill entries/links.
    home = root / 'auth-config'
    require(not any((home / p).exists() or (home / p).is_symlink()
                    for p in ('config.toml', 'hooks.json', 'plugins')),
            'CODEX_AMBIENT_CONFIGURATION')
    skills = home / 'skills'
    require(not skills.is_symlink(), 'CODEX_AMBIENT_CONFIGURATION')
    if skills.exists():
        require(skills.is_dir() and all(p.name == '.system' and p.is_dir() and not p.is_symlink()
                for p in skills.iterdir()), 'CODEX_AMBIENT_CONFIGURATION')
    return config


def environment(root):
    result = {k: v for k, v in os.environ.items() if k in ('PATH', 'HOME', 'TMPDIR', 'USER', 'SHELL', 'LANG')}
    result.update(CODEX_HOME=str(Path(root).resolve() / 'auth-config'), PYTHONDONTWRITEBYTECODE='1')
    result['GIT_CEILING_DIRECTORIES'] = str(Path(root).resolve())
    return result


def overrides(root):
    config = json.loads((Path(root) / 'config.json').read_text())
    return [part for k, v in config.items() for part in ('-c', k + '=' + toml(v))]


def command(root, thread_id=None):
    config = verify(root)
    args = [config['client'], 'exec', '--strict-config', '--ignore-user-config', '--ignore-rules',
            '--dangerously-bypass-hook-trust', '--skip-git-repo-check', '--json', *overrides(root)]
    if thread_id is not None:
        require(isinstance(thread_id, str) and bool(thread_id) and not thread_id.startswith('-'),
                'CODEX_THREAD_INVALID')
        args += ['resume', thread_id]
    return args + ['-']


def admission(root, config):
    """Separate, reviewable authorization; never inherited from a Claude run."""
    root = Path(root)
    path = root / 'authorization.json'
    require(path.is_file(), 'CODEX_INFERENCE_NOT_AUTHORIZED')
    authority = json.loads(path.read_text())
    require(authority.get('authorized') is True and authority.get('owner_message'),
            'CODEX_INFERENCE_NOT_AUTHORIZED')
    require(authority.get('launch_sha256') == sha(root / 'launch.json'), 'CODEX_AUTHORIZATION_CHANGED')
    require(authority.get('purpose') in ('access_preflight', 'pilot_takeover'), 'CODEX_AUTHORIZATION_PURPOSE')
    require(authority.get('token_response_caps') == 'none_usage_reporting_only', 'CODEX_USAGE_POLICY_CHANGED')
    deadline = authority.get('deadline')
    require(type(deadline) in (float, int) and time.time() < deadline, 'CODEX_DEADLINE_EXPIRED')
    compaction_configuration(config, json.loads((root / 'config.json').read_text()), authority)
    if authority['purpose'] == 'pilot_takeover':
        for name in ('access_preflight', 'transition_review'):
            record = authority.get(name, {})
            require(isinstance(record, dict) and isinstance(record.get('path'), str)
                    and Path(record['path']).is_file() and sha(record['path']) == record.get('sha256'),
                    'CODEX_ADMISSION_EVIDENCE_REQUIRED')
    require(os.environ.get('NESREV_HEAVY_RUN_LOCK') == config['heavy_lock'], 'SHARED_HEAVY_RUN_REQUIRED')
    return authority


def authenticate(root, config):
    result = subprocess.run([config['client'], '-c', 'cli_auth_credentials_store="file"', 'login', 'status'],
                            cwd=config['workspace'], env=environment(root), capture_output=True, text=True, timeout=15)
    require(result.returncode == 0 and 'Logged in using ChatGPT' in result.stdout + result.stderr,
            'CODEX_SUBSCRIPTION_LOGIN_REQUIRED')


def run(root, probe_message=None):
    """One owner-authorized phase; an error never starts a replacement phase."""
    root = Path(root).resolve()
    config = verify(root)
    authority = admission(root, config)
    import fcntl
    with (root / 'run.lock').open('a+b') as lock, termination_handlers() as termination:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError('CODEX_ALREADY_RUNNING') from exc
        state = json.loads((root / 'state.json').read_text())
        require_quiescent_runs(state, config)
        require(not state.get('halted') and not any(r['status'] == 'running' for r in state['runs']),
                'CODEX_RECOVERY_REQUIRED')
        message = phase_message(root, authority, state['thread_id'], probe_message)
        if not state['runs']:
            require(sha(Path(config['session']) / 'editor/state.json') == config['initial_editor_sha256'],
                    'CODEX_HANDOFF_CHANGED')
        authenticate(root, config)
        require(time.time() < authority['deadline'], 'CODEX_DEADLINE_EXPIRED')
        identifier = uuid.uuid4().hex
        folder = root / 'runs' / identifier
        folder.mkdir(parents=True)
        row = {'id': identifier, 'status': 'running', 'started': time.time(),
               'authorization_sha256': sha(root / 'authorization.json'),
               'launch_sha256': sha(root / 'launch.json'),
               'heavy_run_id': os.environ.get('NESREV_HEAVY_RUN_ID'),
               'continuation': state['thread_id'] is not None, 'native_turns': [],
               'probe': authority.get('probe'), 'message_sha256': hashlib.sha256(message).hexdigest()}
        state['runs'].append(row)
        save(root / 'state.json', state)
        events = Events(state['thread_id'])
        process = None
        error = None
        monitor = HookMonitor(root / 'hooks.jsonl')
        phase_deadline = phase_expiry(authority, row['started'])
        row['phase_deadline'] = phase_deadline
        try:
            monitor.poll()
            with (folder / 'stderr.log').open('wb') as errors, (folder / 'stdout.jsonl').open('wb') as output:
                with defer_termination(termination):
                    process = subprocess.Popen(command(root, state['thread_id']), cwd=config['workspace'],
                        env=environment(root), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errors,
                        start_new_session=True)
                    row['client_pgid'] = process.pid
                    save(root / 'state.json', state)
                    process_tree.observe(row, config)
                    save(root / 'state.json', state)
                process.stdin.write(message)
                process.stdin.close()
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stdout, selectors.EVENT_READ)
                    pending = b''
                    while selector.get_map():
                        if process_tree.observe(row, config)[0]:
                            save(root / 'state.json', state)
                        monitor.poll()
                        poll_session(root / 'auth-config', events.thread)
                        require(time.time() < authority['deadline'], 'CODEX_DEADLINE_EXPIRED')
                        require(time.time() < phase_deadline, 'CODEX_PHASE_TIMEOUT')
                        for key, _ in selector.select(.1):
                            chunk = os.read(key.fileobj.fileno(), 65536)
                            if not chunk:
                                selector.unregister(key.fileobj)
                                continue
                            output.write(chunk); output.flush()
                            pending += chunk
                            require(len(pending) <= 8 * 1024 * 1024, 'CODEX_EVENT_TOO_LARGE')
                            while b'\n' in pending:
                                line, pending = pending.split(b'\n', 1)
                                if not line: continue
                                events.accept(json.loads(line))
                                state['thread_id'] = events.thread
                                row['native_turns'] = list(events.turns)
                                save(root / 'state.json', state)
                    require(not pending.strip(), 'CODEX_PARTIAL_EVENT')
                process.wait(timeout=5)
                require(process.returncode == 0, 'CODEX_CLIENT_FAILED')
                require(events.complete(), 'CODEX_STREAM_INCOMPLETE')
        except BaseException as exc:
            termination['cleaning'] = True
            error = type(exc).__name__ + ': ' + str(exc)
            row.update(status='stopping', error=error, usage_uncertain=True)
            state['halted'] = True
            save(root / 'state.json', state)
            raise
        finally:
            termination['cleaning'] = True
            audit_errors = []
            try:
                process_tree.stop_tree(process, row, config, lambda: save(root / 'state.json', state))
            except Exception as exc:
                audit_errors.append('CODEX_PROCESS_CLEANUP_FAILED: ' + str(exc))
            try:
                if process is not None and process.poll() is None:
                    stop_group(process)
            except Exception as exc:
                audit_errors.append('CODEX_PROCESS_CLEANUP_FAILED: ' + str(exc))
            try:
                require_quiescent_runs(state, config)
                if not audit_errors:
                    row['processes_reconciled'] = True
            except Exception as exc:
                audit_errors.append(str(exc))
            if process is not None and process.stdout is not None:
                process.stdout.close()
            try:
                audit = audit_session(root / 'auth-config', events.thread,
                                      offered_path=folder / 'offered-tools.json')
                state['thread_id'] = audit['thread_id']
                save(folder / 'session-audit.json', audit)
                enforce_session(audit)
            except Exception as exc:
                audit_errors.append(str(exc))
            try:
                monitor.poll(final=True)
            except Exception as exc:
                audit_errors.append(str(exc))
            original_error = error
            if termination['signal'] is not None and error is None:
                error = 'CODEX_TERMINATED:' + signal.Signals(termination['signal']).name
            if audit_errors and error is None:
                error = audit_errors[0]
            row.update(status='finished' if error is None else 'interrupted', finished=time.time(),
                       error=error, exit_code=process.returncode if process is not None else None,
                       native_turns=events.turns, startup_warnings=events.warnings,
                       usage_uncertain=error is not None, audit_errors=audit_errors)
            state['halted'] = error is not None
            save(root / 'state.json', state)
            save(folder / 'run.json', row)
            if original_error is None and error is not None:
                raise ValueError(error)
        return row


def hook_decision(policy, request):
    require(isinstance(request, dict), 'CODEX_HOOK_SCHEMA')
    tool = request.get('tool_name')
    allowed = request.get('hook_event_name') == 'PreToolUse' and tool == TOOL
    if allowed and policy.get('session_home'):
        try:
            poll_session(policy['session_home'], request.get('session_id'), required=True)
        except (ValueError, OSError):
            allowed = False
    if request.get('hook_event_name') == 'PreToolUse' and tool == 'view_image':
        args = request.get('tool_input')
        value = args.get('path') if isinstance(args, dict) else None
        path = Path(value) if isinstance(value, str) else Path()
        expected = policy['media'].get(str(path))
        allowed = bool(expected and path.is_absolute() and not path.is_symlink()
                       and path.is_file() and sha(path) == expected)
    return {'hookSpecificOutput': {'hookEventName': 'PreToolUse',
            'permissionDecision': 'allow' if allowed else 'deny',
            'permissionDecisionReason': 'STRUCTURED_PASS_ALLOW' if allowed else 'STRUCTURED_PASS_DENY'}}


class Events:
    """Record native turn usage. Tool items and messages are not responses."""
    def __init__(self, expected_thread=None):
        self.thread = expected_thread
        self.initialized = False
        self.active = False
        self.turns = []
        self.error = None
        self.warnings = []
        self.turn_started = False

    def accept(self, event):
        require(isinstance(event, dict) and isinstance(event.get('type'), str), 'CODEX_EVENT_INVALID')
        kind = event['type']
        if kind == 'thread.started':
            identifier = event.get('thread_id')
            require(isinstance(identifier, str) and bool(identifier) and not self.initialized,
                    'CODEX_THREAD_INVALID')
            require(self.thread is None or self.thread == identifier, 'CODEX_THREAD_CHANGED')
            self.thread = identifier
            self.initialized = True
        elif kind == 'turn.started':
            require(self.initialized and not self.active, 'CODEX_EVENT_ORDER')
            self.active = True
            self.turn_started = True
        elif kind in ('turn.completed', 'turn.failed'):
            require(self.active, 'CODEX_EVENT_ORDER')
            usage = event.get('usage')
            if kind == 'turn.completed':
                require(isinstance(usage, dict) and all(type(usage.get(k)) is int and usage[k] >= 0
                        for k in ('input_tokens', 'cached_input_tokens', 'output_tokens')), 'CODEX_USAGE_UNAVAILABLE')
            else:
                self.error = event.get('error') or 'CODEX_TURN_FAILED'
            self.turns.append(event)
            self.active = False
        elif kind == 'error':
            self.error = event.get('message') or 'CODEX_CLIENT_ERROR'
        elif kind in ('item.started', 'item.updated', 'item.completed'):
            require(isinstance(event.get('item'), dict), 'CODEX_EVENT_ORDER')
            item = event['item']
            if kind == 'item.completed' and item.get('type') == 'error' and not self.turn_started:
                message = item.get('message')
                require(self.initialized and isinstance(message, str) and message in STARTUP_WARNINGS,
                        'CODEX_STARTUP_WARNING_UNEXPECTED')
                require(sum(w['item']['message'] == message for w in self.warnings) < STARTUP_WARNINGS[message],
                        'CODEX_STARTUP_WARNING_UNEXPECTED')
                self.warnings.append(event)
                return
            require(self.active, 'CODEX_EVENT_ORDER')
            allowed = item.get('type') in ('agent_message', 'reasoning')
            if item.get('type') == 'mcp_tool_call':
                allowed = item.get('server') == 'facts' and item.get('tool') == 'operation'
            # Detection complements the pre-tool denial; it is not the access
            # boundary and cannot undo a tool call.
            require(allowed, 'CODEX_UNEXPECTED_TOOL_EVENT')
        else:
            raise ValueError('CODEX_EVENT_UNSUPPORTED')

    def complete(self):
        return bool(self.initialized and self.turns and not self.active and self.error is None
                    and all(t['type'] == 'turn.completed' for t in self.turns))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    hook = sub.add_parser('hook')
    hook.add_argument('--policy', type=Path, required=True)
    check = sub.add_parser('check')
    check.add_argument('--root', type=Path, required=True)
    launch = sub.add_parser('run')
    launch.add_argument('--root', type=Path, required=True)
    launch.add_argument('--probe-message', type=Path)
    prep = sub.add_parser('prepare')
    for name in ('root', 'session', 'prompt', 'client', 'interpreter', 'service-root', 'heavy-lock', 'message-file'):
        prep.add_argument('--' + name, type=Path, required=True)
    for name in ('model', 'effort'):
        prep.add_argument('--' + name, required=True)
    prep.add_argument('--media', type=Path, action='append', default=[])
    prep.add_argument('--compaction-probe', action='store_true')
    args = parser.parse_args()
    if args.action == 'hook':
        try:
            policy = json.loads(args.policy.read_text())
            request = json.load(sys.stdin)
            result = hook_decision(policy, request)
            with Path(policy['log']).open('a') as stream:
                stream.write(json.dumps({'tool': request.get('tool_name'),
                    'tool_use_id': request.get('tool_use_id'), 'session_id': request.get('session_id'),
                    'input_sha256': hashlib.sha256(json.dumps(request.get('tool_input'), sort_keys=True,
                        separators=(',', ':')).encode()).hexdigest(), 'at': time.time(),
                    'decision': result['hookSpecificOutput']['permissionDecision']}) + '\n')
            print(json.dumps(result))
        except Exception:
            # Codex treats hook failures as diagnostics. Explicit exit 2 is
            # required to deny when the policy, input or audit log is broken.
            print('STRUCTURED_PASS_DENY: hook input, policy or log unavailable', file=sys.stderr)
            raise SystemExit(2)
    elif args.action == 'check':
        config = verify(args.root)
        print(json.dumps({'prepared': True, 'role': config['role'], 'model': config['model'],
                          'inference_admitted': False}))
    elif args.action == 'prepare':
        config = prepare(args.root, session=args.session, prompt=args.prompt, model=args.model,
            effort=args.effort, client=args.client, interpreter=args.interpreter,
            service_root=args.service_root, heavy_lock=args.heavy_lock,
            message=args.message_file.read_text(), media=args.media, compaction_probe=args.compaction_probe)
        print(json.dumps({'prepared': True, 'role': config['role'], 'model': config['model'],
                          'inference_admitted': False}))
    else:
        print(json.dumps(run(args.root, args.probe_message)))


if __name__ == '__main__':
    main()
