"""Offline client configuration, access-hook and event-accounting contracts."""
import json
import copy
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import structured_codex_client as client

DECLARATION = json.loads((Path(__file__).parent / "fixtures/codex_tool_declaration.json").read_text())


class HookTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.media = self.root / 'reference.png'
        self.media.write_bytes(b'\x89PNG\r\n\x1a\nfixture')
        self.policy = {'media': {str(self.media): client.sha(self.media)}}

    def decision(self, tool, args=None, event='PreToolUse'):
        return client.hook_decision(self.policy, {'hook_event_name': event, 'tool_name': tool,
                                                  'tool_input': args or {}})['hookSpecificOutput']['permissionDecision']

    def test_service_allowed_and_other_routes_denied(self):
        self.assertEqual(self.decision(client.TOOL), 'allow')
        for tool in ('Bash', 'exec_command', 'write_stdin', 'apply_patch', 'Read', 'read_file',
                     'Agent', 'spawn_agent', 'WebSearch', 'browser', 'mcp__other__operation',
                     'mcp__facts__shell', 'read_mcp_resource', 'request_permissions',
                     'mcp__facts__operation_extra', None):
            with self.subTest(tool=tool):
                self.assertEqual(self.decision(tool, {'command': 'fixture', 'file_path': str(self.media)}), 'deny')

    def test_missing_or_wrong_hook_event_denied(self):
        for event in ('PostToolUse', None, ''):
            with self.subTest(event=event):
                self.assertEqual(self.decision(client.TOOL, event=event), 'deny')
        with self.assertRaisesRegex(ValueError, '^CODEX_HOOK_SCHEMA$'):
            client.hook_decision(self.policy, [])

    def test_only_pinned_unchanged_media_allowed(self):
        self.assertEqual(self.decision('view_image', {'path': str(self.media)}), 'allow')
        other = self.root / 'secret.png'
        other.write_bytes(self.media.read_bytes())
        for path in (str(other), self.media.name, '', str(self.root / 'absent')):
            with self.subTest(path=path):
                self.assertEqual(self.decision('view_image', {'path': path}), 'deny')
        self.media.write_bytes(b'changed')
        self.assertEqual(self.decision('view_image', {'path': str(self.media)}), 'deny')

    def test_bad_image_arguments_deny(self):
        for value in (None, 42, [], {}):
            with self.subTest(value=value):
                self.assertEqual(self.decision('view_image', {'path': value}), 'deny')

    def test_broken_hook_input_policy_and_log_exit_two(self):
        policy = self.root / 'policy.json'
        policy.write_text(json.dumps({**self.policy, 'log': str(self.root / 'audit.jsonl')}))
        command = [sys.executable, '-B', client.__file__, 'hook', '--policy', str(policy)]
        request = {'hook_event_name': 'PreToolUse', 'tool_name': client.TOOL,
                   'tool_use_id': 'tool-1', 'session_id': 'thread-1', 'tool_input': {'operation': 'status'}}
        good = json.dumps(request)
        passed = subprocess.run(command, input=good, text=True, capture_output=True)
        self.assertEqual(passed.returncode, 0)
        self.assertEqual(json.loads(passed.stdout)['hookSpecificOutput']['permissionDecision'], 'allow')
        row = json.loads((self.root / 'audit.jsonl').read_text())
        self.assertEqual(row['tool_use_id'], 'tool-1')
        self.assertEqual(row['session_id'], 'thread-1')
        self.assertEqual(row['input_sha256'], client.hashlib.sha256(b'{"operation":"status"}').hexdigest())
        denied = {**request, 'tool_name': 'exec_command', 'tool_use_id': 'tool-2'}
        self.assertEqual(subprocess.run(command, input=json.dumps(denied), text=True, capture_output=True).returncode, 0)
        rows = [json.loads(line) for line in (self.root / 'audit.jsonl').read_text().splitlines()]
        self.assertEqual([(r['tool_use_id'], r['decision']) for r in rows], [('tool-1', 'allow'), ('tool-2', 'deny')])
        for data in ('not json', '[]'):
            with self.subTest(data=data):
                self.assertEqual(subprocess.run(command, input=data, text=True, capture_output=True).returncode, 2)
        policy.write_text(json.dumps({**self.policy, 'log': str(self.root / 'absent/audit.jsonl')}))
        self.assertEqual(subprocess.run(command, input=good, text=True, capture_output=True).returncode, 2)
        policy.unlink()
        self.assertEqual(subprocess.run(command, input=good, text=True, capture_output=True).returncode, 2)

    def test_symlink_cannot_replace_pinned_media(self):
        target = self.root / 'copy.png'
        target.write_bytes(self.media.read_bytes())
        self.media.unlink()
        self.media.symlink_to(target)
        self.assertEqual(self.decision('view_image', {'path': str(self.media)}), 'deny')


class ProfileFixture:
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.service = self.root / 'tooling'
        (self.service / 'scripts/structured_pass').mkdir(parents=True)
        (self.service / 'scripts/structured_pass_bridge.py').write_text('# bridge\n')
        (self.service / 'scripts/structured_pass/service.py').write_text('# service\n')
        self.session = self.root / 'session'
        (self.session / 'editor').mkdir(parents=True)
        (self.session / 'editor/state.json').write_text(json.dumps({'reader_hashes': {'fixture': 'pinned'},
            'candidates': {'existing': 'published'}}))
        self.prompt = self.root / 'prompt.md'
        self.prompt.write_text('Use the service.\n')
        self.client = self.root / 'client'
        self.client.write_bytes(b'not executable; preparation must not start it')
        self.code_host = self.root / 'codex-code-mode-host'
        self.code_host.write_bytes(b'installed but disabled synthetic host')
        self.profile = self.root / 'profile'
        self.config = client.prepare(self.profile, session=self.session, prompt=self.prompt, model='fixture-model',
            effort='xhigh', client=self.client, interpreter=sys.executable, service_root=self.service,
            heavy_lock=self.root / 'lock', message='Continue from status and the service report.')
        workspace = Path(self.config['workspace'])
        self.addCleanup(workspace.rmdir)


class ConfigurationTests(ProfileFixture, unittest.TestCase):
    def prepare_again(self, **overrides):
        args = dict(session=self.session, prompt=self.prompt, model='fixture-model', effort='xhigh',
            client=self.client, interpreter=sys.executable, service_root=self.service,
            heavy_lock=self.root / 'lock', message='fixture')
        args.update(overrides)
        return client.prepare(self.root / 'second-profile', **args)

    def test_invalid_preparation_inputs_refuse_before_writes(self):
        cases = [({'model': None}, 'MODEL_CONFIGURATION_REQUIRED'),
                 ({'model': ''}, 'MODEL_CONFIGURATION_REQUIRED'),
                 ({'effort': ' '}, 'MODEL_CONFIGURATION_REQUIRED'),
                 ({'message': None}, 'CODEX_MESSAGE_REQUIRED'),
                 ({'message': ''}, 'CODEX_MESSAGE_REQUIRED'),
                 ({'heavy_lock': Path('relative')}, 'SHARED_HEAVY_RUN_REQUIRED')]
        for args, code in cases:
            with self.subTest(args=args), self.assertRaisesRegex(ValueError, '^' + code + '$'):
                self.prepare_again(**args)
            self.assertFalse((self.root / 'second-profile').exists())
        bridge = self.service / 'scripts/structured_pass_bridge.py'
        original = bridge.read_bytes(); bridge.unlink()
        with self.assertRaisesRegex(ValueError, '^CODEX_SERVICE_MISSING$'): self.prepare_again()
        bridge.write_bytes(original)
        (self.session / 'editor/state.json').write_text('{"reader_hashes": null}')
        with self.assertRaisesRegex(ValueError, '^CODEX_SESSION_INVALID$'): self.prepare_again()

    def test_bad_and_duplicate_media_refuse_before_writes(self):
        first = self.root / 'reference.png'
        first.write_bytes(b'not a PNG')
        with self.assertRaisesRegex(ValueError, '^CODEX_MEDIA_REQUIRES_PNG$'):
            self.prepare_again(media=[first])
        first.write_bytes(b'\x89PNG\r\n\x1a\nfixture')
        other = self.root / 'other'; other.mkdir()
        second = other / first.name; second.write_bytes(first.read_bytes())
        with self.assertRaisesRegex(ValueError, '^CODEX_MEDIA_DUPLICATE$'):
            self.prepare_again(media=[first, second])
        self.assertFalse((self.root / 'second-profile').exists())

    def test_changed_or_symlinked_profile_media_refuse(self):
        first = self.root / 'reference.png'
        first.write_bytes(b'\x89PNG\r\n\x1a\nfixture')
        config = self.prepare_again(media=[first])
        workspace = Path(config['workspace']); target = workspace / first.name
        try:
            self.assertEqual(client.verify(self.root / 'second-profile'), config)
            target.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, '^CODEX_MEDIA_CHANGED$'): client.verify(self.root / 'second-profile')
            target.unlink(); target.symlink_to(first)
            with self.assertRaisesRegex(ValueError, '^CODEX_MEDIA_CHANGED$'): client.verify(self.root / 'second-profile')
        finally:
            target.unlink(); workspace.rmdir()

    def test_prepare_advanced_session_preserves_it_and_starts_unauthorized(self):
        self.assertEqual(json.loads((self.session / 'editor/state.json').read_text())['candidates'],
                         {'existing': 'published'})
        self.assertFalse(json.loads((self.profile / 'state.json').read_text())['authorized'])
        self.assertEqual(client.verify(self.profile), self.config)
        self.assertEqual(client.sha(self.session / 'editor/state.json'), self.config['initial_editor_sha256'])
        self.assertEqual(Path(self.config['workspace']), self.profile / 'workspace')
        with self.assertRaisesRegex(ValueError, '^CODEX_PROFILE_EXISTS$'):
            client.prepare(self.profile, session=self.session, prompt=self.prompt, model='fixture-model',
                effort='xhigh', client=self.client, interpreter=sys.executable,
                service_root=self.service, heavy_lock=self.root / 'lock', message='fixture')

    def test_configuration_disables_side_channels_and_fixes_mcp_role(self):
        config = json.loads((self.profile / 'config.json').read_text())
        roundtrip = tomllib.loads('\n'.join(json.dumps(k) + ' = ' + client.toml(v) for k, v in config.items()))
        self.assertEqual(roundtrip, config)
        self.assertEqual(config['approval_policy'], 'never')
        self.assertEqual(config['web_search'], 'disabled')
        self.assertEqual(config['permissions']['structured']['filesystem'][':root'], 'deny')
        self.assertFalse(config['permissions']['structured']['network']['enabled'])
        self.assertEqual(config['skills'], {'bundled': {'enabled': False}})
        self.assertEqual(config['agents'], {'enabled': False})
        self.assertFalse(config['include_collaboration_mode_instructions'])
        self.assertTrue(config['suppress_unstable_features_warning'])
        self.assertEqual(config['features']['code_mode'],
                         {'enabled': False, 'direct_only_tool_namespaces': ['mcp__facts']})
        for key in ('shell_tool', 'multi_agent', 'apps', 'plugins', 'browser_use', 'computer_use',
                    'image_generation', 'code_mode_host', 'memories', 'goals',
                    'request_permissions_tool', 'view_image', 'unified_exec', 'unified_exec_tty',
                    'daemon_auto_start', 'guardian_approval'):
            self.assertFalse(config['features'][key], key)
        self.assertTrue(config['features']['hooks'])
        self.assertEqual(set(config['mcp_servers']), {'facts'})
        server = config['mcp_servers']['facts']
        self.assertEqual(server['enabled_tools'], ['operation'])
        self.assertEqual(server['tools'], {'operation': {'approval_mode': 'approve'}})
        self.assertNotIn('default_tools_approval_mode',server)
        self.assertEqual(server['omit_tools_from'], ['deferred', 'code_mode'])
        self.assertTrue(server['required'])
        self.assertEqual(server['args'][-2:], ['implementer', 'corridor'])
        self.assertEqual(json.loads((self.profile/'policy.json').read_text())['session_home'],str(self.profile/'auth-config'))

    def test_unsupported_config_values_refuse(self):
        for value in (None, 1.5, object()):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, '^CODEX_CONFIG_VALUE$'):
                client.toml(value)

    def test_launch_and_resume_use_identical_overrides_and_no_shell(self):
        first = client.command(self.profile)
        resumed = client.command(self.profile, 'thread-fixture')
        self.assertEqual(resumed, first[:-1] + ['resume', 'thread-fixture', '-'])
        for flag in ('--strict-config', '--ignore-user-config', '--ignore-rules', '--json'):
            self.assertIn(flag, first)
        self.assertNotIn('--dangerously-bypass-approvals-and-sandbox', first)
        self.assertNotIn('--sandbox', first)  # Would override the named read restrictions.
        with self.assertRaisesRegex(ValueError, '^CODEX_THREAD_INVALID$'):
            client.command(self.profile, '--last')
        for identifier in ('', 1, True):
            with self.subTest(identifier=identifier), self.assertRaisesRegex(ValueError, '^CODEX_THREAD_INVALID$'):
                client.command(self.profile, identifier)

    def test_changed_pins_and_extra_workspace_file_refuse(self):
        for path in (self.client, self.profile / 'prompt.md', self.profile / 'config.json',
                     self.service / 'scripts/structured_pass/service.py'):
            before = path.read_bytes()
            path.write_bytes(before + b'changed')
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, '^CODEX_(CLIENT|CONFIGURATION)_CHANGED$'):
                client.verify(self.profile)
            path.write_bytes(before)
        extra = Path(self.config['workspace']) / 'extra'
        extra.write_text('not allowed')
        with self.assertRaisesRegex(ValueError, '^CODEX_WORKSPACE_CHANGED$'):
            client.verify(self.profile)
        extra.unlink()
        config = {**self.config, 'configuration_sha256': 'wrong'}
        client.save(self.profile / 'launch.json', config)
        with self.assertRaisesRegex(ValueError, '^CODEX_CONFIGURATION_CHANGED$'): client.verify(self.profile)

    def test_ambient_configuration_refused(self):
        for name in ('config.toml', 'hooks.json', 'skills', 'plugins'):
            path = self.profile / 'auth-config' / name
            path.write_text('unexpected')
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, '^CODEX_AMBIENT_CONFIGURATION$'):
                client.verify(self.profile)
            path.unlink()

    def test_client_managed_skills_allow_resume_but_user_skills_refuse(self):
        skills = self.profile / 'auth-config/skills'
        for name in ('imagegen', 'openai-docs', 'review-agent', 'skill-creator', 'skill-installer'):
            folder = skills / '.system' / name
            folder.mkdir(parents=True)
            (folder / 'SKILL.md').write_text('---\nname: '+name+'\n---\nBundled content.\n')
            (folder / 'agents').mkdir()
            (folder / 'agents/openai.yaml').write_text('interface: {}\n')
        (skills / '.system/.codex-system-skills.marker').write_text('client marker')
        self.assertEqual(client.verify(self.profile), self.config)
        self.assertIn('resume', client.command(self.profile, 'thread-fixture'))
        for name in ('user-skill', '.unexpected'):
            extra = skills / name; extra.mkdir()
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, '^CODEX_AMBIENT_CONFIGURATION$'):
                client.verify(self.profile)
            extra.rmdir()

    def test_ambient_symlinks_and_fake_system_file_refuse(self):
        home = self.profile / 'auth-config'; skills = home / 'skills'
        skills.symlink_to(self.root / 'missing', target_is_directory=True)
        with self.assertRaisesRegex(ValueError, '^CODEX_AMBIENT_CONFIGURATION$'): client.verify(self.profile)
        skills.unlink(); skills.mkdir()
        system = skills / '.system'; system.write_text('not a directory')
        with self.assertRaisesRegex(ValueError, '^CODEX_AMBIENT_CONFIGURATION$'): client.verify(self.profile)
        system.unlink(); system.symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, '^CODEX_AMBIENT_CONFIGURATION$'): client.verify(self.profile)
        system.unlink()
        for name in ('config.toml', 'hooks.json', 'plugins'):
            path = home / name; path.symlink_to(self.root / 'missing')
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, '^CODEX_AMBIENT_CONFIGURATION$'):
                client.verify(self.profile)
            path.unlink()

    def test_native_full_feature_inventory_refuses_any_drift(self):
        rows = [{'name': name, 'enabled': True} for name in sorted(client.ENABLED_FEATURES)]
        self.assertEqual(client.check_native_features(rows), sorted(client.ENABLED_FEATURES))
        self.assertEqual(client.check_native_features(rows + [{'name': 'view_image', 'enabled': True}], True),
                         sorted(client.ENABLED_FEATURES | {'view_image'}))
        for bad in (rows[:-1], rows + [{'name': 'new_default_tool', 'enabled': True}],
                    rows + [{'name': 'unified_exec_tty', 'enabled': True}]):
            with self.subTest(bad=bad[-1]), self.assertRaisesRegex(ValueError, '^CODEX_FEATURE_SET_CHANGED$'):
                client.check_native_features(bad)
        for bad in (None, {}, [None], [{'enabled': True}], [{'name': 'hooks', 'enabled': 1}], rows + [rows[0]]):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, '^CODEX_FEATURE_SCHEMA$'):
                client.check_native_features(bad)

    def test_missing_workspace_is_a_typed_refusal(self):
        workspace = Path(self.config['workspace'])
        workspace.rmdir()
        try:
            with self.assertRaisesRegex(ValueError, '^CODEX_WORKSPACE_CHANGED$'): client.verify(self.profile)
        finally:
            workspace.mkdir()

    def test_secrets_not_inherited_by_environment(self):
        with patch.dict(os.environ, {'OPENAI_API_KEY': 'canary', 'ANTHROPIC_API_KEY': 'canary',
                                    'CODEX_HOME': '/untrusted', 'PYTHONPATH': '/untrusted'}):
            environment = client.environment(self.profile)
        self.assertNotIn('OPENAI_API_KEY', environment)
        self.assertNotIn('ANTHROPIC_API_KEY', environment)
        self.assertNotIn('PYTHONPATH', environment)
        self.assertEqual(environment['CODEX_HOME'], str(self.profile / 'auth-config'))
        self.assertEqual(environment['GIT_CEILING_DIRECTORIES'],str(self.profile))


class RunnerTests(ProfileFixture, unittest.TestCase):
    def fake(self, mode='success'):
        program = '''#!INTERPRETER
import json,sys,time,os
from pathlib import Path
if sys.argv[-2:]==['login','status']:
 print('Logged in using ChatGPT');sys.exit(0)
sys.stdin.read()
folder=Path(os.environ['CODEX_HOME'])/'sessions';folder.mkdir(exist_ok=True)
(folder/'rollout-fixture.jsonl').write_text(json.dumps({'type':'session_meta','payload':{'id':'thread-fixture'}})+'\\n'+json.dumps({'type':'response_item','payload':{'type':'additional_tools','id':'tools-fixture','tools':json.loads(DECLARATION_TEXT)}})+'\\n')
def emit(x):print(json.dumps(x),flush=True)
emit({'type':'thread.started','thread_id':'thread-fixture'})
emit({'type':'turn.started'})
MODE_CODE
'''.replace('INTERPRETER', sys.executable).replace('DECLARATION_TEXT', repr(json.dumps(DECLARATION)))
        endings = {
            'success': "emit({'type':'turn.completed','usage':{'input_tokens':1200,'cached_input_tokens':900,'output_tokens':1000000}})",
            'quota': "emit({'type':'turn.failed','error':{'message':'quota reached'}});sys.exit(1)",
            'partial': "sys.stdout.write('{');sys.stdout.flush()",
            'hang': "sys.stdout.write('{');sys.stdout.flush();time.sleep(30)",
            'wrong_tool': "emit({'type':'item.started','item':{'type':'command_execution'}})",
            'nonfatal_error': "emit({'type':'item.completed','item':{'type':'error','message':'denied probe'}})",
            'bad_offered_tools': "p=folder/'rollout-fixture.jsonl';p.write_text(p.read_text().replace('operation','not_allowed'));emit({'type':'turn.completed','usage':{'input_tokens':1,'cached_input_tokens':0,'output_tokens':1}})",
            'silent_call': "p=folder/'rollout-fixture.jsonl';p.write_text(p.read_text()+json.dumps({'type':'response_item','payload':{'type':'custom_tool_call','name':'exec','call_id':'forbidden'}})+'\\n');emit({'type':'turn.completed','usage':{'input_tokens':1,'cached_input_tokens':0,'output_tokens':1}})",
            'silent_call_halt': "p=folder/'rollout-fixture.jsonl';p.write_text(p.read_text()+json.dumps({'type':'response_item','payload':{'type':'custom_tool_call','name':'exec','call_id':'forbidden'}})+'\\n');sys.exit(3)",
            'silent_deny': "(Path(os.environ['CODEX_HOME']).parent/'hooks.jsonl').write_text(json.dumps({'decision':'deny','tool':'functions__wait'})+'\\n');time.sleep(30)",
            'nonzero': "emit({'type':'turn.completed','usage':{'input_tokens':1,'cached_input_tokens':0,'output_tokens':1}});sys.exit(7)",
            'unfinished': 'pass',
            'trailing': "emit({'type':'turn.completed','usage':{'input_tokens':1,'cached_input_tokens':0,'output_tokens':1}});sys.stdout.write('{')",
            'oversize': "sys.stdout.write('x'*(9*1024*1024));sys.stdout.flush()",
        }
        self.client.write_text(program.replace('MODE_CODE', endings[mode]))
        self.client.chmod(0o700)
        self.config['client_sha256'] = client.sha(self.client)
        client.save(self.profile / 'launch.json', self.config)
        client.save(self.profile / 'authorization.json', {
            'authorized': True, 'owner_message': 'synthetic offline test only',
            'launch_sha256': client.sha(self.profile / 'launch.json'), 'purpose': 'access_preflight',
            'token_response_caps': 'none_usage_reporting_only', 'deadline': time.time() + 20})

    def invoke(self, probe_message=None):
        with patch.dict(os.environ, {'NESREV_HEAVY_RUN_LOCK': str(self.root / 'lock'), 'NESREV_HEAVY_RUN_ID': 'synthetic'}):
            return client.run(self.profile, probe_message)

    def test_run_and_resume_preserve_native_thread_and_usage(self):
        self.fake()
        with patch.object(client,'stop_group',side_effect=AssertionError('exited root signalled again')):
            first = self.invoke()
            second = self.invoke()
        self.assertEqual(first['status'], 'finished')
        self.assertFalse(first['continuation'])
        self.assertTrue(second['continuation'])
        state = json.loads((self.profile / 'state.json').read_text())
        self.assertEqual(state['thread_id'], 'thread-fixture')
        self.assertEqual(len(state['runs']), 2)
        self.assertFalse(state['halted'])
        self.assertTrue(all(r['processes_reconciled'] is True for r in state['runs']))
        self.assertEqual(state['runs'][0]['native_turns'][0]['usage']['output_tokens'], 1000000)
        self.assertNotIn('charged', state['runs'][0])

    def test_private_forbidden_call_halts_while_stdout_is_silent(self):
        self.fake('silent_call')
        program=self.client.read_text().replace("emit({'type':'turn.completed','usage':{'input_tokens':1,'cached_input_tokens':0,'output_tokens':1}})","time.sleep(30)")
        self.client.write_text(program);self.config['client_sha256']=client.sha(self.client)
        client.save(self.profile/'launch.json',self.config)
        auth=json.loads((self.profile/'authorization.json').read_text());auth['launch_sha256']=client.sha(self.profile/'launch.json')
        client.save(self.profile/'authorization.json',auth)
        start=time.monotonic()
        with self.assertRaisesRegex(ValueError,'^CODEX_FORBIDDEN_SESSION_CALL$'):self.invoke()
        self.assertLess(time.monotonic()-start,3)
        state=json.loads((self.profile/'state.json').read_text())
        self.assertTrue(state['halted']);self.assertEqual(state['runs'][0]['native_turns'],[])

    def test_separate_child_group_is_recorded_and_killed_before_late_write(self):
        self.fake('wrong_tool');marker=self.root/'late-write';pidfile=self.root/'child-pid'
        program=self.client.read_text().replace("emit({'type':'item.started','item':{'type':'command_execution'}})",
            "import subprocess\np=subprocess.Popen([sys.executable,'-c',"+repr("import time,signal;from pathlib import Path;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(2);Path("+repr(str(marker))+").write_text('late')")+"],start_new_session=True)\nPath("+repr(str(pidfile))+").write_text(str(p.pid))\ntime.sleep(.3)\nemit({'type':'item.started','item':{'type':'command_execution'}})\ntime.sleep(30)")
        self.client.write_text(program);self.config['client_sha256']=client.sha(self.client);client.save(self.profile/'launch.json',self.config)
        auth=json.loads((self.profile/'authorization.json').read_text());auth['launch_sha256']=client.sha(self.profile/'launch.json');client.save(self.profile/'authorization.json',auth)
        try:
            with self.assertRaisesRegex(ValueError,'CODEX_UNEXPECTED_TOOL_EVENT'):self.invoke()
            pid=int(pidfile.read_text());state=json.loads((self.profile/'state.json').read_text());row=state['runs'][0]
            self.assertIn(pid,[v['pgid'] for v in row['processes']]);self.assertNotEqual(pid,row['client_pgid'])
            self.assertFalse(client.group_alive(pid));self.assertFalse(marker.exists())
        finally:
            if pidfile.exists() and client.group_alive(int(pidfile.read_text())):os.killpg(int(pidfile.read_text()),signal.SIGKILL)

    def test_orphan_bridge_refuses_new_phase_by_exact_session(self):
        self.fake()
        bridge=self.service/'scripts/structured_pass_bridge.py'
        bridge.write_text('import time;time.sleep(30)\n')
        self.config['files'][str(bridge)]=client.sha(bridge);client.save(self.profile/'launch.json',self.config)
        auth=json.loads((self.profile/'authorization.json').read_text());auth['launch_sha256']=client.sha(self.profile/'launch.json');client.save(self.profile/'authorization.json',auth)
        p=subprocess.Popen([sys.executable,'-B',str(bridge),'--mcp',str(self.session),'implementer','corridor'],start_new_session=True)
        try:
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_BRIDGE_ALIVE$'):self.invoke()
            self.assertEqual(json.loads((self.profile/'state.json').read_text())['runs'],[])
        finally:
            os.killpg(p.pid,signal.SIGKILL);p.wait()

    def test_recorded_child_blocks_after_adapter_and_client_are_killed(self):
        self.fake('hang');pidfile=self.root/'independent-child'
        program=self.client.read_text().replace("sys.stdout.write('{');sys.stdout.flush();time.sleep(30)",
            "import subprocess\np=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)'],start_new_session=True)\nPath("+repr(str(pidfile))+").write_text(str(p.pid))\ntime.sleep(30)")
        self.client.write_text(program);self.config['client_sha256']=client.sha(self.client);client.save(self.profile/'launch.json',self.config)
        auth=json.loads((self.profile/'authorization.json').read_text());auth['launch_sha256']=client.sha(self.profile/'launch.json');client.save(self.profile/'authorization.json',auth)
        env={**os.environ,'NESREV_HEAVY_RUN_LOCK':str(self.root/'lock'),'NESREV_HEAVY_RUN_ID':'synthetic'}
        pgid=None
        with (self.root/'killed-adapter.log').open('w') as log:
            p=subprocess.Popen([sys.executable,'-B',client.__file__,'run','--root',str(self.profile)],env=env,stdout=log,stderr=log,start_new_session=True)
            try:
                until=time.monotonic()+5
                while time.monotonic()<until:
                    state=json.loads((self.profile/'state.json').read_text())
                    if state['runs']:
                        pgid=state['runs'][0].get('client_pgid')
                        if pidfile.exists() and int(pidfile.read_text()) in [v['pid'] for v in state['runs'][0].get('processes',[])]:break
                    time.sleep(.02)
                self.assertTrue(pidfile.exists());child=int(pidfile.read_text())
                self.assertIn(child,[v['pid'] for v in state['runs'][0].get('processes',[])])
                os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=2);os.killpg(pgid,signal.SIGKILL)
                until=time.monotonic()+2
                while client.group_alive(pgid) and time.monotonic()<until:time.sleep(.02)
                self.assertFalse(client.group_alive(pgid));self.assertTrue(client.group_alive(child))
                with self.assertRaisesRegex(ValueError,'^CODEX_DESCENDANT_ALIVE$'):self.invoke()
            finally:
                if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait()
                for child in ([pgid] if pgid else [])+([int(pidfile.read_text())] if pidfile.exists() else []):
                    if client.group_alive(child):os.killpg(child,signal.SIGKILL)

    def test_no_admission_starts_no_process(self):
        with patch.object(client.process_tree, 'snapshot', return_value={}), patch.object(client.subprocess, 'Popen') as spawn:
            with self.assertRaisesRegex(ValueError, '^CODEX_INFERENCE_NOT_AUTHORIZED$'):
                self.invoke()
            spawn.assert_not_called()

    def test_extra_offered_tools_halt_and_are_retained_as_names_only(self):
        self.fake('bad_offered_tools')
        with self.assertRaisesRegex(ValueError, '^CODEX_OFFERED_TOOLS_CHANGED$'): self.invoke()
        state = json.loads((self.profile / 'state.json').read_text())
        self.assertTrue(state['halted'])
        rows = json.loads((self.profile/'runs'/state['runs'][0]['id']/'offered-tools.json').read_text())
        self.assertEqual(rows[0]['names'][-1], 'mcp__facts__not_allowed')
        self.assertNotIn('description', str(rows))

    def test_admission_refusals_happen_before_client_start(self):
        self.fake()
        path = self.profile / 'authorization.json'
        original = json.loads(path.read_text())
        cases = [('authorized', False, 'CODEX_INFERENCE_NOT_AUTHORIZED'),
                 ('owner_message', '', 'CODEX_INFERENCE_NOT_AUTHORIZED'),
                 ('launch_sha256', 'wrong', 'CODEX_AUTHORIZATION_CHANGED'),
                 ('purpose', 'unknown', 'CODEX_AUTHORIZATION_PURPOSE'),
                 ('token_response_caps', 'old', 'CODEX_USAGE_POLICY_CHANGED'),
                 ('deadline', time.time()-1, 'CODEX_DEADLINE_EXPIRED'),
                 ('deadline', 'tomorrow', 'CODEX_DEADLINE_EXPIRED'),
                 ('purpose', 'pilot_takeover', 'CODEX_ADMISSION_EVIDENCE_REQUIRED')]
        for key, value, error in cases:
            client.save(path, {**original, key: value})
            with self.subTest(key=key), patch.object(client.subprocess, 'Popen') as spawn:
                with self.assertRaisesRegex(ValueError, '^' + error + '$'): self.invoke()
                spawn.assert_not_called()
        client.save(path, original)
        with patch.dict(os.environ, {'NESREV_HEAVY_RUN_LOCK': '/wrong'}), patch.object(client.subprocess, 'Popen') as spawn:
            with self.assertRaisesRegex(ValueError, '^SHARED_HEAVY_RUN_REQUIRED$'): client.run(self.profile)
            spawn.assert_not_called()

    def test_takeover_evidence_pins_are_required_independently(self):
        self.fake()
        path = self.profile / 'authorization.json'
        authority = json.loads(path.read_text()); authority['purpose'] = 'pilot_takeover'
        evidence = self.root / 'review.json'; evidence.write_text('{"verdict":"synthetic"}')
        pin = {'path': str(evidence), 'sha256': client.sha(evidence)}
        authority.update(access_preflight=pin, transition_review=pin)
        client.save(path, authority)
        with patch.dict(os.environ, {'NESREV_HEAVY_RUN_LOCK': str(self.root / 'lock')}):
            self.assertEqual(client.admission(self.profile, self.config), authority)
            for name in ('access_preflight', 'transition_review'):
                for bad in (None, {'path': None}, {'path': str(self.root / 'missing'), 'sha256': pin['sha256']},
                            {**pin, 'sha256': 'wrong'}):
                    client.save(path, {**authority, name: bad})
                    with self.subTest(name=name, bad=bad), self.assertRaisesRegex(ValueError, '^CODEX_ADMISSION_EVIDENCE_REQUIRED$'):
                        client.admission(self.profile, self.config)

    def test_wrong_or_failed_authentication_refuses(self):
        for code, stdout, stderr in ((1, 'Logged in using ChatGPT', ''), (0, 'API key', ''), (0, '', 'Not logged in')):
            result = subprocess.CompletedProcess([], code, stdout, stderr)
            with self.subTest(code=code, text=stdout), patch.object(client.subprocess, 'run', return_value=result):
                with self.assertRaisesRegex(ValueError, '^CODEX_SUBSCRIPTION_LOGIN_REQUIRED$'):
                    client.authenticate(self.profile, self.config)

    def test_stale_running_reservation_blocks_resume(self):
        self.fake()
        client.save(self.profile / 'state.json', {'thread_id': None, 'runs': [{'status': 'running'}]})
        with self.assertRaisesRegex(ValueError, '^CODEX_RECOVERY_REQUIRED$'): self.invoke()

    def test_concurrent_phase_refuses(self):
        import fcntl
        self.fake()
        with (self.profile / 'run.lock').open('a+b') as held:
            fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaisesRegex(ValueError, '^CODEX_ALREADY_RUNNING$'): self.invoke()

    def test_changed_initial_handoff_starts_no_client(self):
        self.fake()
        (self.session / 'editor/state.json').write_text('{"changed":true}')
        with patch.object(client.process_tree, 'snapshot', return_value={}), patch.object(client.subprocess, 'Popen') as spawn:
            with self.assertRaisesRegex(ValueError, '^CODEX_HANDOFF_CHANGED$'): self.invoke()
            spawn.assert_not_called()

    def test_each_stream_completion_guard_independently(self):
        for mode, code in (('nonzero', 'CODEX_CLIENT_FAILED'), ('unfinished', 'CODEX_STREAM_INCOMPLETE'),
                           ('trailing', 'CODEX_PARTIAL_EVENT'), ('oversize', 'CODEX_EVENT_TOO_LARGE')):
            self.fake(mode)
            client.save(self.profile / 'state.json', {'thread_id': None, 'runs': []})
            with self.subTest(mode=mode), self.assertRaisesRegex(ValueError, '^' + code + '$'): self.invoke()

    def test_failures_preserve_logs_and_block_automatic_resume(self):
        for mode in ('quota', 'partial', 'wrong_tool', 'nonfatal_error'):
            self.fake(mode)
            client.save(self.profile / 'state.json', {'thread_id': None, 'runs': []})
            with self.subTest(mode=mode), self.assertRaises(ValueError): self.invoke()
            state = json.loads((self.profile / 'state.json').read_text())
            self.assertTrue(state['halted'])
            self.assertEqual(state['runs'][0]['status'], 'interrupted')
            self.assertTrue(state['runs'][0]['usage_uncertain'])
            self.assertIsNotNone(state['runs'][0]['exit_code'])
            self.assertEqual(state['runs'][0]['audit_errors'], [])
            self.assertTrue((self.profile / 'runs' / state['runs'][0]['id'] / 'stdout.jsonl').is_file())
            self.assertTrue((self.profile / 'runs' / state['runs'][0]['id'] / 'offered-tools.json').is_file())
            with self.assertRaisesRegex(ValueError, '^CODEX_RECOVERY_REQUIRED$'): self.invoke()

    def test_deadline_interrupts_even_partial_json(self):
        self.fake('hang')
        path = self.profile / 'authorization.json'
        authority = json.loads(path.read_text())
        authority['deadline'] = time.time() + .4
        client.save(path, authority)
        started = time.monotonic()
        with self.assertRaisesRegex(ValueError, '^CODEX_DEADLINE_EXPIRED$'): self.invoke()
        self.assertLess(time.monotonic() - started, 4)
        state = json.loads((self.profile / 'state.json').read_text())
        self.assertEqual(state['runs'][0]['status'], 'interrupted')
        self.assertNotEqual(state['runs'][0]['exit_code'], 0)

    def test_hook_deny_without_any_stdout_stops_group(self):
        self.fake('silent_deny')
        program = self.client.read_text()
        program = program.replace("emit({'type':'thread.started','thread_id':'thread-fixture'})", '')
        program = program.replace("emit({'type':'turn.started'})", '')
        # A child ignores TERM and would leave a marker if only the parent died.
        marker = self.root / 'child-survived'
        child = "import signal,time;from pathlib import Path;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(1);Path("+repr(str(marker))+").write_text('survived')"
        program = program.replace("time.sleep(30)", "time.sleep(5)")
        program = program.replace("(Path(os.environ['CODEX_HOME']).parent/'hooks.jsonl')",
            "__import__('subprocess').Popen([sys.executable,'-c',"+repr(child)+"]);time.sleep(.1);(Path(os.environ['CODEX_HOME']).parent/'hooks.jsonl')")
        self.client.write_text(program)
        self.config['client_sha256'] = client.sha(self.client)
        client.save(self.profile / 'launch.json', self.config)
        auth = json.loads((self.profile/'authorization.json').read_text())
        auth['launch_sha256'] = client.sha(self.profile/'launch.json')
        client.save(self.profile/'authorization.json', auth)
        started = time.monotonic()
        with self.assertRaisesRegex(ValueError, '^CODEX_HOOK_DENIED$'): self.invoke()
        self.assertLess(time.monotonic()-started, 3)
        state = json.loads((self.profile/'state.json').read_text())
        folder = self.profile/'runs'/state['runs'][0]['id']
        self.assertEqual((folder/'stdout.jsonl').read_bytes(), b'')
        self.assertTrue(state['halted'])
        self.assertEqual(json.loads((folder/'session-audit.json').read_text())['thread_id'], 'thread-fixture')
        time.sleep(1.1)
        self.assertFalse(marker.exists())

    def test_session_only_call_refuses_success_and_is_audited_on_halt(self):
        for mode, code in (('silent_call','CODEX_FORBIDDEN_SESSION_CALL'),('silent_call_halt','CODEX_FORBIDDEN_SESSION_CALL|CODEX_CLIENT_FAILED')):
            self.fake(mode)
            client.save(self.profile/'state.json', {'thread_id':None,'runs':[]})
            with self.subTest(mode=mode), self.assertRaisesRegex(ValueError, '^'+code+'$'): self.invoke()
            state = json.loads((self.profile/'state.json').read_text())
            folder = self.profile/'runs'/state['runs'][0]['id']
            audit = json.loads((folder/'session-audit.json').read_text())
            self.assertEqual(audit['calls'], [{'call_id':'forbidden','name':'functions__exec',
                'namespace':'functions','tool':'exec','declared_type':'custom',
                'observed':{'name':'exec','type':'custom_tool_call'},'allowed':False}])
            self.assertIn('CODEX_FORBIDDEN_SESSION_CALL', state['runs'][0]['audit_errors'])
            self.assertTrue(state['halted'])

    def test_probe_message_requires_preflight_and_exact_phase_pin(self):
        self.fake()
        message = self.root/'probe.txt';message.write_text('Attempt one synthetic denied tool.')
        auth = json.loads((self.profile/'authorization.json').read_text())
        probe = {'path':str(message),'sha256':client.sha(message),'tool':'functions__exec','resume':False}
        auth['probe'] = probe
        self.assertEqual(client.phase_message(self.profile, auth, None, message), message.read_bytes())
        for purpose in ('pilot_takeover','other'):
            for passed in (message,None):
                with self.subTest(purpose=purpose, passed=passed), self.assertRaisesRegex(ValueError,'^CODEX_PROBE_FORBIDDEN$'):
                    client.phase_message(self.profile, {**auth,'purpose':purpose}, None, passed)
        for bad in (None,12,{}, {**probe,'path':'wrong'}, {**probe,'sha256':'wrong'},
                    {**probe,'tool':client.TOOL},{**probe,'resume':True},{**probe,'resume':0}):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError,'^CODEX_PROBE_AUTHORIZATION$'):
                client.phase_message(self.profile,{**auth,'probe':bad}, None,message)
        with self.assertRaisesRegex(ValueError,'^CODEX_PROBE_AUTHORIZATION$'):
            client.phase_message(self.profile,auth,None,None)
        with self.assertRaisesRegex(ValueError,'^CODEX_PROBE_AUTHORIZATION$'):
            client.phase_message(self.profile,auth,'existing-thread',message)
        resumed = {**auth,'probe':{**probe,'resume':True}}
        self.assertEqual(client.phase_message(self.profile,resumed,'existing-thread',message),message.read_bytes())
        # Exercise the production runner fence even with all takeover evidence valid.
        evidence=self.root/'accepted.json';evidence.write_text('{}')
        pin={'path':str(evidence),'sha256':client.sha(evidence)}
        auth.update(purpose='pilot_takeover',access_preflight=pin,transition_review=pin)
        client.save(self.profile/'authorization.json',auth)
        with patch.object(client.process_tree,'snapshot',return_value={}), patch.object(client.subprocess,'Popen') as spawn, patch.dict(os.environ,{'NESREV_HEAVY_RUN_LOCK':str(self.root/'lock')}):
            with self.assertRaisesRegex(ValueError,'^CODEX_PROBE_FORBIDDEN$'):client.run(self.profile,message)
            spawn.assert_not_called()

    def test_preflight_phase_timeout_is_distinct_from_shared_deadline(self):
        self.fake('hang')
        self.client.write_text(self.client.read_text().replace('time.sleep(30)','time.sleep(.5)'))
        self.config['client_sha256']=client.sha(self.client);client.save(self.profile/'launch.json',self.config)
        real_time=time.time
        times=iter([real_time(),real_time(),real_time(),real_time()+181,real_time()+181])
        auth=json.loads((self.profile/'authorization.json').read_text());auth['deadline']=real_time()+1000
        auth['launch_sha256']=client.sha(self.profile/'launch.json')
        message=self.root/'probe.txt';message.write_text('Synthetic denial.')
        auth['probe']={'path':str(message),'sha256':client.sha(message),'tool':'functions__exec','resume':False}
        client.save(self.profile/'authorization.json',auth)
        with patch.object(client.time,'time',side_effect=lambda:next(times,real_time()+181)):
            with self.assertRaisesRegex(ValueError,'^CODEX_PHASE_TIMEOUT$'):self.invoke(message)

    def test_functional_phase_can_run_past_three_minutes(self):
        self.fake()
        now=time.time();auth=json.loads((self.profile/'authorization.json').read_text());auth['deadline']=now+1000
        client.save(self.profile/'authorization.json',auth)
        times=iter([now,now,now])
        with patch.object(client.time,'time',side_effect=lambda:next(times,now+181)):
            result=self.invoke()
        self.assertEqual(result['status'],'finished')
        self.assertEqual(result['phase_deadline'],auth['deadline'])
        self.assertEqual(client.phase_expiry({**auth,'probe':{}},now),now+180)
        self.assertEqual(client.phase_expiry({**auth,'probe':{},'deadline':now+60},now),now+60)
        self.assertEqual(client.phase_expiry({**auth,'purpose':'pilot_takeover'},now),auth['deadline'])

    def test_signalled_silent_adapter_reaps_client_and_persists_group(self):
        self.fake('hang')
        heartbeat=self.root/'heartbeat'
        child_pid=self.root/'child-pid'
        program=self.client.read_text()
        program=program.replace("emit({'type':'thread.started','thread_id':'thread-fixture'})",'')
        program=program.replace("emit({'type':'turn.started'})",'')
        program=program.replace("sys.stdout.write('{');sys.stdout.flush();time.sleep(30)",
            'Path('+repr(str(child_pid))+').write_text(str(os.getpid()))\nwhile True:\n Path('+repr(str(heartbeat))+').write_text(str(time.time()))\n time.sleep(.05)')
        self.client.write_text(program);self.config['client_sha256']=client.sha(self.client)
        client.save(self.profile/'launch.json',self.config)
        auth=json.loads((self.profile/'authorization.json').read_text());auth['launch_sha256']=client.sha(self.profile/'launch.json')
        client.save(self.profile/'authorization.json',auth)
        env={**os.environ,'NESREV_HEAVY_RUN_LOCK':str(self.root/'lock'),'NESREV_HEAVY_RUN_ID':'synthetic'}
        for sig in (signal.SIGTERM,signal.SIGHUP,signal.SIGINT,signal.SIGKILL):
            client.save(self.profile/'state.json',{'thread_id':None,'runs':[]});heartbeat.unlink(missing_ok=True);child_pid.unlink(missing_ok=True)
            pgid=None
            with (self.root/'adapter.log').open('w') as log:
                proc=subprocess.Popen([sys.executable,'-B',client.__file__,'run','--root',str(self.profile)],
                    env=env,stdout=log,stderr=log,start_new_session=True)
                try:
                    deadline=time.monotonic()+5
                    while time.monotonic()<deadline and not heartbeat.exists() and proc.poll() is None:time.sleep(.01)
                    self.assertTrue(heartbeat.exists())
                    state=json.loads((self.profile/'state.json').read_text())
                    pgid=state['runs'][0]['client_pgid']
                    self.assertTrue(client.group_alive(pgid))
                    self.assertEqual((self.profile/'runs'/state['runs'][0]['id']/'stdout.jsonl').read_bytes(),b'')
                    os.killpg(proc.pid,sig);proc.wait(timeout=2)
                    state=json.loads((self.profile/'state.json').read_text())
                    if sig==signal.SIGKILL:
                        self.assertTrue(client.group_alive(pgid))
                        with self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_ALIVE$'):self.invoke()
                    else:
                        self.assertNotEqual(proc.returncode,-sig)
                        self.assertFalse(client.group_alive(pgid))
                        self.assertTrue(state['halted'])
                        self.assertEqual(state['runs'][0]['status'],'interrupted')
                        self.assertIn(signal.Signals(sig).name,state['runs'][0]['error'])
                        before=heartbeat.read_bytes();time.sleep(.1);self.assertEqual(heartbeat.read_bytes(),before)
                finally:
                    if proc.poll() is None:os.killpg(proc.pid,signal.SIGKILL);proc.wait(timeout=2)
                    if pgid is None and child_pid.exists():pgid=int(child_pid.read_text())
                    if pgid is not None and client.group_alive(pgid):os.killpg(pgid,signal.SIGKILL)

    def test_group_liveness_and_signal_handlers_fail_closed_and_restore(self):
        for bad in (None,True,0,1,'123'):
            with self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_INVALID$'):client.group_alive(bad)
        for effect,expected in ((None,True),(PermissionError(),True),(ProcessLookupError(),False)):
            with patch.object(client.os,'killpg',side_effect=effect):self.assertEqual(client.group_alive(123456),expected)
        row={'pid':123456,'pgid':123456,'started':'start'}
        with patch.object(client.process_tree,'snapshot',return_value={123456:row}):
            with self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_ALIVE$'):
                client.require_quiescent_runs({'runs':[{'status':'finished','client_pgid':123456}]})
        before={s:signal.getsignal(s) for s in (signal.SIGTERM,signal.SIGHUP,signal.SIGINT)}
        with client.termination_handlers() as status:
            status['cleaning']=True
            signal.getsignal(signal.SIGTERM)(signal.SIGTERM,None)
            self.assertEqual(status['signal'],signal.SIGTERM)
        self.assertEqual({s:signal.getsignal(s) for s in before},before)
        with client.termination_handlers() as status:
            captured=[]
            with self.assertRaisesRegex(client.ClientSignal,'^CODEX_TERMINATED:SIGTERM$'):
                with client.defer_termination(status):
                    signal.getsignal(signal.SIGTERM)(signal.SIGTERM,None)
                    captured.append('PGID saved before raising')
            self.assertEqual(captured,['PGID saved before raising'])
            self.assertFalse(status['deferring'])

    def test_cleanup_failure_is_preserved_and_blocks_resume(self):
        self.fake()
        with patch.object(client.process_tree,'stop_tree',side_effect=PermissionError('synthetic cleanup refusal')):
            with self.assertRaisesRegex(ValueError,'^CODEX_PROCESS_CLEANUP_FAILED:'):self.invoke()
        state=json.loads((self.profile/'state.json').read_text())
        self.assertTrue(state['halted'])
        self.assertNotIn('processes_reconciled',state['runs'][0])
        self.assertIn('CODEX_PROCESS_CLEANUP_FAILED',state['runs'][0]['error'])
        with self.assertRaisesRegex(ValueError,'^CODEX_RECOVERY_REQUIRED$'):self.invoke()

    def test_deadline_expiring_during_login_starts_no_phase(self):
        self.fake()
        auth=json.loads((self.profile/'authorization.json').read_text())
        times=iter([auth['deadline']-1,auth['deadline']+1])
        with patch.object(client.process_tree,'snapshot',return_value={}), patch.object(client,'authenticate'), patch.object(client.time,'time',side_effect=lambda:next(times,auth['deadline']+1)), patch.object(client.subprocess,'Popen',side_effect=AssertionError('phase launched after expiry')) as spawn:
            with self.assertRaisesRegex(ValueError,'^CODEX_DEADLINE_EXPIRED$'):self.invoke()
            spawn.assert_not_called()
        self.assertEqual(json.loads((self.profile/'state.json').read_text())['runs'],[])


class EventTests(unittest.TestCase):
    def start(self, thread=None):
        events = client.Events(thread)
        events.accept({'type': 'thread.started', 'thread_id': 'thread-fixture'})
        events.accept({'type': 'turn.started'})
        return events

    def finish(self, events):
        events.accept({'type': 'turn.completed', 'usage': {
            'input_tokens': 1200, 'cached_input_tokens': 900, 'output_tokens': 70}})

    def test_multiple_items_are_one_native_turn_not_response_count(self):
        events = self.start('thread-fixture')
        for kind in ('item.started', 'item.updated', 'item.completed'):
            events.accept({'type': kind, 'item': {'id': 'item_1', 'type': 'mcp_tool_call',
                          'server': 'facts', 'tool': 'operation'}})
        for kind in ('reasoning', 'agent_message'):
            events.accept({'type': 'item.completed', 'item': {'id': kind, 'type': kind}})
        self.finish(events)
        self.assertTrue(events.complete())
        self.assertEqual(len(events.turns), 1)
        self.assertEqual(events.turns[0]['usage']['output_tokens'], 70)

    def test_error_failure_and_interruption_do_not_count_as_complete(self):
        events = self.start()
        self.assertFalse(events.complete())
        events.accept({'type': 'turn.failed', 'error': {'message': 'quota reached'}})
        self.assertFalse(events.complete())
        self.assertEqual(events.error, {'message': 'quota reached'})
        events = self.start()
        self.finish(events)
        events.accept({'type': 'error', 'message': 'transport failed'})
        self.assertFalse(events.complete())

    def test_resume_different_thread_and_duplicate_start_refused(self):
        events = client.Events('expected')
        with self.assertRaisesRegex(ValueError, '^CODEX_THREAD_CHANGED$'):
            events.accept({'type': 'thread.started', 'thread_id': 'wrong'})
        events = self.start()
        with self.assertRaisesRegex(ValueError, '^CODEX_THREAD_INVALID$'):
            events.accept({'type': 'thread.started', 'thread_id': 'thread-fixture'})
        for identifier in ('', None, 1):
            with self.subTest(identifier=identifier), self.assertRaisesRegex(ValueError, '^CODEX_THREAD_INVALID$'):
                client.Events().accept({'type': 'thread.started', 'thread_id': identifier})

    def test_event_order_unknown_schema_and_duplicate_usage_refused(self):
        for event in ({'type': 'turn.started'}, {'type': 'turn.completed', 'usage': {}},
                      {'type': 'item.started', 'item': {}}, {'type': 'unrecognized'}, {}, []):
            with self.subTest(event=event), self.assertRaises(ValueError):
                client.Events().accept(event)
        events = self.start()
        self.finish(events)
        with self.assertRaisesRegex(ValueError, '^CODEX_EVENT_ORDER$'):
            self.finish(events)
        events = self.start()
        with self.assertRaisesRegex(ValueError, '^CODEX_EVENT_ORDER$'): events.accept({'type': 'turn.started'})
        for event in ({'type': 'item.started', 'item': None}, {'type': 'item.started', 'item': 'bad'}):
            with self.subTest(event=event), self.assertRaisesRegex(ValueError, '^CODEX_EVENT_ORDER$'):
                events.accept(event)
        self.finish(events)
        with self.assertRaisesRegex(ValueError, '^CODEX_EVENT_ORDER$'):
            events.accept({'type': 'item.started', 'item': {'type': 'agent_message'}})

    def test_missing_or_invalid_usage_refused(self):
        good = {'input_tokens': 1200, 'cached_input_tokens': 900, 'output_tokens': 70}
        for usage in (None, [], 'missing'):
            with self.subTest(usage=usage), self.assertRaisesRegex(ValueError, '^CODEX_USAGE_UNAVAILABLE$'):
                self.start().accept({'type': 'turn.completed', 'usage': usage})
        for field in good:
            for value in (None, -1, True, '5'):
                usage = {**good, field: value}
                with self.subTest(field=field, value=value), self.assertRaisesRegex(ValueError, '^CODEX_USAGE_UNAVAILABLE$'):
                    self.start().accept({'type': 'turn.completed', 'usage': usage})

    def test_unexpected_tools_detected(self):
        for item in ({'type': 'todo_list'}, {'type': 'command_execution'}, {'type': 'file_change'}, {'type': 'web_search'},
                     {'type': 'mcp_tool_call', 'server': 'other', 'tool': 'operation'},
                     {'type': 'mcp_tool_call', 'server': 'facts', 'tool': 'shell'}):
            with self.subTest(item=item), self.assertRaisesRegex(ValueError, '^CODEX_UNEXPECTED_TOOL_EVENT$'):
                self.start().accept({'type': 'item.started', 'item': item})

    def test_actual_captured_startup_stream_records_only_pinned_warnings(self):
        path = Path(__file__).parent/'fixtures/codex_startup_refused.jsonl'
        events = client.Events()
        raw = [json.loads(line) for line in path.read_text().splitlines()]
        for event in raw: events.accept(event)
        self.assertEqual(events.warnings, raw[1:4])
        self.assertEqual(len(events.warnings), 3)
        self.assertEqual(events.turns[-1]['type'], 'turn.failed')
        self.assertFalse(events.complete())  # The endpoint rejected the request.

    def test_startup_warning_limits_timing_and_exact_message(self):
        message = next(iter(client.STARTUP_WARNINGS))
        def warning(text=message):
            return {'type': 'item.completed', 'item': {'type': 'error', 'message': text}}
        events = client.Events()
        with self.assertRaisesRegex(ValueError, '^CODEX_STARTUP_WARNING_UNEXPECTED$'): events.accept(warning())
        events.accept({'type': 'thread.started', 'thread_id': 'fixture'})
        for bad in (None, {}, message+' ', 'Unknown warning'):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, '^CODEX_STARTUP_WARNING_UNEXPECTED$'):
                events.accept(warning(bad))
        events.accept(warning()); events.accept(warning())
        with self.assertRaisesRegex(ValueError, '^CODEX_STARTUP_WARNING_UNEXPECTED$'): events.accept(warning())
        events.accept({'type': 'turn.started'})
        with self.assertRaisesRegex(ValueError, '^CODEX_UNEXPECTED_TOOL_EVENT$'): events.accept(warning())
        self.finish(events)
        with self.assertRaisesRegex(ValueError, '^CODEX_EVENT_ORDER$'): events.accept(warning())


class OfferedToolTests(unittest.TestCase):
    def test_full_declaration_hash_includes_schema_description_and_order(self):
        self.assertEqual(client.declaration_hash(DECLARATION), client.DECLARATION_SHA256)
        for section in ('description', 'parameters'):
            changed=copy.deepcopy(DECLARATION)
            changed[-1]['tools'][0][section]='changed'
            with self.subTest(section=section), self.assertRaisesRegex(ValueError,'^CODEX_TOOL_DECLARATION_CHANGED$'):
                client.check_offered_tools(changed)
        changed=copy.deepcopy(DECLARATION)
        changed[0]['tools'][0]['description']+='\nAn additional capability.'
        for rows in (changed,list(reversed(DECLARATION))):
            with self.assertRaisesRegex(ValueError,'^CODEX_TOOL_DECLARATION_CHANGED$'):client.check_offered_tools(rows)

    def test_exact_direct_tool_and_unknown_shapes(self):
        good = copy.deepcopy(DECLARATION)
        self.assertEqual(set(client.check_offered_tools(good)), client.OFFERED_TOOLS)
        for bad in ([], good*2, good+[{'type': 'custom','name':'exec'}],
                    [{'type': 'function', 'name': 'operation'}]):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, '^CODEX_OFFERED_TOOLS_CHANGED$'):
                client.check_offered_tools(bad)
        renamed=copy.deepcopy(good);renamed[-1]['tools'][0]['name']='wrong'
        with self.assertRaisesRegex(ValueError,'^CODEX_OFFERED_TOOLS_CHANGED$'):client.check_offered_tools(renamed)
        for bad in (None, {}, [None], [{'type':'function'}], [{'type':'function','name':''}],
                    [{'type':'unknown','name':'x'}], [{'type':'namespace','name':'x'}]):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, '^CODEX_TOOL_SCHEMA$'):
                client.offered_tool_names(bad)

    def test_session_export_uses_matching_thread_and_retains_names_only(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name); folder = root/'sessions';folder.mkdir()
            for invalid in (None, '', 12):
                with self.subTest(invalid=invalid), self.assertRaisesRegex(ValueError, '^CODEX_THREAD_INVALID$'):
                    client.session_tool_records(root, invalid)
            with self.assertRaisesRegex(ValueError, '^CODEX_SESSION_MISSING_OR_AMBIGUOUS$'): client.session_tool_records(root, 'wanted')
            for thread in ('wanted', 'other'):
                (folder/('rollout-'+thread+'.jsonl')).write_text('\n'.join(json.dumps(e) for e in [
                    {'type':'session_meta','payload':{'id':thread}},
                    {'type':'response_item','payload':{'type':'additional_tools','id':'tool-set','tools':[
                        {'type':'function','name':client.TOOL if thread=='wanted' else 'secret', 'description':'private'}]}}])+'\n')
            rows = client.session_tool_records(root, 'wanted')
            self.assertEqual(rows, [{'thread_id':'wanted','item_id':'tool-set','names':[client.TOOL], 'declaration_sha256':client.declaration_hash([{'type':'function','name':client.TOOL,'description':'private'}])}])
            with self.assertRaisesRegex(ValueError, '^CODEX_SESSION_MISSING_OR_AMBIGUOUS$'): client.session_tool_records(root, 'absent')

    def test_private_call_scan_fails_closed_and_exports_no_arguments(self):
        with tempfile.TemporaryDirectory() as name:
            home=Path(name); folder=home/'sessions';folder.mkdir(); path=folder/'rollout-test.jsonl'
            def write(items):
                events=[{'type':'session_meta','payload':{'id':'wanted'}}]
                events += [{'type':'response_item','payload':{'type':'additional_tools','tools':DECLARATION}}]
                events += [{'type':'response_item','payload':i} for i in items]
                path.write_text(''.join(json.dumps(e)+'\n' for e in events))
            for item in ({'type':'function_call','name':'operation'},
                         {'type':'function_call','name':'operation','namespace':'mcp__facts'}):
                write([{**item,'call_id':'allowed','arguments':'PRIVATE'}])
                audit=client.audit_session(home,'wanted');client.enforce_session(audit)
                self.assertNotIn('PRIVATE',json.dumps(audit))
            for tool in ('exec','wait','request_user_input','request_user_input_async'):
                kind='custom_tool_call' if tool=='exec' else 'function_call'
                for names in ({'name':tool},{'name':tool,'namespace':'functions'}):
                    write([{'type':kind,**names,'call_id':'denied'}])
                    with self.subTest(kind=kind,tool=tool), self.assertRaisesRegex(ValueError,'^CODEX_FORBIDDEN_SESSION_CALL$'):
                        client.enforce_session(client.audit_session(home,'wanted'))
            for bad in ({'type':'function_call'}, {'type':'function_call','name':''}, {'type':'function_call','name':12},
                        {'type':'custom_tool_call','name':'operation','namespace':12},
                        {'type':'custom_tool_call','name':'operation','namespace':''}):
                write([bad])
                with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_INVALID$'):client.audit_session(home,'wanted')
            write([{'type':'future_tool_call'}])
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_UNSUPPORTED$'):client.audit_session(home,'wanted')
            write([{'type':'function_call_output','call_id':'x','output':'private'}])
            client.enforce_session(client.audit_session(home,'wanted'))
            for invalid in ('',12):
                with self.assertRaisesRegex(ValueError,'^CODEX_THREAD_INVALID$'):client.audit_session(home,invalid)
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_MISSING_OR_AMBIGUOUS$'):client.audit_session(home,'absent')
            duplicate=folder/'rollout-duplicate.jsonl';duplicate.write_bytes(path.read_bytes())
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_MISSING_OR_AMBIGUOUS$'):client.audit_session(home,'wanted')
            duplicate.unlink()
            path.write_text(path.read_text()+json.dumps({'type':'session_meta','payload':{'id':'second'}})+'\n')
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_INVALID$'):client.audit_session(home,'wanted')
            path.write_text(json.dumps({'type':'session_meta','payload':{'id':12}})+'\n')
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_INVALID$'):client.audit_session(home)

    def test_end_audit_enforces_names_and_whole_declaration_independently(self):
        good={'calls':[],'tools':[{'names':sorted(client.OFFERED_TOOLS),'declaration_sha256':client.DECLARATION_SHA256}]}
        client.enforce_session(good)
        for names in ([],sorted(client.OFFERED_TOOLS)+[client.TOOL], sorted(client.FORBIDDEN_TOOLS)+['wrong']):
            bad=copy.deepcopy(good);bad['tools'][0]['names']=names
            with self.assertRaisesRegex(ValueError,'^CODEX_OFFERED_TOOLS_CHANGED$'):client.enforce_session(bad)
        bad=copy.deepcopy(good);bad['tools'][0]['declaration_sha256']='changed'
        with self.assertRaisesRegex(ValueError,'^CODEX_TOOL_DECLARATION_CHANGED$'):client.enforce_session(bad)


class CallResolutionTests(unittest.TestCase):
    def test_live_bare_custom_exec_resolves_and_is_forbidden(self):
        call={'type':'custom_tool_call','name':'exec','call_id':'live-exec',
              'input':'text("synthetic-preflight-denial")\n'}
        result=client.resolve_call(call,DECLARATION)
        self.assertEqual((result['namespace'],result['tool'],result['declared_type']),('functions','exec','custom'))
        self.assertEqual(result['observed'],{'type':'custom_tool_call','name':'exec'})
        self.assertFalse(result['allowed'])

    def test_facts_bare_and_namespaced_are_allowed(self):
        for extra in ({},{'namespace':'mcp__facts'}):
            with self.subTest(extra=extra):
                call={'type':'function_call','name':'operation',**extra}
                result=client.resolve_call(call,DECLARATION)
                self.assertEqual((result['namespace'],result['tool'],result['declared_type']),('mcp__facts','operation','function'))
                self.assertTrue(result['allowed'])
                self.assertEqual(result['observed'],call)

    def test_wrong_kind_is_forbidden_before_allow(self):
        for call in ({'type':'custom_tool_call','name':'operation'},
                     {'type':'custom_tool_call','name':'operation','namespace':'mcp__facts'},
                     {'type':'function_call','name':'exec'}):
            with self.subTest(call=call), self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_TYPE$'):
                client.resolve_call(call,DECLARATION)

    def test_no_suffix_or_joined_name_matching(self):
        for call in ({'type':'function_call','name':'missing'},
                     {'type':'function_call','name':'mcp__facts__operation'},
                     {'type':'function_call','name':'operation','namespace':'other'},
                     {'type':'function_call','name':'operation','namespace':'functions'},
                     {'type':'function_call','name':'operation_extra','namespace':'mcp__facts'}):
            with self.subTest(call=call), self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_UNDECLARED$'):
                client.resolve_call(call,DECLARATION)

    def test_ambiguous_bare_name_refuses_even_if_types_differ(self):
        for kind in ('function','custom'):
            declaration=copy.deepcopy(DECLARATION)
            declaration[0]['tools'].append({'type':kind,'name':'operation'})
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_AMBIGUOUS$'):
                client.resolve_call({'type':'function_call','name':'operation'},declaration)
            # Explicit namespace resolves only its declared pair.
            self.assertTrue(client.resolve_call({'type':'function_call','name':'operation',
                'namespace':'mcp__facts'},declaration)['allowed'])
        duplicate=copy.deepcopy(DECLARATION)
        duplicate[-1]['tools']*=2
        with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_AMBIGUOUS$'):
            client.resolve_call({'type':'function_call','name':'operation','namespace':'mcp__facts'},duplicate)

    def test_only_facts_pair_and_function_kind_can_be_allowed(self):
        other=copy.deepcopy(DECLARATION)
        other[0]['tools'].append({'type':'function','name':'operation'})
        other[-1]['tools'].append({'type':'function','name':'different'})
        for call in ({'type':'function_call','name':'operation','namespace':'functions'},
                     {'type':'function_call','name':'different','namespace':'mcp__facts'},
                     {'type':'function_call','name':'wait','namespace':'functions'}):
            with self.subTest(call=call):self.assertFalse(client.resolve_call(call,other)['allowed'])

    def test_call_field_shapes_refuse(self):
        good={'type':'function_call','name':'operation'}
        for key, value in (('type','agent_message'),('name',None),('name',''),('name',12),
                           ('namespace',None),('namespace',''),('namespace',12)):
            with self.subTest(key=key,value=value),self.assertRaisesRegex(ValueError,'^CODEX_SESSION_CALL_INVALID$'):
                client.resolve_call({**good,key:value},DECLARATION)

    def test_declaration_entry_shapes_refuse(self):
        call={'type':'function_call','name':'operation'}
        for bad in (None,{}, {'type':'function','name':'facts','tools':[]},
                    {'type':'namespace','name':None,'tools':[]},
                    {'type':'namespace','name':12,'tools':[]},
                    {'type':'namespace','name':'','tools':[]},
                    {'type':'namespace','name':'facts','tools':None}):
            with self.subTest(bad=bad),self.assertRaisesRegex(ValueError,'^CODEX_TOOL_SCHEMA$'):
                client.resolve_call(call,[bad])
        for bad in (None,{}, {'type':'function','name':None},{'type':'function','name':''},
                    {'type':'function','name':12},
                    {'type':'unknown','name':'operation'}):
            with self.subTest(bad=bad),self.assertRaisesRegex(ValueError,'^CODEX_TOOL_SCHEMA$'):
                client.resolve_call(call,[{'type':'namespace','name':'facts','tools':[bad]}])

    def test_scanner_requires_preceding_pinned_same_session_declaration(self):
        declaration={'type':'additional_tools','tools':DECLARATION}
        call={'type':'function_call','name':'operation','call_id':'facts'}
        self.assertTrue(client.session_calls([declaration,call])[0]['allowed'])
        for items in ([call],[call,declaration]):
            with self.subTest(items=items),self.assertRaisesRegex(ValueError,'^CODEX_TOOL_LIST_MISSING$'):
                client.session_calls(items)
        client.session_calls([])
        with self.assertRaisesRegex(ValueError,'^CODEX_TOOL_LIST_MISSING$'):
            client.session_calls([],require_declaration=True)
        changed=copy.deepcopy(declaration);changed['tools'][0]['tools'][0]['description']+=' changed'
        for items in ([changed,call],[declaration,call,changed]):
            with self.subTest(items=items),self.assertRaisesRegex(ValueError,'^CODEX_TOOL_DECLARATION_CHANGED$'):
                client.session_calls(items)

    def test_bare_facts_pass_hook_but_wrong_type_or_undeclared_call_denies(self):
        with tempfile.TemporaryDirectory() as temp:
            home=Path(temp);(home/'sessions').mkdir();path=home/'sessions/rollout-fixture.jsonl'
            policy={'tool':client.TOOL,'session_home':str(home),'media':{}}
            request={'hook_event_name':'PreToolUse','tool_name':client.TOOL,'session_id':'fixture'}
            prefix=[{'type':'session_meta','payload':{'id':'fixture'}},
                    {'type':'response_item','payload':{'type':'additional_tools','tools':DECLARATION}}]
            for call,decision in (({'type':'function_call','name':'operation'},'allow'),
                                  ({'type':'function_call','name':'operation','namespace':'mcp__facts'},'allow'),
                                  ({'type':'custom_tool_call','name':'operation'},'deny'),
                                  ({'type':'function_call','name':'unknown'},'deny'),
                                  ({'type':'custom_tool_call','name':'exec'},'deny')):
                path.write_text(''.join(json.dumps(v)+'\n' for v in prefix+[{'type':'response_item','payload':call}]))
                with self.subTest(call=call):
                    self.assertEqual(client.hook_decision(policy,request)['hookSpecificOutput']['permissionDecision'],decision)


class HookMonitorTests(unittest.TestCase):
    def test_silent_append_partial_and_invalid_evidence(self):
        with tempfile.TemporaryDirectory() as name:
            p=Path(name)/'hooks.jsonl'; monitor=client.HookMonitor(p);monitor.poll()
            row=json.dumps({'tool':client.TOOL,'decision':'allow'}).encode()
            p.write_bytes(row[:10]);monitor.poll()
            p.write_bytes(row+b'\n');monitor.poll();monitor.poll(final=True)
            p.write_bytes(b'')
            with self.assertRaisesRegex(ValueError,'^CODEX_HOOK_LOG_CHANGED$'):monitor.poll()
            for record,code in (([], 'CODEX_HOOK_LOG_INVALID'), ({'decision':'unknown'},'CODEX_HOOK_LOG_INVALID'),
                                ({'decision':'deny','tool':'functions__exec'},'CODEX_HOOK_DENIED'),
                                ({'decision':'allow','tool':'functions__exec'},'CODEX_HOOK_UNEXPECTED_ALLOW')):
                p.write_text(json.dumps(record)+'\n')
                with self.subTest(record=record),self.assertRaisesRegex(ValueError,'^'+code+'$'):client.HookMonitor(p).poll()
            p.write_bytes(row)
            with self.assertRaisesRegex(ValueError,'^CODEX_HOOK_LOG_PARTIAL$'):client.HookMonitor(p).poll(final=True)


class RuntimePinTests(ProfileFixture, unittest.TestCase):
    def test_preparation_requires_installed_host_to_pin(self):
        self.code_host.unlink()
        with self.assertRaisesRegex(ValueError,'^CODEX_CODE_HOST_MISSING$'):
            client.prepare(self.root/'second', session=self.session,prompt=self.prompt,model='fixture-model',
                effort='xhigh',client=self.client,interpreter=sys.executable,service_root=self.service,
                heavy_lock=self.root/'lock',message='synthetic')
        self.assertFalse((self.root/'second').exists())

    def test_host_and_declaration_pins_refuse_changes(self):
        original=self.code_host.read_bytes();self.code_host.write_bytes(b'different host')
        with self.assertRaisesRegex(ValueError,'^CODEX_CODE_HOST_CHANGED$'):client.verify(self.profile)
        self.code_host.write_bytes(original)
        config={**self.config,'tool_declaration_sha256':'different'};client.save(self.profile/'launch.json',config)
        with self.assertRaisesRegex(ValueError,'^CODEX_TOOL_DECLARATION_CHANGED$'):client.verify(self.profile)


class ProcessAndSessionTests(unittest.TestCase):
    def test_permission_error_reaps_exited_root_but_refuses_live_group(self):
        from unittest.mock import Mock
        mod=client.process_tree
        owned={'pid':123456,'ppid':1,'pgid':123456,'started':'start','command':'client'}
        for alive in (False,True):
            p=Mock(pid=123456)
            with self.subTest(alive=alive), patch.object(mod,'snapshot',side_effect=[{123456:owned},{},{}]), patch.object(mod.os,'killpg',side_effect=PermissionError()):
                if alive:
                    # Keep the identity visible while signaling is refused.
                    mod.snapshot.side_effect=None;mod.snapshot.return_value={123456:owned}
                    with patch.object(mod.time,'monotonic',side_effect=[0,0,2]), self.assertRaisesRegex(ValueError,'^CODEX_PROCESS_CLEANUP_INCOMPLETE$'):
                        mod.stop_tree(p,{'client_pgid':123456},None,lambda:None)
                else:
                    mod.stop_tree(p,{'client_pgid':123456},None,lambda:None)
                    p.wait.assert_called_once()
                self.assertGreaterEqual(p.poll.call_count,2)
        for fail_on in (signal.SIGTERM,signal.SIGKILL):
            for alive in (False,True):
                p=Mock(pid=123456)
                def signal_group(pgid,sig):
                    if sig==fail_on:raise PermissionError()
                with self.subTest(signal=fail_on,alive=alive), patch.object(client.os,'killpg',side_effect=signal_group), patch.object(client,'group_alive',side_effect=[True,alive]):
                    if alive:
                        with self.assertRaises(PermissionError):client.stop_group(p)
                    else:client.stop_group(p)
                    self.assertGreaterEqual(p.poll.call_count,2)

    def test_process_snapshot_and_cleanup_refusals(self):
        from types import SimpleNamespace
        mod=client.process_tree
        valid='10 1 10 Tue Nov 10 01:02:03 2026 client\n'
        with patch.object(mod.subprocess,'run',return_value=SimpleNamespace(stdout=valid)):
            self.assertEqual(mod.snapshot()[10]['started'],'Tue Nov 10 01:02:03 2026')
        with patch.object(mod.subprocess,'run',return_value=SimpleNamespace(stdout='broken\n')):
            with self.assertRaisesRegex(ValueError,'^CODEX_PROCESS_SNAPSHOT_INVALID$'):mod.snapshot()
        for bad in (None,True,0,1,'123'):
            with self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_INVALID$'):mod.group_alive(bad)
        for bad in (True,0,1,'123',123.0):
            with self.subTest(pgid=bad), self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_INVALID$'):
                mod.live_groups({'client_pgid':bad},{})
        with patch.object(mod.os,'killpg',side_effect=PermissionError()):self.assertTrue(mod.group_alive(123456))
        p=SimpleNamespace(pid=123456,poll=lambda:None)
        orphan={'pid':123457,'ppid':1,'pgid':123456,'started':'child','command':'worker'}
        with patch.object(mod,'snapshot',return_value={123457:orphan}):
            with self.assertRaisesRegex(ValueError,'^CODEX_PROCESS_GROUP_IDENTITY_UNCERTAIN$'):
                mod.stop_tree(p,{'client_pgid':123456},None,lambda:None)
        owned={'pid':123456,'ppid':1,'pgid':os.getpgrp(),'started':'start','command':'client'}
        for unsafe in (1,os.getpgrp()):
            owned['pgid']=unsafe
            with patch.object(mod,'snapshot',return_value={123456:owned}),patch.object(mod.os,'killpg'),patch.object(mod,'group_alive',side_effect=lambda g:g==unsafe):
                with self.assertRaisesRegex(ValueError,'^'+('CODEX_CLIENT_GROUP_INVALID' if unsafe==1 else 'CODEX_PROCESS_GROUP_UNSAFE')+'$'):
                    mod.stop_tree(p,{'client_pgid':123456},None,lambda:None)
        owned['pgid']=123456
        with patch.object(mod,'snapshot',return_value={123456:owned}),patch.object(mod,'group_alive',return_value=True),patch.object(mod.os,'killpg'),patch.object(mod.time,'monotonic',side_effect=[0,2,2]):
            with self.assertRaisesRegex(ValueError,'^CODEX_PROCESS_CLEANUP_INCOMPLETE$'):
                mod.stop_tree(p,{'client_pgid':123456},None,lambda:None)

    def test_parent_chain_includes_separate_groups_and_excludes_unrelated_daemon(self):
        rows={pid:{'pid':pid,'ppid':ppid,'pgid':pgid,'started':'start','command':cmd} for pid,ppid,pgid,cmd in
              [(10,1,10,'client'),(11,10,11,'bridge'),(12,11,12,'worker'),(20,1,20,'daemon'),(21,20,21,'codex-code-mode-host')]}
        self.assertEqual(set(client.process_tree.descendants(rows,10)),{10,11,12})
        row={'client_pgid':10};client.process_tree.observe(row,None,rows)
        rows.pop(10);rows[11]['ppid']=1
        self.assertEqual(set(client.process_tree.descendants(rows,10,row['processes'])),{11,12})
        rows[11]['started']='reused'
        self.assertNotIn(11,client.process_tree.descendants(rows,10,row['processes']))

    def test_descendant_and_exact_session_bridge_block_after_client_exit(self):
        config={'service_root':'/tooling','session':'/fixture/session'}
        child={'pid':11,'ppid':1,'pgid':11,'started':'start','command':'python -B /tooling/scripts/structured_pass_bridge.py --mcp /fixture/session implementer corridor'}
        self.assertTrue(client.process_tree.bridge_matches(child,config))
        for wrong in ('/fixture/session-other','/fixture','/another/session'):
            self.assertFalse(client.process_tree.bridge_matches(child,{**config,'session':wrong}))
        with patch.object(client.process_tree,'snapshot',return_value={11:child}):
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_BRIDGE_ALIVE$'):
                client.process_tree.require_quiescent({'runs':[]},config)
            with self.assertRaisesRegex(ValueError,'^CODEX_DESCENDANT_ALIVE$'):
                client.process_tree.require_quiescent({'runs':[{'processes':[child]}]})
        orphan={**child,'pid':12,'command':'worker'}
        with patch.object(client.process_tree,'snapshot',return_value={12:orphan}):
            with self.assertRaisesRegex(ValueError,'^CODEX_DESCENDANT_GROUP_ALIVE$'):
                client.process_tree.require_quiescent({'runs':[{'processes':[child]}]})

    def test_reused_groups_are_ignored_without_signalling(self):
        old={'pid':11,'ppid':1,'pgid':11,'started':'old','command':'worker'}
        reused={**old,'started':'later'}
        for root in (None,11):
            run={'processes':[old],'client_pgid':root}
            state={'runs':[run]};before=copy.deepcopy(state)
            with self.subTest(root=root), patch.object(client.process_tree,'snapshot',return_value={11:reused}), patch.object(client.os,'killpg',side_effect=PermissionError()) as signal_group:
                client.require_quiescent_runs(state)
                signal_group.assert_not_called()
                self.assertEqual(state,before)
            with patch.object(client.process_tree,'snapshot',return_value={11:old}):
                with self.assertRaisesRegex(ValueError,'CODEX_(CLIENT_GROUP|DESCENDANT)_ALIVE'):
                    client.require_quiescent_runs(state)

    def test_leaderless_groups_still_refuse(self):
        old={'pid':11,'ppid':1,'pgid':11,'started':'old','command':'worker'}
        child={**old,'pid':12,'started':'child'}
        for root,code in ((None,'CODEX_DESCENDANT_GROUP_ALIVE'),(11,'CODEX_CLIENT_GROUP_ALIVE')):
            with self.subTest(root=root), patch.object(client.process_tree,'snapshot',return_value={12:child}):
                with self.assertRaisesRegex(ValueError,'^'+code+'$'):
                    client.require_quiescent_runs({'runs':[{'processes':[old],'client_pgid':root}]})
        # A crash before the initial observation leaves no start-time proof.
        with patch.object(client.process_tree,'snapshot',return_value={11:old}):
            with self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_ALIVE$'):
                client.require_quiescent_runs({'runs':[{'client_pgid':11}]})

    def test_reconciled_runs_skip_history_but_still_check_session_bridge(self):
        config={'service_root':'/tooling','session':'/session'}
        old={'pid':11,'ppid':1,'pgid':11,'started':'old','command':'worker'}
        run={'processes':[old],'client_pgid':11,'processes_reconciled':True}
        with patch.object(client.process_tree,'snapshot',return_value={11:old}):
            client.require_quiescent_runs({'runs':[run]},config)
            for bad in (False,'true',1):
                with self.subTest(marker=bad), self.assertRaisesRegex(ValueError,'^CODEX_CLIENT_GROUP_ALIVE$'):
                    client.require_quiescent_runs({'runs':[{**run,'processes_reconciled':bad}]},config)
        bridge={**old,'command':'python -B /tooling/scripts/structured_pass_bridge.py --mcp /session implementer corridor'}
        with patch.object(client.process_tree,'snapshot',return_value={11:bridge}):
            with self.assertRaisesRegex(ValueError,'^CODEX_SESSION_BRIDGE_ALIVE$'):
                client.require_quiescent_runs({'runs':[run]},config)

    def test_cleanup_does_not_adopt_or_signal_reused_root(self):
        from unittest.mock import Mock
        old={'pid':11,'ppid':1,'pgid':11,'started':'old','command':'worker'}
        row={'client_pgid':11,'processes':[old]};reused={**old,'started':'later'}
        p=Mock(pid=11)
        with patch.object(client.process_tree,'snapshot',return_value={11:reused}), patch.object(client.os,'killpg') as signal_group:
            client.process_tree.stop_tree(p,row,None,lambda:None)
            signal_group.assert_not_called()
            self.assertEqual(row['processes'],[old])

    def test_streaming_audit_and_hook_deny_follow_on_facts(self):
        with tempfile.TemporaryDirectory() as temp:
            home=Path(temp);(home/'sessions').mkdir();path=home/'sessions/rollout-fixture.jsonl'
            policy={'tool':client.TOOL,'session_home':str(home),'media':{}}
            request={'hook_event_name':'PreToolUse','tool_name':client.TOOL,'session_id':'fixture'}
            self.assertEqual(client.hook_decision(policy,request)['hookSpecificOutput']['permissionDecision'],'deny')
            client.poll_session(home,'fixture')
            path.write_text(json.dumps({'type':'session_meta','payload':{'id':'fixture'}})+'\n')
            self.assertEqual(client.hook_decision(policy,request)['hookSpecificOutput']['permissionDecision'],'deny')
            with path.open('a') as stream:
                stream.write(json.dumps({'type':'response_item','payload':{'type':'additional_tools','tools':DECLARATION}})+'\n')
            self.assertEqual(client.hook_decision(policy,request)['hookSpecificOutput']['permissionDecision'],'allow')
            with path.open('a') as stream:stream.write('{')
            client.poll_session(home,'fixture') # incomplete record waits for newline
            with path.open('a') as stream:stream.write('"type":"response_item","payload":{"type":"custom_tool_call","name":"exec","namespace":"functions"}}\n')
            with self.assertRaisesRegex(ValueError,'^CODEX_FORBIDDEN_SESSION_CALL$'):client.poll_session(home,'fixture')
            self.assertEqual(client.hook_decision(policy,request)['hookSpecificOutput']['permissionDecision'],'deny')


class CompactionTests(unittest.TestCase):
    def observed_item(self):
        return json.loads((Path(__file__).parent / 'fixtures/codex_compaction_item.json').read_text())

    def test_observed_four_key_item_and_legacy_item_both_pass(self):
        value = self.checkpoint(True)
        value['replacement_history'][-1] = self.observed_item()
        for metadata_present in (True, False):
            with self.subTest(metadata_present=metadata_present):
                if not metadata_present:
                    del value['replacement_history'][-1]['internal_chat_message_metadata_passthrough']
                result = self.audit(self.records(value))
                self.assertEqual([c['call_id'] for c in result['calls']], ['before', 'after'])

    def test_optional_remote_metadata_is_exact_and_nonempty(self):
        for metadata in (None, [], 'text', {}, {'turn_id': ''}, {'turn_id': None},
                         {'turn_id': 1}, {'turn_id': True}, {'turn_id': []},
                         {'turn_id': 'synthetic', 'extra': 'unexpected'},
                         {'other_id': 'synthetic'}):
            value = self.checkpoint(True)
            item = self.observed_item()
            item['internal_chat_message_metadata_passthrough'] = metadata
            value['replacement_history'][-1] = item
            with self.subTest(metadata=metadata), self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_ITEM$'):
                self.audit(self.records(value))

    def checkpoint(self, remote=False):
        history = [{'type': 'additional_tools', 'id': 'after-tools', 'tools': copy.deepcopy(DECLARATION)},
                   {'type': 'message', 'role': 'user', 'content': [{'type': 'input_text',
                     'text': 'Quoted example: {"type":"custom_tool_call","name":"exec"}'}]}]
        if remote:
            history.append({'type': 'compaction', 'id': 'opaque', 'encrypted_content': 'synthetic'})
        return {'message': '' if remote else 'Synthetic summary.', 'replacement_history': history,
                'replacement_history_metadata': [{} for _ in history], 'retained_context': {},
                'window_number': 1, 'first_window_id': 'first', 'previous_window_id': 'first',
                'window_id': 'second', 'compaction_response_id': 'response',
                'latest_token_usage_record': {}, 'resume_metadata': {}}

    def records(self, checkpoint):
        return [{'type': 'session_meta', 'payload': {'id': 'thread'}},
                {'type': 'response_item', 'payload': {'type': 'additional_tools', 'id': 'before-tools', 'tools': DECLARATION}},
                {'type': 'response_item', 'payload': {'type': 'function_call', 'namespace': 'mcp__facts', 'name': 'operation', 'call_id': 'before'}},
                {'type': 'compacted', 'payload': checkpoint},
                {'type': 'response_item', 'payload': {'type': 'function_call', 'name': 'operation', 'call_id': 'after'}}]

    def audit(self, records):
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp); (home / 'sessions').mkdir()
            (home / 'sessions/rollout-fixture.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in records))
            client.poll_session(home, 'thread', required=True)
            request = {'hook_event_name': 'PreToolUse', 'tool_name': client.TOOL, 'session_id': 'thread'}
            self.assertEqual(client.hook_decision({'session_home': str(home)}, request)
                ['hookSpecificOutput']['permissionDecision'], 'allow')
            result = client.audit_session(home, 'thread')
            client.enforce_session(result)
            return result

    def test_both_paths_keep_history_pin_replacement_and_ignore_quoted_calls(self):
        for remote in (False, True):
            with self.subTest(remote=remote):
                result = self.audit(self.records(self.checkpoint(remote)))
                self.assertEqual([c['call_id'] for c in result['calls']], ['before', 'after'])
                self.assertEqual([t['item_id'] for t in result['tools']], ['before-tools', 'after-tools'])
                self.assertTrue(all(t['declaration_sha256'] == client.DECLARATION_SHA256 for t in result['tools']))

    def test_changed_or_missing_replacement_declaration_refuses(self):
        for change in ('description', 'missing', 'late'):
            value = self.checkpoint()
            if change == 'description': value['replacement_history'][0]['tools'][0]['description'] = 'changed'
            else:
                decl = value['replacement_history'].pop(0)
                if change == 'late':
                    value['replacement_history'].insert(0, {'type': 'function_call', 'name': 'operation'})
                    value['replacement_history'].append(decl)
                value['replacement_history_metadata'] = [{} for _ in value['replacement_history']]
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, '^CODEX_TOOL_(DECLARATION_CHANGED|LIST_MISSING)$'):
                self.audit(self.records(value))

    def test_forbidden_before_or_inside_checkpoint_still_halts(self):
        for location in ('before', 'inside'):
            value = self.checkpoint(True); rows = self.records(value)
            forbidden = {'type': 'custom_tool_call', 'name': 'exec', 'call_id': 'forbidden'}
            if location == 'before': rows.insert(3, {'type': 'response_item', 'payload': forbidden})
            else:
                value['replacement_history'].append(forbidden)
                value['replacement_history_metadata'].append({})
            with self.subTest(location=location), self.assertRaisesRegex(ValueError, '^CODEX_FORBIDDEN_SESSION_CALL$'):
                self.audit(rows)

    def test_unknown_checkpoint_shapes_and_items_refuse(self):
        cases = []
        for key in self.checkpoint():
            v = self.checkpoint(); del v[key]; cases.append(v)
        v = self.checkpoint(); v['new_shape'] = True; cases.append(v)
        for key, bad in [('window_number', True), ('message', None), ('replacement_history', {}),
                         ('replacement_history_metadata', []), ('window_id', ''), ('resume_metadata', None)]:
            v = self.checkpoint(); v[key] = bad; cases.append(v)
        for kind in ('future_compaction', '_compaction_checkpoint', 'new_tool_call'):
            v = self.checkpoint(); v['replacement_history'].append({'type': kind}); v['replacement_history_metadata'].append({}); cases.append(v)
        for value in cases:
            with self.subTest(value=str(value)[:150]), self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_'):
                self.audit(self.records(value))

    def test_remote_item_and_path_must_match_observed_shapes(self):
        cases = []
        v = self.checkpoint(); v['message'] = ''; cases.append(v)
        v = self.checkpoint(True); v['message'] = 'mixed'; cases.append(v)
        v = self.checkpoint(True); v['replacement_history'][-1]['encrypted_content'] = ''; cases.append(v)
        v = self.checkpoint(True); v['replacement_history'][-1]['extra'] = True; cases.append(v)
        v = self.checkpoint(True); v['replacement_history'].append(v['replacement_history'][-1]); v['replacement_history_metadata'].append({}); cases.append(v)
        for value in cases:
            with self.subTest(value=str(value)[:150]), self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_'):
                self.audit(self.records(value))

    def test_history_cannot_restart_at_checkpoint_or_invent_compaction_record(self):
        rows = self.records(self.checkpoint())
        for changed in ([rows[0], *rows[3:]],
                        [rows[0], rows[3], rows[1], rows[4]],
                        [*rows[:3], {'type': 'response_item', 'payload': {'type': '_compaction_checkpoint', 'payload': self.checkpoint()}}],
                        [*rows[:3], {'type': 'context_compaction', 'payload': {}}],
                        [*rows[:3], {'type': 'response_item', 'payload': {'type': 'context_compaction'}}]):
            with self.subTest(changed=changed[-1]['type']), self.assertRaisesRegex(ValueError, '^CODEX_(TOOL_LIST_MISSING|COMPACTION_)'):
                self.audit(changed)


class CompactionAdmissionTests(ProfileFixture, unittest.TestCase):
    def probe(self):
        profile = self.root / 'compaction-profile'
        config = client.prepare(profile, session=self.session, prompt=self.prompt, model='fixture-model',
            effort='xhigh', client=self.client, interpreter=sys.executable, service_root=self.service,
            heavy_lock=self.root / 'lock', message='Synthetic compaction.', compaction_probe=True)
        protocol = self.root / 'protocol.json'; protocol.write_text('{"synthetic":true}\n')
        authority = {'authorized': True, 'owner_message': 'fixture', 'purpose': 'access_preflight',
            'launch_sha256': client.sha(profile / 'launch.json'), 'deadline': time.time() + 60,
            'token_response_caps': 'none_usage_reporting_only', 'compaction_probe': True,
            'compaction_protocol': {'path': str(protocol), 'sha256': client.sha(protocol)}}
        return profile, config, authority

    def test_probe_is_pinned_and_admitted_only_with_explicit_preflight_authority(self):
        profile, config, authority = self.probe()
        self.assertEqual(json.loads((profile / 'config.json').read_text())['model_auto_compact_token_limit'], 16384)
        self.assertEqual(client.verify(profile), config)
        with patch.dict(os.environ, {'NESREV_HEAVY_RUN_LOCK': config['heavy_lock']}):
            client.save(profile / 'authorization.json', authority)
            self.assertEqual(client.admission(profile, config), authority)
            for change in ({'purpose': 'pilot_takeover'}, {'compaction_probe': False}, {'compaction_probe': 1},
                           {'compaction_protocol': {}}, {'compaction_protocol': {'path': str(self.prompt), 'sha256': 'wrong'}}):
                client.save(profile / 'authorization.json', {**authority, **change})
                with self.subTest(change=change), self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_AUTHORIZATION$'):
                    client.admission(profile, config)

    def test_repinned_threshold_without_probe_and_unreviewed_values_refuse(self):
        profile, config, _ = self.probe()
        settings = json.loads((profile / 'config.json').read_text())
        for launch, value in (({**config, 'compaction_probe': False}, settings),
                              ({**config, 'compaction_probe': 1}, settings),
                              (config, {**settings, 'model_auto_compact_token_limit': True}),
                              (config, {**settings, 'model_auto_compact_token_limit': 32768}),
                              (config, {**settings, 'model_auto_compact_token_limit_scope': 'body_after_prefix'})):
            client.save(profile / 'config.json', value)
            launch = copy.deepcopy(launch); launch['configuration_sha256'] = client.sha(profile / 'config.json')
            launch['files'][str(profile / 'config.json')] = launch['configuration_sha256']
            client.save(profile / 'launch.json', launch)
            with (self.subTest(probe=launch.get('compaction_probe'), value=value.get('model_auto_compact_token_limit')),
                  self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_CONFIGURATION$')):
                client.verify(profile)

    def test_ordinary_profile_uses_default_threshold(self):
        self.assertNotIn('model_auto_compact_token_limit', json.loads((self.profile / 'config.json').read_text()))
        self.assertNotIn('compaction_probe', self.config)
        self.assertEqual(client.verify(self.profile), self.config)

    def test_preparation_requires_boolean_compaction_probe(self):
        for index, value in enumerate((1, 0, None, 'true')):
            profile = self.root / ('bad-probe-' + str(index))
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_CONFIGURATION$'):
                client.prepare(profile, session=self.session, prompt=self.prompt, model='fixture-model',
                    effort='xhigh', client=self.client, interpreter=sys.executable, service_root=self.service,
                    heavy_lock=self.root / 'lock', message='fixture', compaction_probe=value)
            self.assertFalse((profile / 'launch.json').exists())

    def test_repinned_context_window_is_banned_for_ordinary_and_probe_profiles(self):
        probe, config, _ = self.probe()
        for profile, launch in ((self.profile, self.config), (probe, config)):
            settings = json.loads((profile / 'config.json').read_text())
            settings['model_context_window'] = 16384
            client.save(profile / 'config.json', settings)
            launch = copy.deepcopy(launch)
            launch['configuration_sha256'] = client.sha(profile / 'config.json')
            launch['files'][str(profile / 'config.json')] = launch['configuration_sha256']
            client.save(profile / 'launch.json', launch)
            with self.subTest(profile=profile.name), self.assertRaisesRegex(ValueError, '^CODEX_COMPACTION_CONFIGURATION$'):
                client.verify(profile)


if __name__ == '__main__':
    unittest.main()
