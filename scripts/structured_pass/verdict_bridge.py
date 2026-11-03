"""Fixed-role transport to agent_review.py; this is not another verdict store."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
from .structured_handoff import windows, require


class Bridge:
    def __init__(self, config):
        self.config = json.loads(Path(config).read_text())
        require(set(self.config) == {'root', 'role', 'run_id', 'scripts'}, 'BRIDGE_CONFIG_INVALID')
        require(self.config['role'] in ('implementer', 'reviewer'), 'BRIDGE_CONFIG_INVALID')
        self.root = Path(self.config['root']).resolve()

    def command(self, *args):
        env = {'PATH': '/usr/bin:/bin', 'PYTHONPATH': self.config['scripts'],
               'PYTHONDONTWRITEBYTECODE': '1', 'LC_ALL': 'C', 'LANG': 'C'}
        completed = subprocess.run([sys.executable, '-B', str(HERE.parent / 'agent_review.py'),
            '--repo', str(self.root), '--expected-run-id', self.config['run_id'], *args],
            capture_output=True, text=True, env=env, timeout=60)
        if completed.returncode:
            message = completed.stderr.strip().removeprefix('error: ')
            raise ValueError(message if re.fullmatch('[A-Z][A-Z0-9_]+', message) else 'REVIEW_COMMAND_FAILED')
        return json.loads(completed.stdout)

    def dispatch(self, request):
        require(isinstance(request, dict) and set(request) == {'operation', 'arguments'}, 'REQUEST_SCHEMA')
        op, args = request['operation'], request['arguments']
        require(isinstance(op, str) and isinstance(args, dict), 'REQUEST_SCHEMA')
        # Authenticate the route via trusted startup configuration, never a request field.
        if op in ('approve', 'request-changes'):
            require(self.config['role'] == 'reviewer', 'REVIEWER_ONLY')
        elif op not in ('status','review_report'):
            raise ValueError('OPERATION_NOT_AVAILABLE')
        if op=='review_report':
            require(set(args)>={'sequence'} and set(args)<={'sequence','offset','limit'}
                    and all(type(v) is int for v in args.values()), 'REQUEST_SCHEMA')
            return self.command('structured-report','--sequence',str(args['sequence']),
                                '--offset',str(args.get('offset',0)),
                                '--limit',str(args.get('limit',1024)))
        expected = set() if op == 'status' else {'ticket', 'report'}
        require(set(args) == expected, 'REQUEST_SCHEMA')
        state = self.command('status', '--json')
        require(state['run_id'] == self.config['run_id'], 'BRIDGE_RUN_CHANGED')
        if op == 'status':
            return state
        require(all(isinstance(args[k], str) and args[k] for k in expected)
                and len(args['report'].encode()) <= 65536, 'REQUEST_SCHEMA')
        # The report enters the same commands and canonical run history as CLI reports.
        folder = self.root / '.agents/runs' / self.config['run_id']
        with tempfile.NamedTemporaryFile(prefix='verdict-input-', suffix='.md', dir=folder) as source:
            source.write(args['report'].encode()); source.flush()
            return self.command(op, '--window', args['ticket'], '--review', source.name)


def mcp(config):
    bridge = Bridge(config)
    for line in sys.stdin:
        try:
            request = json.loads(line)
        except ValueError:
            print(json.dumps({'jsonrpc': '2.0', 'id': None, 'error': {'code': -32700, 'message': 'Parse error'}}), flush=True)
            continue
        if not isinstance(request, dict) or not isinstance(request.get('method'), str):
            print(json.dumps({'jsonrpc': '2.0', 'id': None, 'error': {'code': -32600, 'message': 'Invalid request'}}), flush=True)
            continue
        if 'id' not in request:
            continue
        method = request['method']
        if method == 'initialize':
            result = {'protocolVersion': request['params']['protocolVersion'], 'capabilities': {'tools': {}},
                      'serverInfo': {'name': 'handoff-verdicts', 'version': 'prototype-1'}}
        elif method == 'tools/list':
            operations = ['status','review_report'] + (['approve', 'request-changes'] if bridge.config['role'] == 'reviewer' else [])
            result = {'tools': [{'name': 'operation', 'description': 'Existing handoff status and window verdicts.',
                'inputSchema': {'type': 'object', 'properties': {'operation': {'type': 'string', 'enum': operations},
                    'arguments': {'type': 'object'}}, 'required': ['operation', 'arguments'], 'additionalProperties': False}}]}
        elif method == 'tools/call':
            try:
                params = request['params']
                require(params['name'] == 'operation', 'REQUEST_SCHEMA')
                answer = bridge.dispatch(params['arguments'])
                result = {'content': [{'type': 'text', 'text': json.dumps(answer)}]}
            except Exception as exc:
                code = str(exc) if isinstance(exc, ValueError) and re.fullmatch('[A-Z][A-Z0-9_]+', str(exc)) else 'INTERNAL_SERVICE_ERROR'
                result = {'isError': True, 'content': [{'type': 'text', 'text': json.dumps({'error': code})}]}
        elif method == 'ping':
            result = {}
        else:
            print(json.dumps({'jsonrpc': '2.0', 'id': request['id'], 'error': {'code': -32601, 'message': 'Unknown method'}}), flush=True)
            continue
        print(json.dumps({'jsonrpc': '2.0', 'id': request['id'], 'result': result}), flush=True)


if __name__ == '__main__':
    mcp(sys.argv[1])
