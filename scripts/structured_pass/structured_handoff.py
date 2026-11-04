"""Structured-window mode of agent_review.py, using its state and verdict commands.

The lock, hashes and copied reports protect consistency. They do not authenticate
an OS user; the restricted client must keep this coordinator outside its workspace.
"""
from contextlib import contextmanager, ExitStack
import fcntl
import json
from pathlib import Path
import sys

from .durable_artifact import canonical, digest
from . import window_coverage as windows
REPORT_PAGE_CHARS = 1024
def require(ok, code):
    if not ok:
        raise ValueError(code)


def register(sub):
    init = sub.add_parser('init-structured', help='coordinator: initialize artifact review coverage')
    for field in ('project', 'run-id', 'store', 'base-artifact', 'head-artifact', 'reviewer'):
        init.add_argument('--' + field, required=True)
    init.add_argument('--max-rounds', type=int, default=16)
    init.add_argument('--editor-state', help='trusted live service state.json; otherwise an explicit frozen review range')
    init.set_defaults(func=None)
    advance = sub.add_parser('advance-structured', help='coordinator: register a published pass head')
    advance.add_argument('--head-artifact', required=True)
    advance.set_defaults(func=None)
    report = sub.add_parser('structured-report', help='read a checked verdict report in character pages')
    report.add_argument('--sequence', type=int, required=True)
    report.add_argument('--offset', type=int, default=0)
    report.add_argument('--limit', type=int, default=REPORT_PAGE_CHARS)
    report.set_defaults(func=None)


@contextmanager
def transaction(root):
    path = root / '.agents/structured-review.lock'
    path.parent.mkdir(exist_ok=True)
    with path.open('a+b') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('REVIEW_STATE_BUSY') from None
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


@contextmanager
def published_head(config):
    """Hold the editor's own lock through approval/archive; never race publication."""
    state_path = config.get('editor_state')
    if not state_path:
        yield None
        return
    state_path = Path(state_path)
    require(state_path.is_file(), 'PUBLISHER_STATE_UNAVAILABLE')
    try:
        lock = (state_path.parent / 'validation.lock').open('r+b')
    except OSError:
        raise ValueError('PUBLISHER_STATE_UNAVAILABLE') from None
    with lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('VALIDATION_IN_PROGRESS') from None
        try:
            state = json.loads(state_path.read_bytes())
            require(Path(state['retention']['root']).resolve() == Path(config['store']).resolve(),
                    'PUBLISHER_STORE_MISMATCH')
            current = state['current']
            head = state['generations'][current]['artifact']['artifact_id']
            start = state['pass_start_generation']
            base = state['generations'][start]['artifact']['artifact_id']
            require(base == config['pass_base'], 'PUBLISHER_BASE_MISMATCH')
            require(windows.receipt(config['store'], head)['legacy_generation'] == current,
                    'PUBLISHER_HEAD_MISMATCH')
        except (OSError, KeyError, TypeError, json.JSONDecodeError):
            raise ValueError('PUBLISHER_STATE_UNAVAILABLE') from None
        try:
            yield head
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def advance(api, root, state, head):
    config = state['structured_review']
    windows.window(config['store'], head)
    windows.pass_edges(config['store'], config['pass_head'], head)
    if config['pass_head'] != head:
        config['pass_head'] = head
        state['status'] = 'CHANGES_REQUESTED' if state['status'] == 'CHANGES_REQUESTED' else 'READY_FOR_REREVIEW'
    return save(api, root, state)


def checked_coverage(api, root, state):
    config = state['structured_review']
    previous = None
    history = config['verdict_history']
    for number, event in enumerate(history, 1):
        body = {k: v for k, v in event.items() if k != 'event_sha256'}
        require(event.get('sequence') == number and event.get('previous_event') == previous
                and event.get('event_sha256') == digest(canonical(body)), 'VERDICT_HISTORY_CHANGED')
        previous = event['event_sha256']
        report = root / event['review_file']
        require(report.resolve().is_relative_to(api.run_dir(root, state).resolve())
                and not report.is_symlink(), 'REVIEW_REPORT_CHANGED')
        require(report.is_file() and digest(report.read_bytes()) == event['review_sha256'],
                'REVIEW_REPORT_CHANGED')
    return windows.coverage(config['store'], config['pass_base'], config['pass_head'], history,
                            run_id=state['run_id'], reviewer=state['review_agent'])


def result(api, root, state):
    coverage = checked_coverage(api, root, state)
    history = state['structured_review']['verdict_history']
    latest = history[-1] if history else None
    text = (root / latest['review_file']).read_bytes().decode('utf-8') if latest else ''
    return {'status': state['status'], 'run_id': state['run_id'], 'round': state['round'],
            'reviewer': state['review_agent'], 'coverage': coverage,
            # Read only the report whose location and digest were checked above,
            # while the handoff lock is held. The implementer has no file access.
            'latest_review': ({'sequence': latest['sequence'], 'verdict': latest['verdict'],
                'sha256': latest['review_sha256'], 'report': text[:REPORT_PAGE_CHARS],
                'total_characters': len(text), 'truncated': len(text)>REPORT_PAGE_CHARS,
                'next_offset': REPORT_PAGE_CHARS if len(text)>REPORT_PAGE_CHARS else None,
                'operation': 'review_report'}
                if latest else None),
            'range_source': 'live-publisher' if state['structured_review'].get('editor_state') else 'frozen-artifacts',
            'verdict_count': len(state['structured_review']['verdict_history'])}


def report_page(api, root, state, sequence, offset, limit):
    checked_coverage(api, root, state)
    history=state['structured_review']['verdict_history']
    require(type(sequence) is int and 1<=sequence<=len(history)
            and type(offset) is int and offset>=0
            and type(limit) is int and 1<=limit<=REPORT_PAGE_CHARS, 'REQUEST_SCHEMA')
    event=history[sequence-1]
    text=(root/event['review_file']).read_bytes().decode('utf-8')
    require(offset<=len(text), 'REQUEST_SCHEMA')
    return {'run_id':state['run_id'], 'sequence':sequence, 'verdict':event['verdict'],
            'sha256':event['review_sha256'], 'offset':offset, 'limit':limit,
            'offset_unit':'Unicode characters', 'total_characters':len(text),
            'report':text[offset:offset+limit],
            'next_offset':offset+limit if offset+limit<len(text) else None}


def save(api, root, state):
    report = result(api, root, state)
    for role in ('implementer', 'reviewer'):
        prompt = api.run_dir(root, state) / 'prompts' / (role + '.md')
        prompt.parent.mkdir(parents=True, exist_ok=True)
        prompt.write_text('Structured pass review. Use the fixed service bridge.\n'
                          'Only recorded reviewer verdicts cover changes; page reads do not.\n'
                          + json.dumps(report, indent=2) + '\n')
        state['prompts'][role] = api.rel(root, prompt)
    api.write_state(root, state)
    return report


def initialize(api, root, args):
    require(not api.state_path(root).exists(), 'STRUCTURED_RUN_ALREADY_EXISTS')
    require(args.max_rounds > 0, 'REQUEST_SCHEMA')
    store = str(Path(args.store).resolve())
    edges = windows.pass_edges(store, args.base_artifact, args.head_artifact)
    require(bool(edges), 'EMPTY_REVIEW_RANGE')
    require(windows.receipt(store, args.base_artifact)['source_path'].startswith(
        'projects/' + args.project + '/'), 'MIXED_REVIEW_PROJECT')
    state = api.initial_state(root, project=args.project, base='HEAD', head='HEAD',
        run_id=args.run_id, max_rounds=args.max_rounds, reviewer=args.reviewer,
        implementer='implementer', allow_process_range=True, allow_unresolved_lxxxx=False)
    # Git identifies the coordinator only. The reviewed range is explicitly artifacts.
    state['structured_review'] = {'schema': 'window-verdict-history-v1', 'store': store,
        'pass_base': args.base_artifact, 'pass_head': args.head_artifact, 'verdict_history': []}
    if args.editor_state:
        state['structured_review']['editor_state'] = str(Path(args.editor_state).resolve())
    state['status'] = 'READY_FOR_REVIEW'
    with published_head(state['structured_review']) as current:
        require(current is None or current == args.head_artifact, 'PUBLISHER_HEAD_MISMATCH')
        return save(api, root, state)


def verdict(api, root, state, args):
    require(isinstance(args.window, str), 'REVIEW_WINDOW_REQUIRED')
    allowed = set(api.REVIEW_READY_STATUSES)
    if args.command == 'request-changes':
        allowed.add('APPROVED')  # A reviewer can revoke a previously accepted window.
    require(state['status'] in allowed, 'REVIEW_NOT_READY')
    config = state['structured_review']
    descriptor = windows.window(config['store'], args.window)
    required = checked_coverage(api, root, state)['required_edges']
    require(all(edge in required for edge in descriptor['edges']), 'VERDICT_OUTSIDE_PASS')
    name = 'APPROVED' if args.command == 'approve' else 'CHANGES_REQUESTED'
    source = api.require_file(root, args.review, 'review file')
    api.verdict_in_file(root, source, name)
    data = (root / source).read_bytes()
    sha = digest(data)
    history = config['verdict_history']
    number = len(history) + 1
    destination = api.run_dir(root, state) / f'review-window-{number:04d}-{sha}.md'
    if destination.exists():
        require(destination.read_bytes() == data, 'REVIEW_REPORT_CHANGED')
    else:
        destination.write_bytes(data)
    event = {**descriptor, 'sequence': number,
        'previous_event': history[-1]['event_sha256'] if history else None,
        'run_id': state['run_id'], 'reviewer': state['review_agent'], 'round': state['round'],
        'verdict': name, 'review_file': api.rel(root, destination), 'review_sha256': sha}
    event['event_sha256'] = digest(canonical(event))
    history.append(event)
    state['last_review'] = event['review_file']
    coverage = checked_coverage(api, root, state)
    state['status'] = ('CHANGES_REQUESTED' if name == 'CHANGES_REQUESTED' else
                       'APPROVED' if coverage['coverage_complete'] else 'READY_FOR_REREVIEW')
    return save(api, root, state)


def archive_document(api, root, state, pass_id):
    """Render checked evidence; the caller holds the review and publisher locks."""
    report = result(api, root, state)
    require(state['status'] == 'APPROVED' and report['coverage']['coverage_complete'],
            'REVIEW_COVERAGE_INCOMPLETE')
    require(bool(api.PASS_ID_RE.fullmatch(pass_id)), 'INVALID_PASS_ID')
    destination = api.project_review_archive_path(root, state, pass_id)
    text = ['# Structured pass review ' + pass_id, '',
            'Artifact coverage; the coordinator Git HEAD is not the reviewed source state.',
            '', '```json', json.dumps(report, indent=2), '```']
    for event in state['structured_review']['verdict_history']:
        text += ['', f"## Verdict {event['sequence']} — {event['verdict']}", '',
                 '```json', json.dumps(event, indent=2), '```', '',
                 (root / event['review_file']).read_text()]
    return {**report, 'archive': api.rel(root, destination)}, ('\n'.join(text) + '\n').encode()


def archive(api, root, state, args):
    require(not args.out, 'STRUCTURED_ARCHIVE_CANONICAL_PATH_REQUIRED')
    answer, data = archive_document(api, root, state, args.pass_id)
    destination = root / answer['archive']
    require(not destination.exists() or args.force, 'REVIEW_ARCHIVE_EXISTS')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(data)
    return answer


def dispatch(api, args):
    """Called by the real handoff parser before ordinary-mode commands dispatch."""
    root = api.repo_root()
    # Ordinary checkout-status deliberately works with stale handoff metadata.
    # Inspect only the mode discriminator here; validate structured state under
    # its lock below, and leave ordinary commands' validation to their handlers.
    try:
        header = json.loads(api.state_path(root).read_text())
    except (OSError, ValueError):
        header = {}
    active = isinstance(header, dict) and 'structured_review' in header
    if (not active and not getattr(args, 'expected_run_id', None)
            and not getattr(args, 'window', None)
            and args.command not in ('init-structured', 'advance-structured', 'structured-report')):
        return None
    with transaction(root), ExitStack() as locks:
        if args.command == 'init-structured':
            answer = initialize(api, root, args)
        else:
            state = api.read_state(root)  # Reload under the lock, never use a bridge snapshot.
            require(args.expected_run_id is None or state['run_id'] == args.expected_run_id,
                    'BRIDGE_RUN_CHANGED')
            require('structured_review' in state, 'STRUCTURED_MODE_REQUIRED')
            checked_coverage(api, root, state)
            config = state['structured_review']
            live = locks.enter_context(published_head(config))
            if live is not None and live != config['pass_head']:
                advance(api, root, state, live)
            if args.command in ('approve', 'request-changes'):
                answer = verdict(api, root, state, args)
            elif args.command == 'status':
                answer = result(api, root, state)
            elif args.command == 'structured-report':
                answer = report_page(api, root, state, args.sequence, args.offset, args.limit)
            elif args.command == 'advance-structured':
                require(live is None, 'HEAD_OWNED_BY_PUBLISHER')
                answer = advance(api, root, state, args.head_artifact)
            elif args.command == 'reready':
                require(state['status'] == 'CHANGES_REQUESTED', 'REVIEW_NOT_AWAITING_REPAIR')
                require(args.head == config['pass_head'], 'MIXED_GENERATION_COMPARISON')
                require(state['round'] < state['max_rounds'], 'REVIEW_ROUNDS_EXHAUSTED')
                source = api.require_file(root, args.response, 'response file')
                data = (root / source).read_bytes()
                require(bool(data.strip()) and len(data) <= 65536, 'REQUEST_SCHEMA')
                # The launcher input is temporary. Retain accepted bytes under
                # the verdict lock before the state can reference them.
                from .publication import immutable_file
                response = api.run_dir(root, state) / 'responses' / (digest(data) + '.md')
                immutable_file(response, data)
                state['last_response'] = api.rel(root, response)
                state['round'] += 1
                state['status'] = 'READY_FOR_REREVIEW'
                answer = save(api, root, state)
            elif args.command == 'archive':
                answer = archive(api, root, state, args)
            else:
                raise ValueError('STRUCTURED_COMMAND_UNAVAILABLE')
    print(json.dumps(answer, sort_keys=True))
    return 0
