"""Retained role observations and fixed ordinary-importer inputs; no triage authority."""
import json
from pathlib import Path
import tempfile

import agent_review as api
import process_friction as friction
from .durable_artifact import canonical, digest, require

ERRORS = frozenset('''LEARNING_REQUIRED LEARNING_BODY_INVALID LEARNING_TOO_LARGE
    LEARNING_SOURCE_CHANGED LEARNING_HISTORY_CHANGED LEARNING_INPUT_INVALID
    APPLICATION_FRICTION_DIRTY APPLICATION_FRICTION_CHANGED'''.split())
MAX_BODY_BYTES = 4096


def help_text(role):
    route = (
        ' In preview.operations, every kind: closeout requires learning: the body '
        'of your Learning Candidates section; the service supplies the heading. '
        'The JSON-encoded body must fit 4096 bytes. Every reready.response must '
        'include the section too.' if role == 'implementer' else
        ' Every approve.report and request-changes.report must include the section.')
    return (' ' + api.LEARNING_CANDIDATE_GUIDANCE +
            " Don't repeat observations from your earlier published candidates, rework "
            "responses or reports in this pass. Carry forward any from a candidate that "
            "did not publish." + route +
            ' Do not edit PROCESS_FRICTION.md or receipts directly.')


def check_report(text):
    require(isinstance(text, str) and '\0' not in text, 'LEARNING_BODY_INVALID')
    sections = api.learning_sections(text)
    require(len(sections) == 1 and sections[0][0] == '##', 'LEARNING_REQUIRED')
    body = sections[0][1]
    require(bool(body), 'LEARNING_REQUIRED')
    require(not api.learning_body_is_empty(body) or body == '_None._', 'LEARNING_BODY_INVALID')
    return body


def body(text):
    require(isinstance(text, str), 'LEARNING_REQUIRED')
    require(len(json.dumps(text).encode()) <= MAX_BODY_BYTES, 'LEARNING_TOO_LARGE')
    report = '## Learning Candidates\n\n' + text
    require(check_report(report) == text.strip(), 'LEARNING_BODY_INVALID')
    return text


def checked_responses(root, state):
    from . import window_coverage as windows
    config = state['structured_review']
    history = config.get('response_history')
    require(isinstance(history, list), 'LEARNING_HISTORY_CHANGED')
    previous = None
    expected_root = api.run_dir(root, state).resolve() / 'responses'
    for number, event in enumerate(history, 1):
        entry = {k: v for k, v in event.items() if k != 'event_sha256'}
        require(event.get('sequence') == number and event.get('round') == number + 1
                and event.get('previous_event') == previous
                and event.get('run_id') == state['run_id']
                and event.get('event_sha256') == digest(canonical(entry)), 'LEARNING_HISTORY_CHANGED')
        windows.pass_edges(config['store'], config['pass_base'], event['head'])
        windows.pass_edges(config['store'], event['head'], config['pass_head'])
        path = root / event['file']
        require(path.resolve() == expected_root / (event['sha256'] + '.md')
                and not path.is_symlink() and path.is_file()
                and digest(path.read_bytes()) == event['sha256'], 'LEARNING_SOURCE_CHANGED')
        check_report(path.read_text())
        previous = event['event_sha256']
    require(len(history) == state['round'] - 1 and
            state.get('last_response') == (history[-1]['file'] if history else None),
            'LEARNING_HISTORY_CHANGED')
    return history


def source(identity, role, origin, text):
    check_report(text)
    return {'id': identity, 'role': role, 'origin': origin,
            'sha256': digest(text.encode()), 'text': text}


def freeze(controller, review):
    from .publication import immutable_file
    state = controller.checked_editor()
    generations = []
    generation = state['current']
    while generation != state['pass_start_generation']:
        require(generation not in generations and generation in state['generations'], 'LEARNING_SOURCE_CHANGED')
        generations.append(generation)
        generation = state['generations'][generation]['base']
    sources = []
    for generation in reversed(generations):
        controller.editor.model(generation)
        record = state['generations'][generation]
        receipt = json.loads((Path(record['capture']) / 'closeout.json').read_text())
        require('learning' in receipt, 'LEARNING_REQUIRED')
        text = body(receipt['learning'])
        sources.append(source('implementer-' + generation, 'implementer',
            {'generation': generation, 'artifact': record['artifact']['artifact_id']},
            '## Learning Candidates\n\n' + text))
    root = controller.root / 'handoff'
    for event in checked_responses(root, review):
        sources.append(source('response-' + str(event['sequence']), 'implementer', event,
                              (root / event['file']).read_bytes().decode()))
    for event in review['structured_review']['verdict_history']:
        data = (root / event['review_file']).read_bytes()
        require(digest(data) == event['review_sha256'], 'LEARNING_SOURCE_CHANGED')
        sources.append(source('review-' + str(event['sequence']), 'reviewer', event, data.decode()))
    bundle = {'schema': 'structured-learning-v1', 'run_id': review['run_id'],
              'project': controller.editor.slug, 'pass_id': controller.config['pass_id'],
              'head': state['current'], 'sources': sources}
    data = canonical(bundle)
    path = api.run_dir(root, review) / 'learning' / (digest(data) + '.json')
    immutable_file(path, data)
    return {'path': str(path.relative_to(root)), 'sha256': digest(data)}, bundle


def archive_section(bundle):
    # The archive keeps originals after the temporary handoff directory is gone.
    # Import consumes the indexed bundle, never parses this combined archive.
    anchors = ''.join('<a id="' + item['id'] + '"></a>\n' for item in bundle['sources'])
    return ('\n## Retained learning sources\n\n' + anchors + '\n```json\n' +
            json.dumps(bundle, indent=2, ensure_ascii=True) + '\n```\n').encode()


def load(controller, closed):
    require(isinstance(closed.get('learning_sources'), dict), 'LEARNING_REQUIRED')
    pin = closed['learning_sources']
    root = controller.root / 'handoff'
    path = root / pin['path']
    expected = root / '.agents/runs' / controller.config['run_id'] / 'learning' / (pin['sha256'] + '.json')
    require(path.resolve() == expected.absolute() and not path.is_symlink()
            and path.is_file() and digest(path.read_bytes()) == pin['sha256'], 'LEARNING_SOURCE_CHANGED')
    bundle = json.loads(path.read_bytes())
    require(bundle['schema'] == 'structured-learning-v1' and
            bundle['project'] == controller.editor.slug and bundle['run_id'] == controller.config['run_id']
            and bundle['pass_id'] == controller.config['pass_id']
            and bundle['head'] == closed['closed_generation'], 'LEARNING_SOURCE_CHANGED')
    for item in bundle['sources']:
        require(digest(item['text'].encode()) == item['sha256'], 'LEARNING_SOURCE_CHANGED')
        check_report(item['text'])
    return bundle


def paths(slug):
    return ('projects/' + slug + '/PROCESS_FRICTION.md',
            'projects/' + slug + '/docs/reverse_engineering/inventory/process_friction_receipts.json')


def output_path(controller, sha):
    require(isinstance(sha, str) and len(sha) == 64 and all(c in '0123456789abcdef' for c in sha),
            'LEARNING_SOURCE_CHANGED')
    return controller.root / 'friction-output' / (sha + '.md')


def build(controller, closed, target, current, hash_at, disk_hash):
    """Rebuild before starting application, using only committed current inputs."""
    from .publication import immutable_file
    bundle = load(controller, closed)
    queue, receipts = paths(controller.editor.slug)
    inputs = {p: hash_at(target, current, p) for p in (queue, receipts)}
    require(all(disk_hash(target, p) == expected for p, expected in inputs.items()),
            'APPLICATION_FRICTION_DIRTY')
    with tempfile.TemporaryDirectory(prefix='friction-import-', dir=controller.root) as temporary:
        staging = Path(temporary)
        (staging / 'projects' / controller.editor.slug).mkdir(parents=True)
        for p, expected in inputs.items():
            if expected is None:
                continue
            data = (target / p).read_bytes()
            require(digest(data) == expected, 'APPLICATION_FRICTION_CHANGED')
            dest = staging / p
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
        try:
            friction.read_receipts(staging, controller.editor.slug)
            if (staging / queue).is_file():
                friction.queue_candidates((staging / queue).read_text(), queue)
            state = {'project': controller.editor.slug, 'run_id': bundle['run_id'],
                     'review_head': closed['coverage']['pass_head']}
            artifacts = [(closed['archive'] + '#' + item['id'], item['text']) for item in bundle['sources']]
            api.update_process_friction(staging, state, bundle['pass_id'], closed['archive'], artifacts=artifacts)
        except (friction.FrictionError, api.UserError, UnicodeError):
            raise ValueError('LEARNING_INPUT_INVALID') from None
        data = (staging / queue).read_bytes() if (staging / queue).is_file() else None
        result = digest(data) if data is not None else None
        if result is not None:
            immutable_file(output_path(controller, result), data)
    require(all(disk_hash(target, p) == expected for p, expected in inputs.items()),
            'APPLICATION_FRICTION_CHANGED')
    return {'sources_sha256': closed['learning_sources']['sha256'], 'inputs': inputs,
            'queue': queue, 'output_sha256': result}


def check_plan(controller, closed, plan):
    queue, receipts = paths(controller.editor.slug)
    require(plan['sources_sha256'] == closed['learning_sources']['sha256']
            and plan['queue'] == queue and set(plan['inputs']) == {queue, receipts},
            'LEARNING_SOURCE_CHANGED')
    load(controller, closed)
    if plan['output_sha256'] is not None:
        path = output_path(controller, plan['output_sha256'])
        require(path.is_file() and not path.is_symlink()
                and digest(path.read_bytes()) == plan['output_sha256'], 'LEARNING_SOURCE_CHANGED')


def check_inputs(target, plan, disk_hash, *, applying=False):
    for path, expected in plan['inputs'].items():
        allowed = {expected}
        if applying and path == plan['queue']:
            allowed.add(plan['output_sha256'])
        require(disk_hash(target, path) in allowed, 'APPLICATION_FRICTION_CHANGED')
