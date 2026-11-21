"""Operator-selected, verbatim guidance and a measured conversation allowance."""
import re

from . import declared_inputs as inputs, producer

INPUT_ID = 'guidance-startup'
PAGE_BYTES = 24576


def sections(data, selected):
    """Canonical anchor blocks, including every byte until the next anchor."""
    text = data.decode('utf-8')
    anchors = {}; fence = None; position = 0
    for line in text.splitlines(keepends=True):
        stripped = line.strip()
        marker = re.match(r'(`{3,}|~{3,})', stripped)
        if marker:
            token = marker[1]
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence):
                fence = None
        if fence is None:
            match = re.fullmatch(r'<a id="([a-z0-9-]+)"></a>', stripped)
            if match:
                inputs.require(match[1] not in anchors)
                anchors[match[1]] = position
        position += len(line)
    inputs.require(isinstance(selected, list) and selected and all(isinstance(a, str) for a in selected)
                   and len(selected) == len(set(selected)))
    if selected == ['*']:
        return text
    inputs.require(all(isinstance(a, str) and a in anchors for a in selected))
    names = list(anchors)
    inputs.require(selected == [a for a in names if a in selected])
    return ''.join(text[anchors[a]:anchors[names[names.index(a)+1]]
                        if names.index(a)+1 < len(names) else len(text)] for a in selected)


def allowance(context):
    keys = {'window_tokens', 'startup_tokens', 'lifecycle_tokens', 'margin_tokens',
            'bytes_per_1000_tokens'}
    inputs.require(isinstance(context, dict) and set(context) == keys)
    inputs.require(all(type(v) is int and v > 0 for v in context.values()))
    inputs.require(context['margin_tokens'] >= (context['window_tokens']+9)//10)
    remaining = context['window_tokens'] - sum(context[k] for k in
                                             ('startup_tokens', 'lifecycle_tokens', 'margin_tokens'))
    response_bytes = remaining * context['bytes_per_1000_tokens'] // 1000
    inputs.require(response_bytes >= PAGE_BYTES, 'INPUT_LIMIT_EXCEEDED')
    return {**context, 'response_tokens': remaining, 'response_bytes': response_bytes,
            'page_maximum_bytes': PAGE_BYTES}


def build(spec, guidance):
    inputs.require(isinstance(spec, dict) and set(spec) == {'sections', 'context'})
    inputs.require(isinstance(spec['sections'], list) and 0 < len(spec['sections']) <= len(guidance))
    seen = set(); parts = ['# Selected startup guidance\n\n'
        'The following canonical sections are reproduced verbatim. All complete guidance files '
        'remain available by their original input IDs. Read additional sections when the work '
        'requires them; those reads consume the remaining conversation allowance.\n\n']
    sources = []
    for choice in spec['sections']:
        inputs.require(isinstance(choice, dict) and set(choice) == {'input_id', 'anchors'})
        identity = choice['input_id']
        inputs.require(isinstance(identity, str) and identity in guidance and identity not in seen)
        seen.add(identity)
        item, data = guidance[identity]
        body = sections(data, choice['anchors'])
        sources.append({'input_id': identity, 'path': item['origin']['path'],
                        'sha256': item['sha256'], 'anchors': choice['anchors'],
                        'selected_sha256': producer.digest(body.encode()), 'selected_bytes': len(body.encode())})
        parts += ['\nSource: '+item['origin']['path']+'; full input: '+identity+
                  '; sha256: '+item['sha256']+'\n\n', body]
    return ''.join(parts).encode(), {'sources': sources, 'budget': allowance(spec['context'])}


def prompt(startup):
    budget = startup['budget']
    inputs.require(budget == allowance({k: v for k, v in budget.items()
        if k not in ('response_tokens', 'response_bytes', 'page_maximum_bytes')}), 'INPUT_CHANGED')
    return ('\n## Prepared startup and conversation allowance\n'
        'Read '+INPUT_ID+' completely at startup, instead of reading the complete playbooks. '
        'The selected sections retain their full prose. Read the operation reference, supplied '
        'reference texts, intake receipt and reference decision as directed by the task. '
        'Use the fixed IDs in the index below; a separate catalog download is unnecessary. '
        'The full playbooks remain available on demand.\n'
        f"The measured context window is {budget['window_tokens']} tokens. Preparation budgets "
        f"{budget['startup_tokens']} tokens for the complete startup, reserves "
        f"{budget['lifecycle_tokens']} for edits, validation and closeout, and leaves "
        f"{budget['margin_tokens']} for estimation error. After startup, the investigation allowance is "
        f"{budget['response_bytes']} bytes of text responses across this conversation, including "
        'all evidence questions, both analogues, extra guidance, refusals and repeated reads. '
        'Add each volume.response_bytes; neither a new question nor a resumed turn resets the total. '
        'For each question use the smaller of 409600 bytes and the remaining conversation allowance. '
        'Before a call, reserve its 24576-byte maximum. Narrow the query or stop for a decision '
        'before exceeding either investigation allowance. Edit preparation, preview, confirm, '
        'validate, publish, review reports, rework and closeout use the separate lifecycle reserve, '
        'including their necessary document and edit-preimage reads. They do not consume the '
        'investigation byte allowance. Do not use that reserve for new evidence questions or '
        'spend the estimation margin. Images require a separate measured allowance. This is audited '
        'caller accounting, not a service-enforced counter.\n')
