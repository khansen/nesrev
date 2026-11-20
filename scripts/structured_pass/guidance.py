"""The existing policy allowlist, read at the pass-start commit."""
from pathlib import Path
import subprocess

NAMES = ('AGENTS.md',) + tuple('agent_playbook/' + name + '.md' for name in
    ('PASS_WORKFLOW', 'ASM_STYLE', 'QUALITY_REVIEW', 'REVIEW_AUDITS', 'TOOLING',
     'DOCUMENTATION', 'DATA_RECOVERY', 'NEW_PROJECT'))


def read(editor, name, generation=None):
    if name not in NAMES:
        from .operation_contract import RequestError
        raise RequestError(field='name',accepted_values=list(NAMES))
    from . import declared_inputs
    selected = generation or editor.state.get('pass_start_generation', editor.state['current'])
    model = editor.model(selected)
    if (model.capture/declared_inputs.FILE).exists():
        return declared_inputs.guidance_bytes(model.capture, name)
    if 'pass_start_generation' not in editor.state:return None
    start = editor.state['generations'][editor.state['pass_start_generation']]
    result = subprocess.run(['/usr/bin/git', '-C', str(Path(start['checkout'])),
        'show', editor.fixture['base_commit'] + ':' + name], capture_output=True)
    if result.returncode:
        return None
    return result.stdout
