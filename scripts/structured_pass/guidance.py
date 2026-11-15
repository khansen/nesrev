"""The existing policy allowlist, read at the pass-start commit."""
from pathlib import Path
import subprocess

NAMES = ('AGENTS.md',) + tuple('agent_playbook/' + name + '.md' for name in
    ('PASS_WORKFLOW', 'ASM_STYLE', 'QUALITY_REVIEW', 'REVIEW_AUDITS', 'TOOLING',
     'DOCUMENTATION', 'DATA_RECOVERY'))


def read(editor, name):
    if name not in NAMES:
        raise ValueError('REQUEST_SCHEMA')
    start = editor.state['generations'][editor.state['pass_start_generation']]
    result = subprocess.run(['/usr/bin/git', '-C', str(Path(start['checkout'])),
        'show', editor.fixture['base_commit'] + ':' + name], capture_output=True)
    if result.returncode:
        return None
    return result.stdout
