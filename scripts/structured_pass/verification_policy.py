"""Service-owned naming eligibility, bound to the immutable pass starting source.

This is the lexical naming rule from verify.sh, not an instruction parser.
Relaxation waives that rule only; a successful full verifier still is required.
"""
import hashlib
from pathlib import Path
import re
import subprocess
import time

from . import gate_environment

ERRORS = frozenset(('VERIFICATION_POLICY_INVALID', 'VERIFICATION_POLICY_CHANGED'))
NAME = r'\bL[0-9A-F]{4,5}\b'
LINE = r'\bL[0-9A-F]{4,5}\b|^L[0-9A-F]{4,5}:'

def require(condition, code='VERIFICATION_POLICY_INVALID'):
    if not condition:
        raise ValueError(code)


def counts(data, env):
    gate_environment.require(set(env) == gate_environment.BASE_KEYS)
    def matches(flag, pattern):
        result = subprocess.run(['rg', flag, pattern], input=data, env=env, capture_output=True)
        require(result.returncode in (0, 1))
        return result.stdout.splitlines()
    return {'distinct_names': len(set(matches('-o', NAME))),
            'matching_lines': len(matches('-n', LINE))}


def derive(base_commit, source, data, env):
    before = counts(data, env)
    return {'schema': 'early-pass-verification-v1', 'base_commit': base_commit,
            'source': source, 'source_sha256': hashlib.sha256(data).hexdigest(),
            'starting_counts': before,
            'eligibility': 'naming-only' if before['distinct_names'] else 'strict'}


def validate(policy, base_commit, source, data, env):
    require(policy == derive(base_commit, source, data, env), 'VERIFICATION_POLICY_CHANGED')


def check_shape(policy):
    require(isinstance(policy, dict) and set(policy) == {
        'schema', 'base_commit', 'source', 'source_sha256', 'starting_counts', 'eligibility'})
    require(policy['schema'] == 'early-pass-verification-v1')
    require(isinstance(policy['base_commit'], str) and re.fullmatch('[a-f0-9]{40}', policy['base_commit']))
    require(isinstance(policy['source_sha256'], str) and re.fullmatch('[a-f0-9]{64}', policy['source_sha256']))
    source = policy['source']
    require(isinstance(source, str) and not Path(source).is_absolute() and '..' not in Path(source).parts)
    before = policy['starting_counts']
    require(isinstance(before, dict) and set(before) == {'distinct_names', 'matching_lines'}
            and all(type(v) is int and v >= 0 for v in before.values()))
    require(policy['eligibility'] == ('naming-only' if before['distinct_names'] else 'strict'))


def expected_scorecard(evidence):
    require(evidence['mode'] in ('strict', 'naming-only'))
    return 'pass (LXXXX allowed)' if evidence['mode'] == 'naming-only' else 'pass'


def summary(evidence):
    return {k: v for k, v in evidence.items() if k != 'attempts'} | {
        'attempts': [{k: a[k] for k in ('mode', 'exit_code', 'log_sha256')}
                     for a in evidence['attempts']]}


def run(checkout, slug, folder, env, policy):
    """Use the verifier's own exit code, never make's lossy exit status."""
    check_shape(policy)
    gate_environment.require(set(env) == gate_environment.BASE_KEYS)
    checkout, folder = Path(checkout), Path(folder)
    data = (checkout / policy['source']).read_bytes()
    after = counts(data, env)
    command = ['/bin/bash', 'scripts/project_verify.sh', slug]
    started = time.monotonic()
    attempts = []
    mode = 'strict'
    for suffix in ('strict', 'naming-only'):
        environment = gate_environment.verification_environment(env, naming_only=suffix == 'naming-only')
        log = folder / ('project-verify.' + suffix + '.log')
        with log.open('wb') as stream:
            result = subprocess.run(command, cwd=checkout, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        attempts.append({'mode': suffix, 'command': command, 'exit_code': result.returncode,
                         'log_sha256': gate_environment.sha(log), 'environment': environment})
        mode = suffix
        if not (suffix == 'strict' and result.returncode == 3 and
                policy['eligibility'] == 'naming-only' and after['distinct_names'] > 0):
            break
    # Keep the conventional log path for gate diagnostics; each attempt is retained.
    effective = folder / 'project-verify.log'
    effective.write_bytes(log.read_bytes())
    require((checkout / policy['source']).read_bytes() == data, 'VERIFICATION_POLICY_CHANGED')
    evidence = {'policy': policy, 'mode': mode, 'before': policy['starting_counts'], 'after': after,
                'source_sha256': hashlib.sha256(data).hexdigest(), 'attempts': attempts,
                'strict_green': result.returncode == 0 and mode == 'strict'}
    return {'target': 'project-verify', 'exit_code': result.returncode,
            'seconds': time.monotonic() - started, 'log_sha256': gate_environment.sha(effective),
            'environment': environment, 'verification': evidence}


def check_evidence(evidence, policy, data, env):
    """Validate successful evidence before trusting a qualified closeout."""
    check_shape(policy)
    require(evidence['policy'] == policy and evidence['before'] == policy['starting_counts']
            and evidence['after'] == counts(data, env)
            and evidence['source_sha256'] == hashlib.sha256(data).hexdigest())
    attempts = evidence['attempts']
    require(isinstance(attempts, list) and bool(attempts))
    mode = evidence['mode']
    if mode == 'strict':
        require(len(attempts) == 1 and attempts[0]['mode'] == 'strict'
                and attempts[0]['exit_code'] == 0 and evidence['strict_green'] is True
                and evidence['after']['distinct_names'] == 0)
    else:
        require(mode == 'naming-only' and policy['eligibility'] == 'naming-only'
                and evidence['after']['distinct_names'] > 0 and evidence['strict_green'] is False
                and len(attempts) == 2 and attempts[0]['mode'] == 'strict'
                and attempts[0]['exit_code'] == 3 and attempts[1]['mode'] == 'naming-only'
                and attempts[1]['exit_code'] == 0)
