"""Observe phase descendants, including children with separate process groups.

Only selected descendants/bridges leave the in-memory host snapshot. Sampling
is not an execution trace and cannot prove absence of arbitrarily short tasks.
"""
import os
from pathlib import Path
import signal
import subprocess
import time


def snapshot():
    result = subprocess.run(['/bin/ps', '-axww', '-o', 'pid=,ppid=,pgid=,lstart=,command='],
                            capture_output=True, text=True, check=True,
                            env={**os.environ, 'LC_ALL': 'C'})
    rows = {}
    for line in result.stdout.splitlines():
        parts = line.split(None, 8)
        if len(parts) != 9:
            raise ValueError('CODEX_PROCESS_SNAPSHOT_INVALID')
        pid, ppid, pgid = map(int, parts[:3])
        rows[pid] = {'pid': pid, 'ppid': ppid, 'pgid': pgid,
                     'started': ' '.join(parts[3:8]), 'command': parts[8]}
    return rows


def same_process(left, right):
    return left['pid'] == right['pid'] and left['started'] == right['started']


def bridge_matches(row, config):
    if not config:
        return False
    # ps renders argv with spaces. Match the complete fixed script/argument
    # suffix, including the absolute session and role, never a substring slug.
    bridge = Path(config['service_root']) / 'scripts/structured_pass_bridge.py'
    return row['command'].endswith(' ' + str(bridge) + ' --mcp ' + config['session'] + ' implementer corridor')


def descendants(rows, root_pid, known=(), config=None):
    roots = [old for old in known if old['pid'] == root_pid]
    selected = {pid: row for pid, row in rows.items() if (pid == root_pid and
                (not roots or any(same_process(row, old) for old in roots))) or bridge_matches(row, config)
                or any(same_process(row, old) for old in known)}
    while True:
        more = {pid: row for pid, row in rows.items() if row['ppid'] in selected}
        if set(more) <= set(selected):
            return selected
        selected.update(more)


def observe(row, config, rows=None):
    rows = snapshot() if rows is None else rows
    known = row.setdefault('processes', [])
    selected = descendants(rows, row.get('client_pgid'), known, config)
    changed = False
    for item in selected.values():
        if not any(same_process(item, old) and item['pgid'] == old['pgid'] for old in known):
            known.append(dict(item))
            changed = True
    return changed, selected


def group_alive(pgid):
    if type(pgid) is not int or pgid <= 1:
        raise ValueError('CODEX_CLIENT_GROUP_INVALID')
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def live_groups(run, rows):
    """Ignore reissued group numbers; retain surviving leaderless groups."""
    known = run.get('processes', [])
    groups = {old['pgid'] for old in known}
    if run.get('client_pgid') is not None:
        groups.add(run['client_pgid'])
    live = set()
    for pgid in groups:
        if type(pgid) is not int or pgid <= 1:
            raise ValueError('CODEX_CLIENT_GROUP_INVALID')
        if not any(row['pgid'] == pgid for row in rows.values()):
            continue
        leader = rows.get(pgid)
        recorded = [old for old in known if old['pid'] == pgid]
        # Missing identity (e.g. SIGKILL before the first observation) cannot
        # prove reuse. A group without its leader likewise remains unresolved.
        if leader is None or not recorded or any(same_process(leader, old) for old in recorded):
            live.add(pgid)
    return live


def require_quiescent(state, config=None):
    rows = snapshot()
    if any(bridge_matches(row, config) for row in rows.values()):
        raise ValueError('CODEX_SESSION_BRIDGE_ALIVE')
    for run in state['runs']:
        if run.get('processes_reconciled') is True:
            continue
        groups = live_groups(run, rows)
        if run.get('client_pgid') in groups:
            raise ValueError('CODEX_CLIENT_GROUP_ALIVE')
        for old in run.get('processes', []):
            if old['pid'] in rows and same_process(old, rows[old['pid']]):
                raise ValueError('CODEX_DESCENDANT_ALIVE')
        if groups:
            raise ValueError('CODEX_DESCENDANT_GROUP_ALIVE')


def stop_tree(process, row, config, persist):
    if process is None:
        return
    sent_term = set()
    deadline = time.monotonic() + .5
    while True:
        process.poll()  # Reap an exited leader before signalling its group.
        rows = snapshot()
        changed, selected = observe(row, config, rows)
        if changed:
            persist()
        groups = live_groups(row, rows)
        for pgid in groups:
            if pgid <= 1 or pgid == os.getpgrp():
                raise ValueError('CODEX_PROCESS_GROUP_UNSAFE')
            # A current identity proves this is still one of our groups.
            owned = any(item['pgid'] == pgid for item in selected.values())
            if not owned:
                raise ValueError('CODEX_PROCESS_GROUP_IDENTITY_UNCERTAIN')
            sig = signal.SIGTERM if time.monotonic() < deadline else signal.SIGKILL
            if sig == signal.SIGTERM and pgid in sent_term:
                continue
            try:
                os.killpg(pgid, sig)
            except ProcessLookupError:
                pass
            except PermissionError:
                # A group can still be exiting when macOS refuses the signal.
                # Retry within the same deadline; never report success until
                # every group is gone. Persistent refusal fails below.
                process.poll()
                continue
            sent_term.add(pgid)
        process.poll()  # Reap our child so it cannot keep its group alive.
        if not live_groups(row, snapshot()):
            break
        if time.monotonic() > deadline + .7:
            raise ValueError('CODEX_PROCESS_CLEANUP_INCOMPLETE')
        time.sleep(.02)
    process.wait(timeout=.1)
    require_quiescent({'runs': [row]}, config)
