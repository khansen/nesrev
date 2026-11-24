"""Observe phase descendants, including children with separate process groups.

Only selected descendants/bridges leave the in-memory host snapshot. Sampling
is not an execution trace and cannot prove absence of arbitrarily short tasks.
"""
import os
import ctypes
import errno
from functools import lru_cache
from pathlib import Path
import signal
import subprocess
import sys
import time


def _ps_snapshot():
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


class _BSDShortInfo(ctypes.Structure):
    # Public proc_bsdshortinfo ABI; unlike full BSD info this permits other UIDs.
    _fields_ = [(name, ctypes.c_uint32) for name in ('pid', 'ppid', 'pgid', 'status')
                ] + [('comm', ctypes.c_char * 16)] + [
        (name, ctypes.c_uint32) for name in
        ('flags', 'uid', 'gid', 'ruid', 'rgid', 'svuid', 'svgid', 'reserved')]


class _KInfoPrefix(ctypes.Structure):
    # Public extern_proc prefix in sys/proc.h, through p_pid. The timeval is
    # padded to pointer alignment, on both supported 64-bit Darwin architectures.
    _fields_ = [('seconds', ctypes.c_long), ('microseconds', ctypes.c_int),
                ('vmspace', ctypes.c_void_p), ('sigacts', ctypes.c_void_p),
                ('flags', ctypes.c_int), ('status', ctypes.c_byte), ('pid', ctypes.c_int)]


@lru_cache(maxsize=1)
def _darwin_api():
    api = ctypes.CDLL('/usr/lib/libSystem.B.dylib', use_errno=True)
    api.proc_listallpids.argtypes = [ctypes.c_void_p, ctypes.c_int]
    api.proc_listallpids.restype = ctypes.c_int
    api.proc_pidinfo.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64,
                                ctypes.c_void_p, ctypes.c_int]
    api.proc_pidinfo.restype = ctypes.c_int
    api.sysctl.argtypes = [ctypes.POINTER(ctypes.c_int), ctypes.c_uint,
                          ctypes.c_void_p, ctypes.POINTER(ctypes.c_size_t),
                          ctypes.c_void_p, ctypes.c_size_t]
    api.sysctl.restype = ctypes.c_int
    api.strvis.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int]
    api.strvis.restype = ctypes.c_int
    api.uselocale.argtypes = [ctypes.c_void_p]
    api.uselocale.restype = ctypes.c_void_p
    return api


def _snapshot_error(stage, *, mib=None, pid=None, error=0):
    return ValueError('CODEX_PROCESS_SNAPSHOT_INVALID '
                      f'stage={stage} mib={mib} pid={pid} errno={error}')


def _sysctl(api, mib, buffer):
    keys = (ctypes.c_int * len(mib))(*mib)
    size = ctypes.c_size_t(ctypes.sizeof(buffer))
    pid = mib[-1] if mib[:2] in ((1, 14), (1, 49)) else None
    ctypes.set_errno(0)
    if api.sysctl(keys, len(keys), ctypes.byref(buffer), ctypes.byref(size), None, 0):
        error = ctypes.get_errno()
        raise OSError(error, f'process sysctl failed mib={mib} pid={pid} errno={error}')
    if size.value > ctypes.sizeof(buffer):
        raise _snapshot_error('sysctl-size', mib=mib, pid=pid)
    return size.value


def _argv_bytes(data):
    if len(data) < 4:
        raise ValueError('CODEX_PROCESS_SNAPSHOT_INVALID')
    argc = int.from_bytes(data[:4], sys.byteorder, signed=True)
    end = data.find(b'\0', 4)
    if argc <= 0 or end < 0:
        raise ValueError('CODEX_PROCESS_SNAPSHOT_INVALID')
    start = end
    while start < len(data) and data[start] == 0:
        start += 1
    args = data[start:].split(b'\0')
    if len(args) <= argc or not args[0]:
        raise ValueError('CODEX_PROCESS_SNAPSHOT_INVALID')
    # The sysctl buffer also contains the environment; never render beyond argc.
    return b' '.join(args[:argc])


def _darwin_command(api, info, argmax):
    fallback = b'(' + bytes(info.comm) + b')'
    if info.status == 5:  # SZOMB
        raw = b'<defunct>'
    else:
        buffer = ctypes.create_string_buffer(argmax)
        try:
            size = _sysctl(api, (1, 49, info.pid), buffer)  # CTL_KERN, KERN_PROCARGS2
            raw = _argv_bytes(buffer.raw[:size])
        except (OSError, ValueError):
            # Exec can make argv unavailable or inconsistent while process
            # metadata remains valid. Match ps without losing the identity row.
            raw = fallback
    visible = ctypes.create_string_buffer(len(raw) * 4 + 1)
    # Match ps's LC_ALL=C without changing the process-wide Python locale.
    old_locale = api.uselocale(ctypes.c_void_p.in_dll(api, '_c_locale'))
    if not old_locale:
        raise _snapshot_error('uselocale', mib=(1, 49, info.pid), pid=info.pid,
                              error=ctypes.get_errno())
    try:
        if api.strvis(visible, raw, 0x8 | 0x10 | 0x40) < 0:  # TAB | NL | NOSLASH
            raise _snapshot_error('strvis', mib=(1, 49, info.pid), pid=info.pid,
                                  error=ctypes.get_errno())
    finally:
        api.uselocale(old_locale)
    return visible.value.decode('utf-8', errors='replace')


def _darwin_snapshot():
    api = _darwin_api()
    ctypes.set_errno(0)
    count = api.proc_listallpids(None, 0)
    if count <= 0:
        raise _snapshot_error('proc_listallpids', error=ctypes.get_errno())
    for _ in range(4):
        capacity = count + 128
        pids = (ctypes.c_int * capacity)()
        ctypes.set_errno(0)
        count = api.proc_listallpids(pids, ctypes.sizeof(pids))
        if count <= 0:
            raise _snapshot_error('proc_listallpids', error=ctypes.get_errno())
        if count < capacity:
            break
    else:
        raise _snapshot_error('proc_listallpids-capacity')
    argmax = ctypes.c_int()
    _sysctl(api, (1, 8), argmax)  # CTL_KERN, KERN_ARGMAX
    if not 0 < argmax.value <= 16 * 1024 * 1024:
        raise _snapshot_error('argmax', mib=(1, 8))
    rows = {}
    for pid in pids[:count]:
        if pid <= 0:
            continue
        info = _BSDShortInfo()
        ctypes.set_errno(0)
        size = api.proc_pidinfo(pid, 13, 0, ctypes.byref(info), ctypes.sizeof(info))
        if size == 0 and ctypes.get_errno() == errno.ESRCH:
            continue  # Exited between enumeration and inspection.
        if size != ctypes.sizeof(info) or info.pid != pid:
            raise _snapshot_error('proc_pidinfo', pid=pid, error=ctypes.get_errno())
        kernel = ctypes.create_string_buffer(1024)
        try:
            size = _sysctl(api, (1, 14, 1, pid), kernel)  # KERN_PROC_PID
        except OSError as error:
            if error.errno == errno.ESRCH:
                continue
            raise
        if size == 0:
            continue  # KERN_PROC_PID also represents an exited PID as no rows.
        if size < ctypes.sizeof(_KInfoPrefix):
            raise _snapshot_error('kernel-size', mib=(1, 14, 1, pid), pid=pid)
        prefix = _KInfoPrefix.from_buffer_copy(kernel)
        if prefix.pid != pid:
            raise _snapshot_error('kernel-pid', mib=(1, 14, 1, pid), pid=pid)
        try:
            stamp = time.localtime(prefix.seconds)
        except (ValueError, OverflowError, OSError) as error:
            raise _snapshot_error('kernel-start-time', mib=(1, 14, 1, pid), pid=pid,
                                  error=getattr(error, 'errno', 0)) from error
        started = ('Mon Tue Wed Thu Fri Sat Sun'.split()[stamp.tm_wday] + ' ' +
                   'Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec'.split()[stamp.tm_mon - 1] +
                   f' {stamp.tm_mday} {stamp.tm_hour:02}:{stamp.tm_min:02}:{stamp.tm_sec:02} {stamp.tm_year}')
        rows[pid] = {'pid': pid, 'ppid': info.ppid, 'pgid': info.pgid,
                     'started': started, 'command': _darwin_command(api, info, argmax.value)}
    if os.getpid() not in rows:
        raise _snapshot_error('self-missing', pid=os.getpid())
    return rows


def snapshot():
    return _darwin_snapshot() if sys.platform == 'darwin' else _ps_snapshot()


def same_process(left, right):
    return left['pid'] == right['pid'] and left['started'] == right['started']


def bridge_matches(row, config):
    if not config:
        return False
    # ps renders argv with spaces. Match the complete fixed script/argument
    # suffix, including the absolute session and role, never a substring slug.
    bridge = Path(config['service_root']) / 'scripts/structured_pass_bridge.py'
    return row['command'].endswith(' ' + str(bridge) + ' --mcp ' +
        config.get('bridge_root',config['session']) + ' implementer ' + config.get('service_profile','corridor'))


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
