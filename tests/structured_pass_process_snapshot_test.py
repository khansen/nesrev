"""Native process inspection preserves cleanup identities without setuid tools."""
import ctypes
import errno
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import structured_client_processes as processes


class SnapshotTests(unittest.TestCase):
    def test_listing_failure_never_reports_quiescence(self):
        for count in (-1, 0):
            api = Mock()
            api.proc_listallpids.return_value = count
            with patch.object(processes.sys, 'platform', 'darwin'), patch.object(processes, '_darwin_api', return_value=api):
                with self.assertRaisesRegex(ValueError, r'^CODEX_PROCESS_SNAPSHOT_INVALID stage=proc_listallpids mib=None pid=None errno=0$'):
                    processes.require_quiescent({'runs': []})
                child = Mock()
                with self.assertRaisesRegex(ValueError, r'^CODEX_PROCESS_SNAPSHOT_INVALID stage=proc_listallpids mib=None pid=None errno=0$'):
                    processes.stop_tree(child, {}, None, lambda: None)
                child.wait.assert_not_called()

    def test_argv_excludes_environment_and_refuses_malformed_buffer(self):
        data = (3).to_bytes(4, sys.byteorder) + b'/bin/test\0\0test\0a b\0\0SECRET=hidden\0'
        self.assertEqual(processes._argv_bytes(data), b'test a b ')
        for bad in (b'', data[:9], data[:24], b'\0' * 50):
            with self.assertRaisesRegex(ValueError, '^CODEX_PROCESS_SNAPSHOT_INVALID$'):
                processes._argv_bytes(bad)

    @unittest.skipUnless(sys.platform == 'darwin', 'Darwin libproc/sysctl ABI and Seatbelt')
    def test_exited_and_unreadable_argv_keeps_process_visible(self):
        api = processes._darwin_api()
        for name in (b'git', b'Python', b'other-user'):
            info = processes._BSDShortInfo(pid=123, comm=name)
            for error in (errno.EPERM, errno.EACCES, errno.ESRCH, errno.EINVAL,
                          errno.EIO, errno.ENOMEM):
                with patch.object(processes, '_sysctl', side_effect=OSError(error, 'unreadable')):
                    self.assertEqual(processes._darwin_command(api, info, 4096), '(' + name.decode() + ')')
            for malformed in (b'', b'\0' * 12, b'\x02\0\0\0/bin/git\0\0git\0'):
                def read_buffer(api, mib, buffer):
                    buffer.raw = malformed + b'\0' * (len(buffer) - len(malformed))
                    return len(malformed)
                with patch.object(processes, '_sysctl', side_effect=read_buffer):
                    self.assertEqual(processes._darwin_command(api, info, 4096), '(' + name.decode() + ')')

    def test_metadata_and_argmax_errors_remain_fatal_and_attributed(self):
        pid = os.getpid()
        api = Mock()
        def list_pids(buffer, size):
            if buffer is not None:buffer[0] = pid
            return 1
        def pidinfo(selected, flavor, arg, buffer, size):
            info = ctypes.cast(buffer, ctypes.POINTER(processes._BSDShortInfo)).contents
            info.pid = selected
            return size
        api.proc_listallpids.side_effect = list_pids
        api.proc_pidinfo.side_effect = pidinfo
        for failed in ((1, 8), (1, 14, 1, pid)):
            def sysctl(keys, count, buffer, size, *_):
                mib = tuple(keys[i] for i in range(count))
                if mib == failed:
                    ctypes.set_errno(errno.EIO)
                    return -1
                self.assertEqual(mib, (1, 8))
                ctypes.cast(buffer, ctypes.POINTER(ctypes.c_int)).contents.value = 4096
                return 0
            api.sysctl.side_effect = sysctl
            with patch.object(processes.sys, 'platform', 'darwin'), patch.object(processes, '_darwin_api', return_value=api):
                with self.assertRaises(OSError) as caught:processes.snapshot()
            self.assertEqual(caught.exception.errno, errno.EIO)
            self.assertIn('mib=' + str(failed), str(caught.exception))
            self.assertIn('pid=' + str(pid if len(failed) == 4 else None), str(caught.exception))
            self.assertIn('errno=5', str(caught.exception))

    def test_pidinfo_failure_and_missing_self_remain_fatal(self):
        pid = os.getpid()
        api = Mock()
        def list_pids(buffer, size):
            if buffer is not None:buffer[0] = pid
            return 1
        api.proc_listallpids.side_effect = list_pids
        for failure in (errno.EIO, errno.ESRCH):
            def pidinfo(*_):
                ctypes.set_errno(failure)
                return 0
            api.proc_pidinfo.side_effect = pidinfo
            with patch.object(processes.sys, 'platform', 'darwin'), patch.object(processes, '_darwin_api', return_value=api), patch.object(processes, '_sysctl', side_effect=lambda a,m,b:setattr(b,'value',4096)):
                with self.assertRaises(ValueError) as caught:processes.snapshot()
            expected = 'stage=proc_pidinfo' if failure == errno.EIO else 'stage=self-missing'
            self.assertIn(expected, str(caught.exception))
            self.assertIn('pid=' + str(pid), str(caught.exception))
            self.assertIn('errno=' + str(failure if failure == errno.EIO else 0), str(caught.exception))

    @unittest.skipUnless(sys.platform == 'darwin', 'Darwin libproc/sysctl ABI')
    def test_argv_exec_race_preserves_complete_snapshot_row(self):
        pid = os.getpid()
        before = processes.snapshot()[pid]
        api = processes._darwin_api()
        info = processes._BSDShortInfo()
        self.assertEqual(api.proc_pidinfo(pid, 13, 0, ctypes.byref(info), ctypes.sizeof(info)), ctypes.sizeof(info))
        original = processes._sysctl
        for failure in ('EIO', 'malformed'):
            def read(api, mib, buffer):
                if mib != (1, 49, pid):return original(api, mib, buffer)
                if failure == 'EIO':raise OSError(errno.EIO, 'exec race')
                return 0
            with patch.object(processes, '_sysctl', side_effect=read):
                row = processes.snapshot()[pid]
            self.assertEqual(row, {**before, 'command':'(' + bytes(info.comm).decode() + ')'})

    @unittest.skipUnless(sys.platform == 'darwin', 'Compare Darwin native inspection with the system ps')
    def test_equivalence_and_loopback_sandbox(self):
        child = subprocess.Popen([sys.executable, '-B', '-c', 'import time; time.sleep(30)',
                                  'space in argument', 'tab\tand\nnewline', 'unicode-\u00e9'])
        try:
            time.sleep(.05)
            before = processes._ps_snapshot()
            native = processes.snapshot()
            after = processes._ps_snapshot()
            stable = {pid for pid in before.keys() & after.keys() if before[pid] == after[pid]}
            self.assertIn(child.pid, stable)
            self.assertEqual(native[child.pid], before[child.pid])
            self.assertGreater(len(stable), 1)
            for pid in stable:
                with self.subTest(pid=pid):
                    self.assertIn(pid, native)
                    for key in ('pid', 'ppid', 'pgid', 'started'):
                        self.assertEqual(native[pid][key], before[pid][key])
                    if native[pid]['command'] != before[pid]['command']:
                        # Other UIDs and an exec between the two ps reads can
                        # make argv unavailable without losing process metadata.
                        info = processes._BSDShortInfo()
                        api = processes._darwin_api()
                        self.assertEqual(api.proc_pidinfo(pid, 13, 0, ctypes.byref(info), ctypes.sizeof(info)), ctypes.sizeof(info))
                        self.assertEqual(native[pid]['command'], '(' + bytes(info.comm).decode() + ')')
            script = ('import json,sys;sys.path.insert(0,sys.argv[1]);'
                      'import structured_client_processes as p;print(json.dumps(p.snapshot()[int(sys.argv[2])]))')
            sandbox = '(version 1)(allow default)(deny network*)(allow network* (remote ip "localhost:*"))'
            result = subprocess.run(['/usr/bin/sandbox-exec', '-p', sandbox,
                                     sys.executable, '-B', '-c', script, str(ROOT/'scripts'), str(child.pid)],
                                    capture_output=True, text=True, check=True)
            self.assertEqual(json.loads(result.stdout), native[child.pid])
        finally:
            child.terminate();child.wait(timeout=5)


if __name__ == '__main__':unittest.main()
