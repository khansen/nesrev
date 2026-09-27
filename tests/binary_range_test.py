#!/usr/bin/env python3
"""Buffered extraction and synthetic-ROM fixture compatibility checks."""

import hashlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import copy_binary_range as copier


class CountingReader(io.BytesIO):
    def __init__(self, payload):
        super().__init__(payload)
        self.calls = 0
        self.largest_read = 0

    def read(self, size=-1):
        self.calls += 1
        self.largest_read = max(self.largest_read, size)
        return super().read(size)


class CopyTests(unittest.TestCase):
    def test_exact_range_uses_bounded_bulk_reads(self):
        payload = bytes(range(256)) * 8192 + b'end'
        source = CountingReader(b'header' + payload + b'excluded trailer')
        destination = io.BytesIO()
        copier.copy_range(source, destination, 6, len(payload))
        self.assertEqual(destination.getvalue(), payload)
        self.assertLessEqual(source.calls, 3, 'copy must not degenerate into small-read loops')
        self.assertLessEqual(source.largest_read, 1024 * 1024)

    def test_short_reads_continue_but_early_eof_fails(self):
        class ShortReader(io.BytesIO):
            def read(self, size=-1):
                return super().read(min(size, 3))
        destination = io.BytesIO()
        copier.copy_range(ShortReader(b'prefixpayloadsuffix'), destination, 6, 7)
        self.assertEqual(destination.getvalue(), b'payload')
        with self.assertRaisesRegex(ValueError, 'still missing'):
            copier.copy_range(io.BytesIO(b'abc'), io.BytesIO(), 1, 3)

    def test_negative_ranges_are_refused_before_writing(self):
        for offset, length in ((-1, 1), (0, -1)):
            destination = io.BytesIO(b'keep')
            with self.assertRaises(ValueError):
                copier.copy_range(io.BytesIO(b'abc'), destination, offset, length)
            self.assertEqual(destination.getvalue(), b'keep')

    def test_cli_paths_aliases_and_failure_status(self):
        with tempfile.TemporaryDirectory(prefix='binary copy ') as temporary:
            root = Path(temporary)
            source, destination = root / 'source bytes', root / 'output bytes'
            source.write_bytes(b'prefixPAYLOADtail')
            command = [sys.executable, str(ROOT / 'scripts/copy_binary_range.py'), str(source)]
            result = subprocess.run(command + [str(destination), '6', '7'], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(destination.read_bytes(), b'PAYLOAD')
            alias = root / 'source alias'
            alias.symlink_to(source)
            result = subprocess.run(command + [str(alias), '6', '7'], capture_output=True)
            self.assertEqual(result.returncode, 1)
            self.assertEqual(source.read_bytes(), b'prefixPAYLOADtail')
            result = subprocess.run(command + [str(destination), '6', '100'], capture_output=True)
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'still missing', result.stderr)
            self.assertNotIn(b'Traceback', result.stderr)

    def test_shared_extractor_keeps_trainer_chr_and_trailer_out(self):
        with tempfile.TemporaryDirectory(prefix='extract PRG ') as temporary:
            root = Path(temporary)
            source, destination = root / 'reference.nes', root / 'PRG.bin'
            payload = bytes(range(256)) * 64
            header = b'NES\x1a' + bytes([1, 1, 4, 0]) + bytes(8)
            source.write_bytes(header + b'T' * 512 + payload + b'C' * 8192 + b'trailer')
            command = ['bash', '-c', 'source "$1"; extract_reference_prg_from_ines "$2" "$3"',
                       '_', str(ROOT / 'scripts/project_common.sh'), str(source), str(destination)]
            result = subprocess.run(command, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(destination.read_bytes(), payload)
            source.write_bytes(header + b'T' * 512 + payload + b'C' * 8191)
            result = subprocess.run(command, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn(b'truncated', result.stderr)
            self.assertEqual(destination.read_bytes(), payload)

    def test_shared_extractor_does_not_copy_large_prg_one_byte_at_a_time(self):
        with tempfile.TemporaryDirectory(prefix='large PRG ') as temporary:
            root = Path(temporary)
            source, destination = root / 'reference.nes', root / 'PRG.bin'
            header = b'NES\x1a' + bytes([0, 0, 0, 8, 0, 1]) + bytes(6)
            payload = bytes(range(256)) * 16384
            source.write_bytes(header + payload)
            spy = root / 'dd'
            spy.write_text(f'''#!{sys.executable}
import os, sys
args = dict(arg.split('=', 1) for arg in sys.argv[1:] if '=' in arg)
if args.get('bs') == '1' and int(args.get('count', '0')) > 65536:
    print('refused millions of single-byte transfers', file=sys.stderr)
    raise SystemExit(97)
os.execv({shutil.which('dd')!r}, ['dd', *sys.argv[1:]])
''')
            spy.chmod(0o755)
            command = ['bash', '-c', 'source "$1"; extract_reference_prg_from_ines "$2" "$3"',
                       '_', str(ROOT / 'scripts/project_common.sh'), str(source), str(destination)]
            result = subprocess.run(command, env=dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH']),
                                    capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(destination.read_bytes(), payload)

    def test_synthetic_rom_bytes_match_recorded_baseline_with_one_python_call(self):
        # Digests captured from the unchanged fixture generator at 2159e1f5c.
        cases = [
            ([], 'e9c88e52e31cec67749fe2f8be4fcd18f20bec6e29f355c1d06b74e015d7b074'),
            (['--trainer', '1', '--trailing', '9'], '4360ab712a5559ec71782314b925b615c584e37ec7f994d37d92365b67f0b1ea'),
            (['--prg', '2', '--chr', '0'], '94065add9637e259e332c7e4c10c1304c87daf150b5dd46ef9364f8b1d959fd0'),
            (['--mapper', '1', '--prg', '8', '--chr', '16', '--header-fmt', '2'], '96faaeb30d067c415b960425790d6c4dafba9290d7858c086f843f711d8f0d9f'),
            (['--prg', '0', '--chr', '0'], '4a80675b5031850bedc9e575f3981c75dcf97b7bcb1cb37de065b9d983d820c6'),
        ]
        with tempfile.TemporaryDirectory(prefix='fixture ROM ') as temporary:
            root = Path(temporary)
            out, calls = root / 'fixture.nes', root / 'calls'
            script = '''set -euo pipefail
source "$1"
CALLS="$2"
shift 2
python3() { echo call >> "$CALLS"; command python3 "$@"; }
make_ines "$@"
'''
            for options, expected in cases:
                with self.subTest(options=options):
                    calls.write_text('')
                    result = subprocess.run(['bash', '-c', script, '_', str(ROOT / 'tests/shell/lib.sh'),
                                             str(calls), str(out), *options], capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(hashlib.sha256(out.read_bytes()).hexdigest(), expected)
                    self.assertEqual(calls.read_text().splitlines(), ['call'])


if __name__ == '__main__':
    unittest.main()
