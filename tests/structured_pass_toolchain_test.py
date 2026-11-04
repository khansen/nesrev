"""Release acquisition refuses changed inputs before compiling or retaining them."""
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
from structured_pass import toolchain
from structured_pass.producer import digest


class ReleaseToolchainTests(unittest.TestCase):
    def setUp(self):
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix='release-toolchain-test-', dir=ROOT/'tmp')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.archive = self.root/'release.tar.gz'
        self.store = self.root/'store'
        self.schema = b'{"test_schema": 1}\n'
        self.pin = {'repository': 'https://example.invalid/assembler', 'release': '9.8.7',
                    'commit': 'a'*40, 'archive_url': 'https://example.invalid/release.tar.gz',
                    'schema_sha256': digest(self.schema)}
        self.pin_path = self.root/'pin.json'
        self.patch = mock.patch.object(toolchain, 'PIN', self.pin_path)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.package()

    def package(self, extra=()):
        data = io.BytesIO()
        with tarfile.open(fileobj=data, mode='w:gz') as archive:
            info = tarfile.TarInfo('xorcyst-9.8.7/doc/source-model.schema.json')
            info.size = len(self.schema)
            archive.addfile(info, io.BytesIO(self.schema))
            for info, content in extra:
                archive.addfile(info, io.BytesIO(content))
        self.archive.write_bytes(data.getvalue())
        self.pin['archive_sha256'] = digest(data.getvalue())
        self.pin_path.write_text(json.dumps(self.pin))

    def compile(self, command, *, cwd, **kwargs):
        if command == ['make', '-j2']:
            for name in ('xasm', 'xlnk'):
                (Path(cwd)/name).write_bytes(('synthetic '+name).encode())
        return subprocess.CompletedProcess(command, 0)

    def output(self, command, **kwargs):
        if command == ['cc', '--version']:
            return 'Synthetic compiler for unit test\n'
        name = Path(command[0]).name
        self.assertIn(name, ('xasm', 'xlnk'))
        self.assertEqual(command[1:], ['--version'])
        return name+' 9.8.7\n'

    def test_release_archive_and_recipe_are_retained(self):
        original = self.archive.read_bytes()
        with mock.patch.object(toolchain.subprocess, 'run', side_effect=self.compile), \
             mock.patch.object(toolchain.subprocess, 'check_output', side_effect=self.output):
            result = toolchain.build(self.archive, self.store)
        destination = Path(result['producer']).parent
        self.assertEqual((destination/'source.tar.gz').read_bytes(), original)
        self.assertEqual((destination/'local.patch').read_bytes(), b'')
        self.assertEqual(Path(result['linker']).read_bytes(), b'synthetic xlnk')
        self.assertEqual(Path(result['producer']).stat().st_mode & 0o777, 0o755)
        recipe = json.loads((destination/'REBUILD-v2.json').read_text())
        for field in ('repository', 'commit', 'release', 'archive_url'):
            self.assertEqual(recipe[field], self.pin[field])
        self.assertEqual(recipe['source_archive_sha256'], self.pin['archive_sha256'])
        self.assertEqual(recipe['source_schema_sha256'], self.pin['schema_sha256'])
        self.assertEqual(recipe['source_directory'], 'xorcyst-9.8.7')
        self.assertEqual(recipe['producer_sha256'], digest(b'synthetic xasm'))
        self.assertEqual(recipe['linker_sha256'], digest(b'synthetic xlnk'))
        self.assertEqual(list(self.store.glob('producer-build-*')), [])

    def test_bad_checksum_refuses_before_archive_parsing(self):
        self.pin['archive_sha256'] = '0'*64
        self.pin_path.write_text(json.dumps(self.pin))
        with mock.patch.object(toolchain.tarfile, 'open', wraps=tarfile.open) as unpack, \
             mock.patch.object(toolchain.subprocess, 'run', side_effect=self.compile) as compile, \
             mock.patch.object(toolchain.subprocess, 'check_output', side_effect=self.output):
            with self.assertRaisesRegex(ValueError, '^PRODUCER_ARCHIVE_CHANGED$'):
                toolchain.build(self.archive, self.store)
        unpack.assert_not_called()
        compile.assert_not_called()

    def test_unsafe_or_duplicate_members_refuse_before_build(self):
        entries = []
        for name in ('/outside', 'xorcyst-9.8.7/../../outside', 'other/configure',
                     'xorcyst-9.8.7/doc/source-model.schema.json'):
            entries.append(tarfile.TarInfo(name))
        link = tarfile.TarInfo('xorcyst-9.8.7/escape')
        link.type = tarfile.SYMTYPE
        link.linkname = '/outside'
        entries.append(link)
        for info in entries:
            with self.subTest(name=info.name):
                self.package([(info, b'')])
                with mock.patch.object(toolchain.subprocess, 'run') as compile:
                    with self.assertRaisesRegex(ValueError, '^PRODUCER_SOURCE_CHANGED$'):
                        toolchain.build(self.archive, self.store)
                compile.assert_not_called()

    def test_wrong_schema_refuses_before_build(self):
        self.pin['schema_sha256'] = '0'*64
        self.pin_path.write_text(json.dumps(self.pin))
        with mock.patch.object(toolchain.subprocess, 'run', side_effect=self.compile) as compile, \
             mock.patch.object(toolchain.subprocess, 'check_output', side_effect=self.output):
            with self.assertRaisesRegex(ValueError, '^PRODUCER_SOURCE_CHANGED$'):
                toolchain.build(self.archive, self.store)
        compile.assert_not_called()

    def test_wrong_tool_version_is_not_retained(self):
        for tool in ('xasm', 'xlnk'):
            def wrong(command, **kwargs):
                return tool+' 0.0.0\n' if Path(command[0]).name == tool else self.output(command, **kwargs)
            with self.subTest(tool=tool), \
                 mock.patch.object(toolchain.subprocess, 'run', side_effect=self.compile), \
                 mock.patch.object(toolchain.subprocess, 'check_output', side_effect=wrong):
                with self.assertRaisesRegex(ValueError, '^PRODUCER_VERSION_MISMATCH$'):
                    toolchain.build(self.archive, self.store)
            self.assertFalse((self.store/'toolchains').exists())

    def test_build_uses_the_checked_archive_snapshot(self):
        original = self.archive.read_bytes()
        def replace_input(command, **kwargs):
            self.archive.write_bytes(b'changed after capture')
            return self.compile(command, **kwargs)
        with mock.patch.object(toolchain.subprocess, 'run', side_effect=replace_input), \
             mock.patch.object(toolchain.subprocess, 'check_output', side_effect=self.output):
            result = toolchain.build(self.archive, self.store)
        self.assertEqual((Path(result['producer']).parent/'source.tar.gz').read_bytes(), original)


if __name__ == '__main__':
    unittest.main()
