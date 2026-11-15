#!/usr/bin/env python3
"""Run isolated Bash test functions sequentially, with timings and explicit scope."""

import argparse
from datetime import datetime, timezone
import fnmatch
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent.parent
DISCOVER = '''set -euo pipefail
source "$1" >/dev/null
compgen -A function test_ > "$2" || true
'''
RUN = '''set -euo pipefail
source "$SCRIPT_DIR/lib.sh"
source "$1"
"$2"
'''


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', help='shell glob matching the suite name (without _test.sh)')
    parser.add_argument('--test', help='shell glob matching a full suite::test_function identifier')
    parser.add_argument('--list', action='store_true', help='discover selected tests without running their bodies')
    parser.add_argument('--json', type=Path, help='write a machine-readable shell-run report')
    parser.add_argument('--slowest', type=int, default=10, help='number of slowest entries to print (default: 10)')
    args = parser.parse_args()
    if args.suite == '' or args.test == '':
        parser.error('filters must not be empty')
    if args.slowest < 0:
        parser.error('--slowest must be nonnegative')
    if args.list and args.json:
        parser.error('--list cannot publish an execution report with --json')
    return args


def publish(path, report):
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    # A complete report replaces the initial incomplete report atomically.
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, prefix='.' + path.name,
                                     suffix='.tmp', delete=False, encoding='utf-8') as output:
        temporary = Path(output.name)
        try:
            json.dump(report, output, indent=2)
            output.write('\n')
            output.close()
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def diagnostics(path, stream):
    for line in path.read_text(errors='replace').splitlines():
        print('      | ' + line, file=stream)


def entry(label, kind, rc, elapsed):
    return {'id': label, 'kind': kind, 'status': 'passed' if rc == 0 else 'failed',
            'exit_code': rc, 'elapsed_seconds': elapsed}


def run(args, report):
    env = dict(os.environ, REPO_ROOT=str(ROOT), SCRIPT_DIR=str(SCRIPT_DIR))
    # Nested fixture Make invocations must not inherit the outer run's filters
    # or overwrite its JSON report through command-line variable propagation.
    for name in ('MAKEFLAGS', 'MFLAGS', 'MAKEOVERRIDES', 'TEST_SUITE', 'TEST_CASE', 'TEST_JSON'):
        env.pop(name, None)
    files = sorted((SCRIPT_DIR / 'cases').glob('*_test.sh'))
    if not files:
        raise ValueError('no test files in tests/shell/cases/')
    suites = [file for file in files if fnmatch.fnmatchcase(file.name[:-8], args.suite or '*')]
    if not suites:
        raise ValueError('suite filter matched no suites')
    scope = 'FILTERED' if report['selection']['filtered'] else 'FULL'
    print(f'Selection: {scope}; suite={args.suite or "*"!r}; test={args.test or "*"!r}',
          file=sys.stderr if args.list else sys.stdout, flush=True)
    selected = []
    rows = report['results']
    discovery_start = time.monotonic()
    for file in suites:
        suite = file.name[:-8]
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix='nesrev_discovery.') as directory:
            directory = Path(directory)
            names = directory / 'functions'
            stderr = directory / 'stderr'
            with stderr.open('wb') as errors:
                result = subprocess.run(['bash', '-c', DISCOVER, '_', str(file), str(names)],
                                        cwd=ROOT, env=env, stdout=subprocess.DEVNULL, stderr=errors)
            functions = sorted(names.read_text().splitlines()) if result.returncode == 0 and names.exists() else []
            if result.returncode or not functions:
                kind = 'source' if result.returncode else 'no-tests'
                label = f'{suite}::<{kind}>'
                rows.append(entry(label, kind, result.returncode or 1, time.monotonic() - started))
                print(f'FAIL  {label} (suite discovery failed)', file=sys.stderr, flush=True)
                diagnostics(stderr, sys.stderr)
                continue
            report['discovered_tests'] += len(functions)
            selected.extend((file, fn, f'{suite}::{fn}') for fn in functions
                            if fnmatch.fnmatchcase(f'{suite}::{fn}', args.test or '*'))
    report['discovery_seconds'] = time.monotonic() - discovery_start
    report['selected_tests'] = [label for _, _, label in selected]
    if not selected and not rows:
        raise ValueError('test filter matched no tests')
    if args.list:
        for _, _, label in selected:
            print(label)
        return 1 if rows else 0
    print(f'Selected {len(selected)} test(s) from {len(suites)} suite(s); '
          f'{len(rows)} discovery failure(s).', flush=True)
    for file, function, label in selected:
        print(f'RUN   {label}', flush=True)
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix='nesrev_shtest.') as directory:
            directory = Path(directory)
            stdout, stderr = directory / 'stdout', directory / 'stderr'
            # Run Bash directly, never as an if-condition: that would disable
            # errexit inside the test and hide non-final command failures.
            with stdout.open('wb') as out, stderr.open('wb') as err:
                result = subprocess.run(['bash', '-c', RUN, '_', str(file), function],
                                        cwd=ROOT, env=dict(env, NESREV_TEST_TMPDIR=str(directory)),
                                        stdout=out, stderr=err)
            row = entry(label, 'test', result.returncode, time.monotonic() - started)
            rows.append(row)
            prefix = 'PASS' if result.returncode == 0 else 'FAIL'
            print(f'{prefix}  {label} ({row["elapsed_seconds"]:.3f}s; exit {result.returncode})', flush=True)
            if result.returncode:
                diagnostics(stderr, sys.stderr)
                diagnostics(stdout, sys.stdout)
    report['complete'] = True
    return 1 if any(row['exit_code'] for row in rows) else 0


def main():
    args = arguments()
    started = time.monotonic()
    report = {'version': 1, 'started_at': datetime.now(timezone.utc).isoformat(),
              'selection': {'filtered': bool(args.suite or args.test), 'suite': args.suite, 'test': args.test},
              'complete': False, 'status': 'running', 'discovered_tests': 0,
              'selected_tests': [], 'discovery_seconds': 0.0, 'results': []}
    try:
        # Invalidate an older successful report before any discovery or tests.
        publish(args.json, report)
        rc = run(args, report)
        report['status'] = ('listed' if args.list else 'passed') if rc == 0 else 'failed'
    except (OSError, ValueError) as error:
        print(f'shell runner: {error}', file=sys.stderr)
        report['status'], report['error'], rc = 'error', str(error), 2
    except KeyboardInterrupt:
        print('shell runner: interrupted', file=sys.stderr)
        report['status'], rc = 'interrupted', 130
    report['elapsed_seconds'] = time.monotonic() - started
    report['exit_code'] = rc
    rows = report['results']
    failed = sum(row['exit_code'] != 0 for row in rows)
    report['counts'] = {'total': len(rows), 'passed': len(rows) - failed, 'failed': failed}
    if not args.list:
        if report['complete']:
            summary = f'{failed} failed of {len(rows)}' if failed else f'{len(rows)} passed'
            print(f'\nshell tests: {summary}')
        else:
            print(f'\nshell tests: incomplete ({report["status"]})')
        print(f'Elapsed: {report["elapsed_seconds"]:.3f}s '
              f'(discovery: {report["discovery_seconds"]:.3f}s)')
        if args.slowest and rows:
            print('Slowest entries (includes setup/source and test subprocess; excludes cleanup):')
            for row in sorted(rows, key=lambda row: (-row['elapsed_seconds'], row['id']))[:args.slowest]:
                print(f'  {row["elapsed_seconds"]:9.3f}s  {row["status"]:6}  {row["id"]}')
    try:
        publish(args.json, report)
    except OSError as error:
        print(f'shell runner: cannot publish report: {error}', file=sys.stderr)
        return 2
    return rc


if __name__ == '__main__':
    sys.exit(main())
