"""Run opted-in, independent unittest cases in two separate worker processes.

Use only for cases whose mutable files, environment and working directory are
private to each test and restored by its fixtures. Class/module fixtures are not
supported: splitting them would change their lifetime. Explicit unittest
selections still run serially, for debugging. This does not parallelize the
shell harness.
"""

from concurrent.futures import Future, ProcessPoolExecutor
from contextlib import redirect_stderr, redirect_stdout
import multiprocessing
import os
from pathlib import Path
import sys
import tempfile
import unittest


def run_one(case, name, log_path):
    # Capture inherited subprocess descriptors as well as Python prints, so
    # concurrent assembler diagnostics stay with their owning test's report.
    # The parent owns this path: a worker crash must not discard flushed output.
    with open(log_path, "w", encoding="utf-8", buffering=1) as output:
        sys.stdout.flush()
        sys.stderr.flush()
        saved = os.dup(1), os.dup(2)
        try:
            os.dup2(output.fileno(), 1)
            os.dup2(output.fileno(), 2)
            with redirect_stdout(output), redirect_stderr(output):
                result = unittest.TextTestRunner(stream=output, verbosity=2).run(
                    unittest.TestSuite([case(name)]))
            output.flush()
        finally:
            for target, descriptor in zip((1, 2), saved):
                os.dup2(descriptor, target)
                os.close(descriptor)
        return result.wasSuccessful()


def run(case):
    for name in ("setUpClass", "tearDownClass"):
        method = getattr(case, name)
        if getattr(method, "__func__", method) is not getattr(unittest.TestCase, name).__func__:
            raise ValueError("isolated test case cannot use class fixtures")
    module = sys.modules[case.__module__]
    if any(hasattr(module, name) for name in ("setUpModule", "tearDownModule")):
        raise ValueError("isolated test case cannot use module fixtures")
    names = unittest.defaultTestLoader.getTestCaseNames(case)
    if not names:
        raise ValueError("isolated test case has no tests")
    failed = 0
    # Spawn also on platforms whose default is fork: inherited module state and
    # open descriptors must not couple worker fixtures to the parent process.
    with tempfile.TemporaryDirectory(prefix="nesrev-case-logs-") as directory:
        jobs = []
        with ProcessPoolExecutor(max_workers=2,
                                 mp_context=multiprocessing.get_context("spawn")) as pool:
            for index, name in enumerate(names):
                log = Path(directory) / f"{index}.log"
                log.touch()
                try:
                    future = pool.submit(run_one, case, name, str(log))
                except Exception as exc:
                    # A pool can break before all selected cases are submitted.
                    future = Future()
                    future.set_exception(exc)
                jobs.append((name, log, future))
        # Wait for worker shutdown before reading logs, including partial logs
        # from interrupted cases. One failed future must not hide later reports.
        for name, log, future in jobs:
            sys.stderr.write(log.read_text(encoding="utf-8", errors="replace"))
            try:
                passed = future.result()
            except Exception as exc:
                passed = False
                print(f"ERROR {case.__name__}.{name}: {type(exc).__name__}: {exc}",
                      file=sys.stderr)
            failed += not passed
    print(f"Isolated tests: {len(names)} selected, {failed} failed", file=sys.stderr)
    return int(bool(failed))
