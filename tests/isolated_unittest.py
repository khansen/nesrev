"""Run opted-in, independent unittest cases in two separate worker processes.

Use only for cases whose mutable files, environment and working directory are
private to each test and restored by its fixtures. Class/module fixtures are not
supported: splitting them would change their lifetime. Explicit unittest
selections still run serially, for debugging. This does not parallelize the
shell harness.
"""

from concurrent.futures import ProcessPoolExecutor
from contextlib import redirect_stderr, redirect_stdout
import multiprocessing
import os
import sys
import tempfile
import unittest


def run_one(case, name):
    # Capture inherited subprocess descriptors as well as Python prints, so
    # concurrent assembler diagnostics stay with their owning test's report.
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as output:
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
        output.seek(0)
        return result.wasSuccessful(), output.read()


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
    with ProcessPoolExecutor(max_workers=2,
                             mp_context=multiprocessing.get_context("spawn")) as pool:
        futures = [pool.submit(run_one, case, name) for name in names]
        for future in futures:
            passed, output = future.result()
            sys.stderr.write(output)
            failed += not passed
    print(f"Isolated tests: {len(names)} run, {failed} failed", file=sys.stderr)
    return int(bool(failed))
