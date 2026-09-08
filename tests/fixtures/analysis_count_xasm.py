#!/usr/bin/env python3
"""Counting test double, delegates assembly but reports its own test identity.

Never use this as production freshness evidence. Identity substitution exists
only so wrapper integration tests can count every assembler launch.
"""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

with open(os.environ["BUNDLE_TEST_CALLS"], "a") as stream:
    stream.write(json.dumps(sys.argv[1:]) + "\n")
run = subprocess.run([os.environ["BUNDLE_TEST_REAL_XASM"], *sys.argv[1:]])
if run.returncode == 0:
    for argument in sys.argv[1:]:
        if argument.startswith("--dependency-manifest="):
            path = Path(argument.split("=", 1)[1])
            data = json.loads(path.read_bytes())
            data["invocation"]["argv"][0] = sys.argv[0]
            for entry in data["inputs"]:
                if "producer" in entry["roles"]:
                    raw = Path(sys.argv[0]).read_bytes()
                    entry.update(path=sys.argv[0], size=len(raw), sha256=hashlib.sha256(raw).hexdigest())
            path.write_text(json.dumps(data))
raise SystemExit(run.returncode)
