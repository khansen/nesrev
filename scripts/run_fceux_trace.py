#!/usr/bin/env python3
"""Run one FCEUX capture with bounded lifetime and explicit completion checks."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time


class CaptureError(Exception):
    pass


def positive_seconds(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return number


def positive_integer(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def input_file(value):
    path = Path(value).expanduser().resolve(strict=True)
    if not path.is_file():
        raise CaptureError(f"not a file: {path}")
    return path


def fingerprint(path):
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def signal_group(process, signum):
    try:
        os.killpg(process.pid, signum)
        return True
    except ProcessLookupError:
        return False


def stop_group(process, grace):
    # start_new_session makes this child's PID its private process-group ID.
    # Clean the group even if the emulator exited but left a helper behind.
    if signal_group(process, signal.SIGTERM):
        deadline = time.monotonic() + grace
        while time.monotonic() < deadline:
            process.poll()
            if not signal_group(process, 0):
                break
            time.sleep(min(0.05, max(0, deadline - time.monotonic())))
        if signal_group(process, 0):
            signal_group(process, signal.SIGKILL)
    process.wait(timeout=grace + 1)


def validate_capture(path, completion_line, required_milestones):
    if path.is_symlink() or not path.is_file():
        raise CaptureError(f"missing fresh trace file: {path}")
    last_line = None
    started = False
    done = False
    milestones = set()
    with path.open(encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            line = line.rstrip("\r\n")
            if not line.strip():
                continue
            last_line = line
            if completion_line is not None:
                continue
            if done:
                raise CaptureError("trace has records after its done event")
            try:
                record = json.loads(line)
            except ValueError as error:
                raise CaptureError(f"invalid JSON trace at line {number}: {error}") from error
            if not isinstance(record, dict):
                raise CaptureError(f"trace record at line {number} is not an object")
            event = record.get("event")
            if not started:
                if event != "start":
                    raise CaptureError("trace must begin with a start event")
                started = True
            elif event == "start":
                raise CaptureError("trace contains a second start event")
            if event == "milestone" and isinstance(record.get("name"), str):
                milestones.add(record["name"])
            if event in ("error", "fail"):
                raise CaptureError(f"trace reports {event} at line {number}")
            if event == "done":
                if record.get("reason") not in ("max_frames", "scenario_complete"):
                    raise CaptureError(f"trace ended early: {record.get('reason')!r}")
                done = True
    if completion_line is not None:
        if last_line != completion_line:
            raise CaptureError(f"trace must end with the exact line {completion_line!r}")
    else:
        if not done:
            raise CaptureError("trace is missing its done event")
        missing = set(required_milestones) - milestones
        if missing:
            raise CaptureError("missing required milestones: " + ", ".join(sorted(missing)))


def completion_written(path, completion_line):
    if path.is_symlink() or not path.is_file():
        return False
    # Poll only the tail; validate the entire log once its terminal record lands.
    limit = max(8192, len((completion_line or "").encode("utf-8")) + 2)
    with path.open("rb") as stream:
        stream.seek(0, os.SEEK_END)
        stream.seek(max(0, stream.tell() - limit))
        tail = stream.read()
    if not tail.endswith(b"\n"):
        return False
    lines = [line for line in tail.splitlines() if line.strip()]
    if not lines:
        return False
    if completion_line is not None:
        return lines[-1] == completion_line.encode("utf-8")
    try:
        record = json.loads(lines[-1])
        return isinstance(record, dict) and record.get("event") == "done"
    except (ValueError, UnicodeError):
        return False


def capture(args):
    if os.name != "posix":
        raise CaptureError("supervised FCEUX capture requires macOS or Linux process groups")
    rom = input_file(args.rom)
    lua = input_file(args.lua)
    movie = input_file(args.movie) if args.movie else None
    executable = shutil.which(args.fceux)
    if executable is None:
        raise CaptureError(f"FCEUX executable not found: {args.fceux}")
    executable = str(Path(executable).resolve())
    output = Path(args.output_dir).expanduser().resolve()
    output.mkdir(parents=True, exist_ok=True)
    run_dir = Path(tempfile.mkdtemp(prefix="capture-", dir=output))
    trace = run_dir / "trace.log"
    command = [executable, "--no-config", "1", "--gamegenie", "0", "--sound", args.sound]
    if args.input2:
        command += ["--input2", args.input2]
    if movie:
        command += ["--playmov", str(movie)]
    command += ["--loadlua", str(lua), str(rom)]
    environment = dict(os.environ, TRACE_OUT=str(trace), TRACE_DIR=str(run_dir),
                       TRACE_MAX_FRAMES=str(args.max_frames))
    result = {
        "status": "failed", "command": command, "rom": fingerprint(rom),
        "lua": fingerprint(lua), "movie": fingerprint(movie) if movie else None,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "trace": str(trace), "timeout_seconds": args.timeout,
        "max_frames": args.max_frames, "completion_line": args.completion_line,
        "required_milestones": args.require_milestone or [], "emulator_exit": None,
        "stopped_after_completion": False,
    }
    print(f"Capture directory: {run_dir}", flush=True)
    interrupted = []

    def interrupt(signum, _frame):
        # Do not raise between Popen spawning the child and returning its handle.
        interrupted.append(signum)

    previous = {sig: signal.signal(sig, interrupt) for sig in (signal.SIGINT, signal.SIGTERM)}
    process = None
    cleaned = False
    started = time.monotonic()
    exit_code = 1
    try:
        with (run_dir / "emulator.log").open("wb") as log:
            process = subprocess.Popen(command, cwd=run_dir, env=environment,
                                       stdin=subprocess.DEVNULL, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            deadline = started + args.timeout
            while process.poll() is None:
                if interrupted:
                    exit_code = 128 + interrupted[0]
                    raise CaptureError(f"capture interrupted by signal {interrupted[0]}")
                if time.monotonic() >= deadline:
                    exit_code = 124
                    raise CaptureError(f"capture timed out after {args.timeout:g} seconds")
                if completion_written(trace, args.completion_line):
                    validate_capture(trace, args.completion_line, args.require_milestone)
                    try:
                        process.wait(timeout=args.shutdown_grace)
                    except subprocess.TimeoutExpired:
                        result["stopped_after_completion"] = True
                        stop_group(process, args.shutdown_grace)
                        cleaned = True
                    break
                time.sleep(0.05)
            if interrupted:
                exit_code = 128 + interrupted[0]
                raise CaptureError(f"capture interrupted by signal {interrupted[0]}")
            if process.returncode != 0 and not result["stopped_after_completion"]:
                raise CaptureError(f"FCEUX exited with status {process.returncode}; see emulator.log")
            # Stop helpers before reading a log that they might still be writing.
            if not cleaned:
                stop_group(process, args.shutdown_grace)
                cleaned = True
            validate_capture(trace, args.completion_line, args.require_milestone)
            result["status"] = "complete"
            exit_code = 0
    except (CaptureError, OSError, UnicodeError, subprocess.SubprocessError) as error:
        result["error"] = str(error)
    finally:
        try:
            if process is not None:
                if not cleaned:
                    stop_group(process, args.shutdown_grace)
                result["emulator_exit"] = process.returncode
        except (OSError, subprocess.SubprocessError) as error:
            result["status"] = "failed"
            result["error"] = f"emulator cleanup failed: {error}"
            exit_code = 1
        finally:
            if interrupted:
                result["status"] = "failed"
                result["error"] = f"capture interrupted by signal {interrupted[0]}"
                exit_code = 128 + interrupted[0]
            for sig, handler in previous.items():
                signal.signal(sig, handler)
        result["duration_seconds"] = round(time.monotonic() - started, 3)
        result["exit_code"] = exit_code
        (run_dir / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    if exit_code:
        print(f"ERROR: {result['error']}\nCapture diagnostics: {run_dir}", file=sys.stderr)
    else:
        print(f"Capture complete (configured checks passed): {trace}")
    return exit_code


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rom", required=True)
    parser.add_argument("--lua", required=True)
    parser.add_argument("--output-dir", required=True, help="parent for a fresh capture directory")
    parser.add_argument("--fceux", default=os.environ.get("FCEUX_BIN", "fceux"))
    parser.add_argument("--movie")
    parser.add_argument("--input2")
    parser.add_argument("--sound", choices=("0", "1"), default="0")
    parser.add_argument("--max-frames", type=positive_integer, default=36000)
    parser.add_argument("--timeout", type=positive_seconds, default=180,
                        help="wall-clock capture limit in seconds (default: 180)")
    parser.add_argument("--shutdown-grace", type=positive_seconds, default=2,
                        help="seconds between TERM and KILL (default: 2)")
    checks = parser.add_mutually_exclusive_group(required=True)
    checks.add_argument("--completion-line", help="exact final line, written after Lua scenario assertions pass")
    checks.add_argument("--require-milestone", action="append",
                        help="required JSONL milestone; repeat for every scenario gate")
    args = parser.parse_args(argv)
    if args.completion_line is not None and (not args.completion_line.strip() or
                                             "\n" in args.completion_line or "\r" in args.completion_line):
        parser.error("--completion-line must be one nonempty line")
    if args.require_milestone and any(not name.strip() for name in args.require_milestone):
        parser.error("--require-milestone must be nonempty")
    try:
        return capture(args)
    except (CaptureError, OSError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
