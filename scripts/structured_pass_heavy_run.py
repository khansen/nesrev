"""Serialize cooperating POSIX test runs and record their disk-space lifecycle.

Use one explicit --lock path across all copies. The supervisor retains the lock
if the CLI is killed, stops the command group, and records the interruption.
Commands must not daemonize or detach from their process group. This is resource
coordination, not an agent permission boundary.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import selectors
import shutil
import signal
import subprocess
import sys
import time
import uuid


MIB = 1024 ** 2
ACTIVE = {"starting", "running", "cleaning", "cleanup_incomplete"}
ENV = "NESREV_HEAVY_RUN_"


class RunError(Exception):
    pass


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def save(path, value):
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        with temporary.open("x") as stream:
            json.dump(value, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def space(paths):
    return [{"path": path, "device": os.stat(path).st_dev,
             "free_bytes": shutil.disk_usage(path).free} for path in paths]


def group_alive(pgid):
    if not pgid:
        return False
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False


def stop_group(process):
    """Finish or kill the owned foreground group before relinquishing the lock."""
    for signum, duration in ((signal.SIGTERM, 2.0), (signal.SIGKILL, 2.0)):
        try:
            os.killpg(process.pid, signum)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + duration
        while time.monotonic() < deadline:
            process.poll()  # Reap our child, including a terminated group leader.
            if not group_alive(process.pid):
                return
            time.sleep(0.025)
    raise RunError("HEAVY_CHILDREN_REMAIN")


def recover(records):
    for path in sorted(records.glob("*.json")):
        value = json.loads(path.read_text())
        if value["status"] not in ACTIVE:
            continue
        # With the lock acquired, an unfinished receipt has lost its supervisor.
        # Never signal an old numeric PID, which may now belong to somebody else.
        if group_alive(value.get("command_pgid")):
            raise RunError("HEAVY_ORPHAN_REQUIRES_RECOVERY")
        value.update(status="interrupted", error="RUNNER_INTERRUPTED",
                     recovered_at=now(), finished_at=None, free_after=None)
        save(path, value)


def supervise(record_path, lock_fd, owner_fd):
    value = json.loads(record_path.read_text())
    process = None
    result = 70
    interrupted = False
    try:
        if os.read(owner_fd, 1) != b"R":
            interrupted = True
        else:
            value.update(supervisor_pid=os.getpid(), status="running", started_at=now())
            save(record_path, value)
            env = os.environ.copy()
            env.update({ENV + "ID": value["run_id"], ENV + "LOCK": value["lock"],
                        ENV + "FD": str(lock_fd)})
            # Record the process group before it can execute any heavy work. If
            # the supervisor dies during registration, EOF cancels the gate.
            gate_read, gate_write = os.pipe()
            try:
                process = subprocess.Popen(
                    [sys.executable, "-B", str(Path(__file__).resolve()),
                     "--command-gate", str(gate_read), *value["command"]],
                    cwd=value["cwd"], env=env, start_new_session=True,
                    pass_fds=(lock_fd, gate_read))
                os.close(gate_read)
                gate_read = None
                value["command_pgid"] = process.pid
                save(record_path, value)
                os.write(gate_write, b"R")
            finally:
                if gate_read is not None:
                    os.close(gate_read)
                os.close(gate_write)
            with selectors.DefaultSelector() as selector:
                selector.register(owner_fd, selectors.EVENT_READ)
                while True:
                    if selector.select(0.05) and os.read(owner_fd, 1) == b"":
                        interrupted = True
                        break
                    if process.poll() is not None:
                        break
        value.update(status="cleaning", interrupted=interrupted)
        save(record_path, value)
        if process is not None:
            stop_group(process)
        command_exit = process.returncode if process is not None else None
        result = 125 if interrupted else (command_exit if command_exit >= 0 else 128-command_exit)
        value.update(status="interrupted" if interrupted else "finished",
                     error="OWNER_INTERRUPTED" if interrupted else None,
                     command_exit=command_exit, exit_code=result, finished_at=now(),
                     free_after=space(value["volumes"]))
        save(record_path, value)
    except Exception as error:
        cleanup_error = None
        if process is not None:
            try:
                stop_group(process)
            except Exception:
                cleanup_error = "HEAVY_CHILDREN_REMAIN"
        value.update(status="cleanup_incomplete" if cleanup_error else "failed",
                     error=cleanup_error or (str(error) if isinstance(error, RunError)
                                             else "HEAVY_RUN_INTERNAL_ERROR"),
                     exit_code=70, finished_at=now())
        try:
            value["free_after"] = space(value["volumes"])
            save(record_path, value)
        except Exception:
            pass  # The pre-launch receipt enables recovery; never invent a result.
        print(value["error"], file=sys.stderr, flush=True)
        result = 70
    finally:
        os.close(owner_fd)
        os.close(lock_fd)
    return result


def nested(args, lock, volumes):
    try:
        fd = int(os.environ[ENV + "FD"])
        if os.environ[ENV + "LOCK"] != str(lock):
            raise RunError("HEAVY_RUN_LOCK_MISMATCH")
        actual, expected = os.fstat(fd), lock.stat()
        if (actual.st_dev, actual.st_ino) != (expected.st_dev, expected.st_ino):
            raise RunError("HEAVY_RUN_CONTEXT_LOST")
        run_id = os.environ[ENV + "ID"]
        if not run_id.isalnum():
            raise RunError("HEAVY_RUN_CONTEXT_LOST")
        value = json.loads((lock.with_name(lock.name + ".runs")/(run_id + ".json")).read_text())
        if value["status"] != "running" or value["run_id"] != run_id:
            raise RunError("HEAVY_RUN_CONTEXT_LOST")
        # An inherited environment alone must not masquerade as a held lock.
        with lock.open("a+b") as probe:
            try:
                fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                pass
            else:
                raise RunError("HEAVY_RUN_CONTEXT_LOST")
        if (not set(volumes).issubset(value["volumes"])
                or args.estimate_mib * MIB > value["estimate_bytes"]):
            raise RunError("HEAVY_RUN_NESTED_BUDGET")
        needed = args.estimate_mib * MIB + max(args.reserve_mib * MIB, value["reserve_bytes"])
        if any(item["free_bytes"] < needed for item in space(volumes)):
            raise RunError("INSUFFICIENT_DISK_SPACE")
        return subprocess.run(args.command, pass_fds=(fd,)).returncode
    except (KeyError, ValueError, OSError, json.JSONDecodeError) as error:
        raise RunError("HEAVY_RUN_CONTEXT_LOST") from error


def run(args):
    supplied = args.lock or os.environ.get(ENV + "LOCK")
    if not supplied or not Path(supplied).is_absolute():
        raise RunError("HEAVY_RUN_ABSOLUTE_LOCK_REQUIRED")
    lock = Path(supplied).resolve()
    volumes = sorted({str(Path(p).resolve(strict=True)) for p in (args.volume or [os.getcwd()])})
    if ENV + "ID" in os.environ:
        return nested(args, lock, volumes)
    lock.parent.mkdir(parents=True, exist_ok=True)
    with lock.open("a+b") as held:
        try:
            fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RunError("HEAVY_RUN_IN_PROGRESS") from error
        records = lock.with_name(lock.name + ".runs")
        records.mkdir(exist_ok=True)
        recover(records)
        run_id = uuid.uuid4().hex
        path = records/(run_id + ".json")
        value = {"schema": "heavy-run-v1", "run_id": run_id, "lock": str(lock),
                 "agent": args.agent, "session": args.session, "owner_pid": os.getpid(),
                 "command": args.command, "cwd": os.getcwd(), "volumes": volumes,
                 "estimate_bytes": args.estimate_mib * MIB,
                 "reserve_bytes": args.reserve_mib * MIB, "created_at": now(),
                 "status": "starting", "free_before": space(volumes), "free_after": None}
        if any(item["free_bytes"] < value["estimate_bytes"] + value["reserve_bytes"]
               for item in value["free_before"]):
            value.update(status="refused", error="INSUFFICIENT_DISK_SPACE", finished_at=now())
            save(path, value)
            raise RunError("INSUFFICIENT_DISK_SPACE")
        save(path, value)
        print("HEAVY_RUN " + run_id + " " + str(path), file=sys.stderr, flush=True)
        read_fd, write_fd = os.pipe()
        guardian = None
        interrupted = []

        def close_owner(signum=None, frame=None):
            nonlocal write_fd
            if signum is not None:
                interrupted.append(signum)
            if write_fd is not None:
                os.close(write_fd)
                write_fd = None

        previous = {sig: signal.signal(sig, close_owner) for sig in (signal.SIGINT, signal.SIGTERM)}
        try:
            guardian = subprocess.Popen([sys.executable, "-B", str(Path(__file__).resolve()),
                                         "--supervise", str(path), str(held.fileno()), str(read_fd)],
                                        pass_fds=(held.fileno(), read_fd), start_new_session=True)
            os.close(read_fd)
            read_fd = None
            if write_fd is not None:
                os.write(write_fd, b"R")
            result = guardian.wait()
            return 128 + interrupted[-1] if interrupted else (result if result >= 0 else 128-result)
        finally:
            close_owner()
            if read_fd is not None:
                os.close(read_fd)
            if guardian is not None and guardian.poll() is None:
                guardian.wait()
            for sig, handler in previous.items():
                signal.signal(sig, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", help="Shared absolute lock path; or NESREV_HEAVY_RUN_LOCK")
    parser.add_argument("--agent", required=True)
    parser.add_argument("--session", required=True)
    parser.add_argument("--estimate-mib", type=int, required=True)
    parser.add_argument("--reserve-mib", type=int, default=2048)
    parser.add_argument("--volume", action="append", help="Existing directory on each affected volume")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.command[:1] == ["--"]:
        args.command = args.command[1:]
    if not args.command or min(args.estimate_mib, args.reserve_mib) < 0:
        parser.error("a command and nonnegative disk estimates are required")
    try:
        return run(args)
    except RunError as error:
        print(str(error), file=sys.stderr)
        return 75
    except Exception:
        print("HEAVY_RUN_INTERNAL_ERROR", file=sys.stderr)
        return 70


if __name__ == "__main__":
    if sys.argv[1:2] == ["--supervise"]:
        raise SystemExit(supervise(Path(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])))
    if sys.argv[1:2] == ["--command-gate"]:
        gate = int(sys.argv[2])
        allowed = os.read(gate, 1) == b"R"
        os.close(gate)
        if not allowed:
            raise SystemExit(125)
        try:
            os.execvp(sys.argv[3], sys.argv[3:])
        except OSError:
            print("HEAVY_COMMAND_START_FAILED", file=sys.stderr)
            raise SystemExit(127)
    raise SystemExit(main())
