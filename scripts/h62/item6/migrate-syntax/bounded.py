#!/usr/bin/env python3
"""Run one owned command tree with serial writer ownership and 4 GiB reserve.

Guarded regression: SIGINT/SIGTERM or an exited command leader must not release
writer ownership while descendants in its process group can still run.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import time
from measure import available, GIB

LOCK_PATH = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")


def group_running(group):
    """Zombies cannot execute; include live descendants after the leader exits."""
    for path in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = path.read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == group and fields[0] not in ("Z", "X"):
                return True
        except (OSError, ValueError, IndexError):
            continue
    return False


def stop_group(group):
    def send(sig):
        try:
            os.killpg(group, sig)
        except ProcessLookupError:
            pass

    term_sent = group_running(group)
    kill_sent = False
    if term_sent:
        send(signal.SIGTERM)
    deadline = time.monotonic() + 2
    while group_running(group) and time.monotonic() < deadline:
        time.sleep(.05)
    # A leader may exit on TERM while a grandchild ignores it. Kill the whole
    # group and retain the lock until no member can execute, even in that case.
    while group_running(group):
        kill_sent = True
        send(signal.SIGKILL)
        time.sleep(.05)
    return {"term_sent": term_sent, "kill_sent": kill_sent}


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or args.output.exists():
        parser.error("require a command and a fresh output directory")
    if len(Path("/proc/swaps").read_text().splitlines()) != 1:
        raise SystemExit("Swap present")
    with LOCK_PATH.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if available() < 4 * GIB:
            raise SystemExit("4 GiB reserve unavailable")
        args.output.mkdir(parents=True)
        start = time.monotonic()
        requested_signal = None
        child = None
        usage = None
        stop = None
        error = None
        cleanup = {"term_sent": False, "kill_sent": False}

        def interrupted(signum, _frame):
            # Record rather than raise: Popen assignment and cleanup must not
            # be interrupted by a second signal, leaving an unowned group.
            nonlocal requested_signal
            if requested_signal is None:
                requested_signal = signum

        previous = {sig: signal.signal(sig, interrupted)
                    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
        try:
            with (args.output / "command.log").open("w") as log:
                if requested_signal is None:
                    child = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                             start_new_session=True,
                                             env=dict(os.environ, LEAN_NUM_THREADS="1"))
                    while True:
                        pid, status, sample = os.wait4(child.pid, os.WNOHANG)
                        if pid:
                            child.returncode = os.waitstatus_to_exitcode(status)
                            usage = sample
                            break
                        if requested_signal is not None:
                            break
                        if available() < 4 * GIB:
                            stop = "reserve-stop"
                            break
                        time.sleep(.2)
        except BaseException as exc:
            stop = "supervisor-error"
            error = repr(exc)
        finally:
            # This finally runs inside the writer lock, including on launch or
            # monitoring errors and after normal leader exit with live children.
            if child is not None:
                if child.returncode is not None and group_running(child.pid) and stop is None:
                    stop = "surviving-descendants"
                cleanup = stop_group(child.pid)
                if child.returncode is None:
                    _, status, usage = os.wait4(child.pid, 0)
                    child.returncode = os.waitstatus_to_exitcode(status)
            if requested_signal is not None:
                stop = "signal-stop"
            result = dict(command=command, exit=child.returncode if child else None,
                          status=stop or ("pass" if child and child.returncode == 0 else "fail"),
                          signal=requested_signal, error=error, cleanup=cleanup,
                          wall_seconds=time.monotonic() - start,
                          max_rss_kib=usage.ru_maxrss if usage else None,
                          threads=1, reserve_gib=4, swap="none",
                          process_group_quiescent=child is None or not group_running(child.pid))
            (args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
            for sig, handler in previous.items():
                signal.signal(sig, handler)
        print(json.dumps(result))
        return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
