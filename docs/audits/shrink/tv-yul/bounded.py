#!/usr/bin/env python3
"""Serial VM guard: 12 GiB address-space cap, no swap, two 4 GiB reserves.

The child owns a fresh process group. pidfd/select observes exit without reaping; waitid(WNOWAIT) keeps its leader
unreaped until monitoring has stopped, so termination cannot target a reused process group.
Sampling failures and failed resource checks always refuse a passing result.
Commands must wait for their workers; detached/background daemons are unsupported.
"""
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import select
import time

RESERVE = 4 * 1024**3
PROCESS_LIMIT = 12 * 1024**3
VM_LIMIT = 16 * 1024**3


def resources():
    cg = Path("/sys/fs/cgroup")
    limit = int((cg / "memory.max").read_text())
    if limit > VM_LIMIT:
        raise RuntimeError("hard cgroup cap exceeds 16 GiB")
    current = int((cg / "memory.current").read_text())
    stats = dict(row.split() for row in (cg / "memory.stat").read_text().splitlines())
    inactive = min(current, int(stats["inactive_file"]))
    mem = {row.split(":")[0]: int(row.split()[1]) * 1024
           for row in Path("/proc/meminfo").read_text().splitlines()
           if len(row.split()) >= 3}
    if mem["SwapTotal"] != 0:
        raise RuntimeError("swap must remain unavailable")
    return dict(limit=limit, current=current, working=current-inactive,
                effective_free=limit-current+inactive, os_available=mem["MemAvailable"])


def under_reserve(sample):
    return sample["os_available"] < RESERVE or sample["effective_free"] < RESERVE


def effective_process_limit():
    existing = resource.getrlimit(resource.RLIMIT_AS)
    return min([PROCESS_LIMIT] + [value for value in existing if value != resource.RLIM_INFINITY])


def run(command, sampler=resources, interval=0.25):
    start = time.monotonic()
    samples = []
    stopped = False
    monitor_error = None
    child = None
    pidfd = None
    applied_limit = None

    def refuse(error=None):
        nonlocal stopped, monitor_error
        stopped = True
        if error is not None and monitor_error is None:
            monitor_error = type(error).__name__ + ": " + str(error)
        if child is not None:
            # The leader is alive or unreaped; no wait/poll reaps it before signalling ends.
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    def sample_once():
        sample = sampler()
        samples.append(sample)
        if under_reserve(sample):
            refuse()

    try:
        applied_limit = effective_process_limit()
        if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
            raise RuntimeError("custom SIGCHLD handling is unsupported")
        sample_once()
        if not stopped:
            child = subprocess.Popen(command, start_new_session=True,
                                     preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (applied_limit, applied_limit)),
                                     env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_LSP_MAX_OPEN_FILES="3"))
            pidfd = os.pidfd_open(child.pid)
            while not stopped:
                exited = bool(select.select([pidfd], [], [], interval)[0])
                sample_once()
                if exited:
                    os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOWAIT)
                    break
    except BaseException as error:
        refuse(error)
    finally:
        # Single-threaded monitoring has ended; only now may the PID be reaped.
        child_exit = child.wait() if child is not None else None
        if pidfd is not None:
            os.close(pidfd)
    elapsed = time.monotonic() - start
    result = dict(command=command, exit=125 if stopped else child_exit,
                  child_exit=child_exit, seconds=elapsed, resource_stop=stopped,
                  monitor_error=monitor_error, configured_process_address_space_limit=PROCESS_LIMIT,
                  applied_process_address_space_limit=applied_limit,
                  policy="12GiB RLIMIT_AS; hard VM cap<=16GiB; no swap; 4GiB OS and effective-free reserves; own process group only; monitoring errors fail closed")
    if samples:
        result.update(cgroup_limit=samples[0]["limit"],
                      peak_cgroup_current=max(s["current"] for s in samples),
                      peak_cgroup_working=max(s["working"] for s in samples),
                      minimum_effective_free=min(s["effective_free"] for s in samples),
                      minimum_os_available=min(s["os_available"] for s in samples))
    return result


def main():
    if len(sys.argv) < 3:
        raise SystemExit("usage: bounded.py RECORD_JSON COMMAND...")
    record = Path(sys.argv[1])
    command = sys.argv[2:]
    if os.environ.get("TVYUL_USE_VM_CAP") not in (None, "", "0"):
        result = dict(command=command, exit=125, resource_stop=True,
                      monitor_error="removed TVYUL_USE_VM_CAP bypass is refused")
    else:
        def cancelled(signum, _frame):
            raise InterruptedError("guard received signal " + str(signum))
        signal.signal(signal.SIGTERM, cancelled)
        signal.signal(signal.SIGINT, cancelled)
        result = run(command)
    record.parent.mkdir(parents=True, exist_ok=True)
    record.write_text(json.dumps(result, indent=2) + "\n")
    print("RESOURCE_CHECK", json.dumps(result), flush=True)
    code = result["exit"]
    raise SystemExit(code if code >= 0 else 128-code)


if __name__ == "__main__":
    main()
