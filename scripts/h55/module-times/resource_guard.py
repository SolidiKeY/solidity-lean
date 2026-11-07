#!/usr/bin/env python3
"""Fail-closed Linux resource preflight for a future H55 executor.

No cgroup is created or changed. This is not a complete measurement runner;
it requires a dedicated cgroup and the caller must monitor throughout a job.
"""
import pathlib

GIB = 1024 ** 3
MAX_MEMORY = 12 * GIB
RESERVE = 4 * GIB


def validate(snapshot):
    required = ("memory_max", "memory_current", "swap_max", "swap_current", "available")
    if not isinstance(snapshot, dict) or any(type(snapshot.get(k)) is not int for k in required):
        return ["missing or invalid resource values"]
    cap, used = snapshot["memory_max"], snapshot["memory_current"]
    errors = []
    if cap <= 0 or cap > MAX_MEMORY or used < 0 or used > cap:
        errors.append("memory cap or usage invalid")
    if snapshot["swap_max"] != 0 or snapshot["swap_current"] != 0:
        errors.append("swap must be disabled")
    if snapshot["available"] < RESERVE or cap - used < RESERVE:
        errors.append("less than 4 GiB reserve")
    return errors


def sample():
    # Refuse nested/unrecognized cgroups; using the mount root for a nested
    # process would inspect the wrong resource boundary.
    group = pathlib.Path("/proc/self/cgroup").read_text().strip()
    if group != "0::/":
        raise ValueError("unsupported cgroup layout")
    base = pathlib.Path("/sys/fs/cgroup")
    def number(name):
        text = (base / name).read_text().strip()
        if not text.isdecimal():
            raise ValueError(f"unbounded or invalid {name}")
        return int(text)
    values = {}
    for line in pathlib.Path("/proc/meminfo").read_text().splitlines():
        key, _, value = line.partition(":")
        if key == "MemAvailable":
            fields = value.split()
            if len(fields) != 2 or fields[1] != "kB" or not fields[0].isdecimal():
                raise ValueError("invalid MemAvailable")
            values["available"] = int(fields[0]) * 1024
    values.update(memory_max=number("memory.max"), memory_current=number("memory.current"),
                  swap_max=number("memory.swap.max"), swap_current=number("memory.swap.current"))
    return values


def preflight():
    try:
        return validate(sample())
    except (OSError, ValueError):
        return ["resource state unavailable or unsupported"]


def _clock_pair():
    import time
    return time.monotonic_ns(), time.clock_gettime_ns(time.CLOCK_BOOTTIME)


def controlled_process(argv, output, timeout_seconds=300, poll_seconds=0.1):
    """Experimental monitored command. Caller must hold the repository lock.

    This function is not an acceptance gate: it does not authenticate argv,
    toolchain, tree, cache, environment, serial Lean configuration or VM.
    Its adjustable timeout exists for tests; never use it as a production
    timing receipt without a fixed-budget orchestration and independent review.
    """
    import math
    import os
    import signal
    import subprocess
    import time
    if (not isinstance(argv, list) or not argv or
            any(not isinstance(x, str) or not x for x in argv) or
            type(timeout_seconds) not in (int, float) or not math.isfinite(timeout_seconds) or
            timeout_seconds <= 0 or timeout_seconds > 300 or
            type(poll_seconds) not in (int, float) or not math.isfinite(poll_seconds) or
            not 0 < poll_seconds <= 0.1):
        raise ValueError("invalid command, timeout or poll interval")
    errors = preflight()
    if errors:
        return {"status": "resource-stop", "errors": errors}
    start_mono, start_boot = _clock_pair()
    try:
        process = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
    except OSError:
        return {"status": "spawn-error"}
    status = None
    code = None
    try:
        while True:
            errors = preflight()
            if errors:
                status = "resource-stop"
                break
            now_mono, now_boot = _clock_pair()
            elapsed = (now_mono - start_mono) / 1e9
            boot_elapsed = (now_boot - start_boot) / 1e9
            if (elapsed < 0 or boot_elapsed < 0 or
                    abs(elapsed - boot_elapsed) > max(0.05, boot_elapsed * 0.01)):
                status = "invalid-clock"
                break
            if elapsed > timeout_seconds or boot_elapsed > timeout_seconds:
                status = "timeout-or-invalid-clock"
                break
            # Keep the exited leader unreaped until the process group is
            # cleaned up, preventing its PID/group ID from being reused.
            info = os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
            if info is not None:
                code = info.si_status if info.si_code == os.CLD_EXITED else -info.si_status
                status = "ok" if code == 0 else "failed"
                break
            time.sleep(min(poll_seconds, max(0, timeout_seconds - elapsed)))
    finally:
        # Kill the complete process group even after a nominal leader exit,
        # so descendants cannot keep running beyond the guard.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
    return {"status": status, "exit_code": code, "errors": errors}


def locked_controlled_process(argv, output):
    """Acquire the repository writer lock and use the fixed 300s budget."""
    import fcntl
    lock_path = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    try:
        with lock_path.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = controlled_process(argv, output, timeout_seconds=300)
            # Process groups are escapable: a successful experimental run
            # is never a production timing pass without cgroup containment.
            if result.get("status") == "ok":
                result = {**result, "status": "untrusted-prototype-success"}
            return result
    except (OSError, ValueError):
        return {"status": "lock-or-control-error"}
