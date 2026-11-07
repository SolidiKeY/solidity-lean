#!/usr/bin/env python3
"""Join snapshots to an experimental observation, never an H56 gate pass."""
import fcntl
import importlib.util
import pathlib
import time

ROOT = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("h55_bound_snapshot", ROOT / "bound_snapshot.py")
bound = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bound)
LOCK = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")


def observe(root, head, tool, source, cache, action):
    """Run a supplied experimental action under the lock with before/after checks.

    This does not impose a timeout on action, authenticate its result, verify
    cache completeness, validate H56 identity or enforce resource limits. A
    successful result is explicitly untrusted and is not a timing receipt.
    """
    if not callable(action):
        raise ValueError("action must be callable")
    try:
        with LOCK.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            before = bound.capture(root, head, tool, source, cache)
            mono_start = time.monotonic_ns()
            boot_start = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
            try:
                result = action()
            except Exception:
                return {"status": "action-error"}
            mono_end = time.monotonic_ns()
            boot_end = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
            after = bound.capture(root, head, tool, source, cache)
    except (OSError, ValueError):
        return {"status": "snapshot-or-lock-error"}
    if not bound.compare(before, after):
        return {"status": "input-drift"}
    if not isinstance(result, dict) or result.get("status") != "exited" or type(result.get("exit_code")) is not int or result["exit_code"] != 0:
        return {"status": "failed-observation"}
    elapsed, boot_elapsed = mono_end - mono_start, boot_end - boot_start
    if (elapsed <= 0 or boot_elapsed <= 0 or elapsed > 300_000_000_000 or boot_elapsed > 300_000_000_000
            or abs(elapsed - boot_elapsed) > max(50_000_000, boot_elapsed // 100)):
        return {"status": "invalid-time"}
    return {"status": "untrusted-observation", "wall_ns": elapsed,
            "boot_ns": boot_elapsed, "snapshot": before}
