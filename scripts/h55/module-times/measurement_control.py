#!/usr/bin/env python3
"""Experimental subprocess controls; this is not an authenticated Lean runner.

There is deliberately no CLI or gate-VM assertion. Callers must separately
establish resource bounds, trusted tools, complete inventory and provenance.
"""
import math
import os
import signal
import subprocess
import time


def check_clocks(start, end, max_seconds):
    """Compare monotonic and boot clocks; rejects disagreement and invalid data."""
    if (type(max_seconds) not in (int, float) or not math.isfinite(max_seconds)
            or max_seconds <= 0 or len(start) != 2 or len(end) != 2):
        return None
    if any(type(x) is not int or x < 0 for x in (*start, *end)):
        return None
    monotonic = (end[0] - start[0]) / 1e9
    boot = (end[1] - start[1]) / 1e9
    if monotonic <= 0 or boot <= 0 or abs(monotonic - boot) > max(0.05, boot * 0.01):
        return None
    if monotonic > max_seconds or boot > max_seconds:
        return None
    return max(monotonic, boot)


def clocks():
    return time.monotonic_ns(), time.clock_gettime_ns(time.CLOCK_BOOTTIME)


def run_control(argv, timeout_seconds):
    """Run one test process and return a conservative outcome and timing.

    This is a control prototype, not a production measurement. stdout/stderr
    are discarded; no Lean job, inventory or cache identity is authenticated.
    """
    if (not isinstance(argv, list) or not argv or
            any(not isinstance(arg, str) or not arg for arg in argv) or
            type(timeout_seconds) not in (int, float) or
            not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
        raise ValueError("invalid command or timeout")
    start = clocks()
    try:
        process = subprocess.Popen(argv, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                   start_new_session=True)
    except OSError:
        return {"status": "spawn-error", "seconds": None}
    try:
        code = process.wait(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        return {"status": "timeout", "seconds": None}
    elapsed = check_clocks(start, clocks(), timeout_seconds)
    if code != 0:
        return {"status": "failed", "seconds": elapsed}
    if elapsed is None:
        return {"status": "invalid-clock-or-over-budget", "seconds": None}
    return {"status": "ok", "seconds": elapsed}
