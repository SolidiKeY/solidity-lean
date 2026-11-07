#!/usr/bin/env python3
"""Experimental Docker deadline control for an explicitly owned container.

Not a Lean timing gate: callers must create, pin and inspect the container and
prove VM, source, toolchain, cache, resource and process ownership separately.
"""
import os
import pathlib
import re
import subprocess
import time

LABEL = "org.solidity-lean.h55-fixture"
IDENT = re.compile(r"[0-9a-f]{64}\Z")
NONCE = re.compile(r"[0-9a-f]{32}\Z")


def docker(*args, timeout=1):
    env = dict(os.environ)
    for key in ("DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"):
        env.pop(key, None)
    return subprocess.run(["docker", "--host=unix:///var/run/docker.sock", *args],
                          env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=True).stdout.strip()


def kernel_limits(container_id, pid, memory, pids):
    """Inspect the observed local cgroup-v2 layout, rejecting all others."""
    if not IDENT.fullmatch(container_id) or not pid.isdigit() or int(pid) <= 0:
        raise ValueError("invalid kernel process identity")
    group = pathlib.Path("/proc", pid, "cgroup").read_text().strip()
    if group != "0::/../docker/" + container_id:
        raise ValueError("unexpected process cgroup")
    mounts = pathlib.Path("/proc/self/mountinfo").read_text().splitlines()
    if not any(len(line.split()) >= 6 and line.split()[3:5] == ["/..", "/sys/fs/cgroup"]
               and " - cgroup2 " in line for line in mounts):
        raise ValueError("unsupported cgroup mount")
    base = pathlib.Path("/sys/fs/cgroup/docker") / container_id
    if base.resolve(strict=True) != base:
        raise ValueError("unexpected cgroup path")
    values = [(base / name).read_text().strip() for name in
              ("memory.max", "memory.swap.max", "memory.swap.current", "pids.max")]
    if values != [str(memory), "0", "0", str(pids)]:
        raise ValueError("effective cgroup limits mismatch")


def state(container_id, nonce, timeout=1, check_limits=True):
    fmt = ("{{index .Config.Labels \"" + LABEL + "\"}}|{{.State.Running}}|{{.State.ExitCode}}"
           "|{{.HostConfig.Memory}}|{{.HostConfig.MemorySwap}}|{{.HostConfig.NetworkMode}}|{{.HostConfig.PidsLimit}}|{{.State.Pid}}")
    parts = docker("inspect", "--format", fmt, container_id, timeout=timeout).split("|")
    if len(parts) != 8 or parts[0] != nonce or parts[1] not in ("true", "false") or not parts[2].isdigit():
        raise ValueError("container identity or state mismatch")
    if check_limits:
        if (not parts[3].isdigit() or not parts[4].isdigit() or not parts[6].isdigit()
                or not 0 < int(parts[3]) <= 12 * 1024 ** 3 or int(parts[4]) != int(parts[3])
                or parts[5] != "none" or int(parts[6]) <= 0):
            raise ValueError("container resource policy mismatch")
        if parts[1] == "true":
            kernel_limits(container_id, parts[7], int(parts[3]), int(parts[6]))
    return parts[1] == "true", int(parts[2])


def stop_owned(container_id, nonce):
    running, _ = state(container_id, nonce, check_limits=False)
    if running:
        docker("kill", container_id)
    running, code = state(container_id, nonce, check_limits=False)
    if running:
        raise RuntimeError("container remained running")
    return code



def host_headroom():
    """Conservative host/parent check; container limits are separate."""
    reserve = 4 * 1024 ** 3
    if pathlib.Path("/proc/self/cgroup").read_text().strip() != "0::/":
        raise ValueError("unsupported cgroup layout")
    fields = {}
    for line in pathlib.Path("/proc/meminfo").read_text().splitlines():
        key, sep, value = line.partition(":")
        if sep and key in ("MemAvailable", "SwapTotal"):
            parts = value.split()
            if len(parts) != 2 or not parts[0].isdigit() or parts[1] != "kB":
                raise ValueError("invalid memory information")
            fields[key] = int(parts[0]) * 1024
    if set(fields) != {"MemAvailable", "SwapTotal"}:
        raise ValueError("missing memory information")
    base = pathlib.Path("/sys/fs/cgroup")
    def number(name):
        value = (base / name).read_text().strip()
        if not value.isdecimal():
            raise ValueError("unbounded or invalid cgroup value")
        return int(value)
    cap, current = number("memory.max"), number("memory.current")
    swap = number("memory.swap.current")
    return (fields["SwapTotal"] == 0 and swap == 0 and 0 <= current <= cap
            and fields["MemAvailable"] >= reserve and cap - current >= reserve)

def watch(container_id, nonce, seconds, *, _anchor=None):
    """Synthetic deadline; timeout is adjustable for tests and never a receipt."""
    if (not isinstance(container_id, str) or not IDENT.fullmatch(container_id) or
            not isinstance(nonce, str) or not NONCE.fullmatch(nonce) or
            type(seconds) not in (int, float) or not 0 < seconds <= 300):
        raise ValueError("invalid owned-container watch arguments")
    if _anchor is None:
        start = time.monotonic_ns()
        boot = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
    elif (isinstance(_anchor, tuple) and len(_anchor) == 2
          and all(type(value) is int and value >= 0 for value in _anchor)):
        start, boot = _anchor
    else:
        raise ValueError("invalid clock anchor")
    observed_running = False
    try:
        while True:
            if not host_headroom():
                return {"status": "resource-stop", "exit_code": stop_owned(container_id, nonce)}
            elapsed = (time.monotonic_ns() - start) / 1e9
            boot_elapsed = (time.clock_gettime_ns(time.CLOCK_BOOTTIME) - boot) / 1e9
            if elapsed < 0 or boot_elapsed < 0 or abs(elapsed - boot_elapsed) > max(.05, boot_elapsed * .01):
                return {"status": "invalid-clock", "exit_code": stop_owned(container_id, nonce)}
            if elapsed >= seconds or boot_elapsed >= seconds:
                return {"status": "timeout", "exit_code": stop_owned(container_id, nonce)}
            try:
                running, code = state(container_id, nonce, timeout=max(.01, min(1, seconds - elapsed)))
            except subprocess.TimeoutExpired:
                # An inspection timeout is still a failure. Classify it as a
                # deadline only if both clocks show that deadline has passed.
                elapsed = (time.monotonic_ns() - start) / 1e9
                boot_elapsed = (time.clock_gettime_ns(time.CLOCK_BOOTTIME) - boot) / 1e9
                if (elapsed >= seconds and boot_elapsed >= seconds and
                        abs(elapsed - boot_elapsed) <= max(.05, boot_elapsed * .01)):
                    return {"status": "timeout", "exit_code": stop_owned(container_id, nonce)}
                raise
            # Inspection itself can cross the deadline or expose a clock
            # discontinuity. Never accept its result using the earlier time.
            elapsed = (time.monotonic_ns() - start) / 1e9
            boot_elapsed = (time.clock_gettime_ns(time.CLOCK_BOOTTIME) - boot) / 1e9
            if elapsed < 0 or boot_elapsed < 0 or abs(elapsed - boot_elapsed) > max(.05, boot_elapsed * .01):
                return {"status": "invalid-clock", "exit_code": stop_owned(container_id, nonce)}
            if elapsed >= seconds or boot_elapsed >= seconds:
                return {"status": "timeout", "exit_code": stop_owned(container_id, nonce)}
            if not running:
                status = "unobserved-exit" if not observed_running else "exited" if code == 0 else "failed"
                return {"status": status, "exit_code": code}
            observed_running = True
            time.sleep(min(.05, max(0, seconds - elapsed)))
    except (OSError, subprocess.SubprocessError, ValueError, RuntimeError):
        # A failed inspection may mean ownership cannot be verified. Attempt
        # cleanup only after a fresh successful ownership check; never claim pass.
        try:
            stop_owned(container_id, nonce)
        except (OSError, subprocess.SubprocessError, ValueError, RuntimeError):
            pass
        return {"status": "watch-error", "exit_code": None}


def start_and_watch(container_id, nonce, seconds=300):
    """Guard regression: execution before watch evades the deadline.

    Synthetic only: caller-supplied identity/limits and Docker daemon are not
    authenticated. Start or cleanup errors never establish a timing pass.
    """
    if (not isinstance(container_id, str) or not IDENT.fullmatch(container_id) or
            not isinstance(nonce, str) or not NONCE.fullmatch(nonce) or
            type(seconds) not in (int, float) or not 0 < seconds <= 300):
        raise ValueError("invalid owned-container start arguments")
    try:
        fmt = "{{index .Config.Labels \"" + LABEL + "\"}}|{{.State.Status}}"
        if docker("inspect", "--format", fmt, container_id) != nonce + "|created":
            return {"status": "untrusted-prestart-state", "exit_code": None}
        if not host_headroom():
            return {"status": "resource-stop-before-start", "exit_code": None}
        # The deadline begins immediately before the start request, not after
        # Docker has started the workload or returned from its API call.
        anchor = (time.monotonic_ns(), time.clock_gettime_ns(time.CLOCK_BOOTTIME))
        try:
            docker("start", container_id, timeout=seconds)
        except (OSError, subprocess.SubprocessError, ValueError):
            # A timed-out start request may still complete later. Attempt only
            # ownership-checked cleanup and never claim it was conclusive.
            try:
                stop_owned(container_id, nonce)
            except (OSError, subprocess.SubprocessError, ValueError, RuntimeError):
                pass
            return {"status": "untrusted-start-error", "exit_code": None}
        result = watch(container_id, nonce, seconds, _anchor=anchor)
        # This wrapper is not an authenticated measurement or acceptance gate.
        if result.get("status") == "exited":
            return {**result, "status": "untrusted-exited"}
        return result
    except (OSError, subprocess.SubprocessError, ValueError):
        return {"status": "untrusted-prestart-error", "exit_code": None}
