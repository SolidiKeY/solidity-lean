#!/usr/bin/env python3
"""Experimental Docker deadline control for an explicitly owned container.

Not a Lean timing gate: callers must create, pin and inspect the container and
prove VM, source, toolchain, cache, resource and process ownership separately.
"""
import os
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


def state(container_id, nonce, timeout=1):
    fmt = "{{index .Config.Labels \"" + LABEL + "\"}}|{{.State.Running}}|{{.State.ExitCode}}"
    parts = docker("inspect", "--format", fmt, container_id, timeout=timeout).split("|")
    if len(parts) != 3 or parts[0] != nonce or parts[1] not in ("true", "false") or not parts[2].isdigit():
        raise ValueError("container identity or state mismatch")
    return parts[1] == "true", int(parts[2])


def stop_owned(container_id, nonce):
    running, _ = state(container_id, nonce)
    if running:
        docker("kill", container_id)
    running, code = state(container_id, nonce)
    if running:
        raise RuntimeError("container remained running")
    return code


def watch(container_id, nonce, seconds):
    """Synthetic deadline; timeout is adjustable for tests and never a receipt."""
    if (not isinstance(container_id, str) or not IDENT.fullmatch(container_id) or
            not isinstance(nonce, str) or not NONCE.fullmatch(nonce) or
            type(seconds) not in (int, float) or not 0 < seconds <= 300):
        raise ValueError("invalid owned-container watch arguments")
    start = time.monotonic_ns()
    boot = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
    try:
        while True:
            elapsed = (time.monotonic_ns() - start) / 1e9
            boot_elapsed = (time.clock_gettime_ns(time.CLOCK_BOOTTIME) - boot) / 1e9
            if elapsed < 0 or boot_elapsed < 0 or abs(elapsed - boot_elapsed) > max(.05, boot_elapsed * .01):
                return {"status": "invalid-clock", "exit_code": stop_owned(container_id, nonce)}
            if elapsed >= seconds or boot_elapsed >= seconds:
                return {"status": "timeout", "exit_code": stop_owned(container_id, nonce)}
            running, code = state(container_id, nonce, timeout=max(.01, min(1, seconds - elapsed)))
            if not running:
                return {"status": "exited", "exit_code": code}
            time.sleep(min(.05, max(0, seconds - elapsed)))
    except (OSError, subprocess.SubprocessError, ValueError, RuntimeError):
        # A failed inspection may mean ownership cannot be verified. Attempt
        # cleanup only after a fresh successful ownership check; never claim pass.
        try:
            stop_owned(container_id, nonce)
        except (OSError, subprocess.SubprocessError, ValueError, RuntimeError):
            pass
        return {"status": "watch-error", "exit_code": None}
