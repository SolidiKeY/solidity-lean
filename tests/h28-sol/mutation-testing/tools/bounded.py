#!/usr/bin/env python3
"""Serial Lean in a pinned local Docker image with a hard no-swap cgroup.

The caller owns the repository writer lock. No network, cache download, shell
command from the manifest, or unbounded Lean fallback is supported.
"""
import json
import hashlib
import os
from pathlib import Path
import re
import subprocess
import time
import uuid

IMAGE = "ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852"
RUNTIME = Path("/workspace/h28-runtime/lean-4.24.0-linux")
LIMIT = 6 * 1024**3
RESERVE = 4 * 1024**3
DOCKER = ["docker", "--host=unix:///var/run/docker.sock"]


def docker_env():
    env = dict(os.environ)
    for key in ("DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"):
        env.pop(key, None)
    return env


class CleanupError(RuntimeError):
    def __init__(self, record):
        self.record = record
        super().__init__("owned container cleanup unconfirmed; stop serial checking: " + record["container_name"])


def remove_owned(name, env):
    try:
        subprocess.run(DOCKER + ["rm", "-f", name], env=env, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, timeout=15)
        probe = subprocess.run(DOCKER + ["inspect", name], env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True, timeout=15)
        return probe.returncode != 0 and "No such object" in probe.stderr
    except (OSError, subprocess.SubprocessError):
        return False


def available_memory(limit, current, host_available, stats):
    # Linux MemAvailable includes reclaimable page cache. Use the same principle
    # within the cgroup, conservatively counting only clean inactive file pages.
    # Subtract all dirty/writeback bytes even if some are outside inactive_file.
    keys = ("inactive_file", "file_dirty", "file_writeback")
    if any(not isinstance(stats.get(key, 0), int) or stats.get(key, 0) < 0 for key in keys):
        raise ValueError("malformed reclaim counters")
    counters_complete = all(key in stats for key in keys)
    inactive = max(0, min(stats.get("inactive_file", 0), current))
    dirty = max(0, stats.get("file_dirty", 0)) + max(0, stats.get("file_writeback", 0))
    reclaimable = max(0, inactive - dirty) if counters_complete else 0
    unused = None if limit is None else limit - current
    cgroup_available = host_available if limit is None else max(0, unused + reclaimable)
    available = min(host_available, cgroup_available)
    return {"available_before": available, "os_available_before": host_available, "strict_unallocated_before": unused,
            "reclaimable_clean_before": reclaimable, "inactive_file_before": inactive,
            "dirty_writeback_before": dirty, "parent_memory_max": limit,
            "parent_memory_current_before": current,
            "availability_method": "min(OS MemAvailable, cgroup unused + clean inactive file cache)",
            "reserve_note": "estimated available headroom after reclaim; not already-unused RAM"}


def choose_limit(available):
    for limit in (LIMIT, 4 * 1024**3, 2 * 1024**3):
        if available - limit >= RESERVE:
            return limit
    return None


def headroom():
    raw_limit = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    limit = None if raw_limit == "max" else int(raw_limit)
    current = int(Path("/sys/fs/cgroup/memory.current").read_text())
    stats = {line.split()[0]: int(line.split()[1]) for line in Path("/sys/fs/cgroup/memory.stat").read_text().splitlines()}
    mem = {line.split(":")[0]: int(line.split()[1]) * 1024
           for line in Path("/proc/meminfo").read_text().splitlines()}
    before = available_memory(limit, current, mem["MemAvailable"], stats)
    limit = choose_limit(before["available_before"])
    if limit is None:
        raise RuntimeError("resource guard: insufficient 4 GiB available headroom even for the 2 GiB profile: " + json.dumps(before))
    return {**before, "reserved_before": before["available_before"] - limit,
            "preferred_memory_limit": LIMIT, "memory_limit": limit, "swap_limit": 0}


def lean(tree, source, log, timeout=180, output=None, cache=None):
    """Run one source check; output is a fresh private relative .olean path."""
    tree, log = Path(tree).resolve(), Path(log).resolve()
    for path in (source, output):
        if path is None:
            continue
        p = Path(path)
        if p.is_absolute() or not p.parts or ".." in p.parts:
            raise ValueError("Lean file must be a relative tree path")
        checked = (tree / p).parent.resolve() if path == output else (tree / p).resolve()
        if not checked.is_relative_to(tree):
            raise ValueError("Lean path escapes private tree")
    guard = headroom()
    limit = guard["memory_limit"]
    if limit not in (LIMIT, 4 * 1024**3, 2 * 1024**3):
        raise ValueError("unapproved hard-memory profile")
    gib = limit // 1024**3
    (tree / ".lake").mkdir(exist_ok=True)
    if not (RUNTIME / "bin/lean").is_file():
        raise RuntimeError("pinned runtime missing")
    args = ["/lean/bin/lean", "-j1", "--tstack=131072", "--json", str(source)]
    if output is not None:
        path = tree / output
        path.parent.mkdir(parents=True, exist_ok=True)
        path.unlink(missing_ok=True)
        args += ["-o", str(output)]
    name = "h28-" + uuid.uuid4().hex
    # Positional arguments stay argv data. The shell script is fixed and cannot
    # be supplied or changed by a manifest entry.
    script = (f'set -eu; test "$(cat /sys/fs/cgroup/memory.max)" = "{limit}"; '
              'test "$(cat /sys/fs/cgroup/memory.swap.max)" = "0"; '
              'set +e; "$@"; code=$?; '
              'printf "\\nH28_CGROUP_PEAK_BYTES=%s\\n" "$(cat /sys/fs/cgroup/memory.peak)"; exit "$code"')
    cache_args = [] if cache is None else ["--mount", f"type=bind,src={Path(cache).resolve()},dst=/cache,readonly"]
    # Cache files are reachable only through the private allowlisted symlinks.
    search = "/task/.lake/build/lib/lean"
    argv = DOCKER + ["run", "--name", name, "--pull=never", f"--memory={gib}g", f"--memory-swap={gib}g",
        "--network=none", "--mount", f"type=bind,src={tree},dst=/task,readonly",
        "--mount", f"type=bind,src={tree / '.lake'},dst=/task/.lake",
        "--mount", "type=bind,src=/workspace/h28-runtime/measure,dst=/measure,readonly",
        "--mount", f"type=bind,src={RUNTIME},dst=/lean,readonly"] + cache_args + ["-w", "/task",
        "-e", "LEAN_NUM_THREADS=1", "-e", "LEAN_PATH=" + search,
        IMAGE, "bash", "-c", script, "h28-lean", "/measure"] + args
    start = time.monotonic()
    env = docker_env()
    timed_out, code, child, failure, state = False, None, None, None, None
    cleanup_confirmed = False
    try:
        with log.open("wb") as stream:
            child = subprocess.Popen(argv, stdout=stream, stderr=subprocess.STDOUT, env=env)
            try:
                code = child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                remove_owned(name, env)
                try:
                    child.wait(timeout=15)
                except subprocess.SubprocessError:
                    child.kill()
                    child.wait(timeout=15)
    except (OSError, subprocess.SubprocessError) as exc:
        failure = type(exc).__name__ + ": " + str(exc)
    finally:
        # Teardown always runs after launch, even if wait/kill/inspection fails.
        if child is not None:
            try:
                if child.poll() is None:
                    child.kill()
                    child.wait(timeout=15)
            except (OSError, subprocess.SubprocessError) as exc:
                failure = type(exc).__name__ + ": " + str(exc)
        try:
            inspect = subprocess.run(DOCKER + ["inspect", name], env=env, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, text=True, timeout=15)
            state = json.loads(inspect.stdout)[0] if inspect.returncode == 0 else None
        except (OSError, subprocess.SubprocessError, ValueError, IndexError) as exc:
            failure = type(exc).__name__ + ": " + str(exc)
        cleanup_confirmed = remove_owned(name, env)
        # Cleanup uncertainty overrides every subsequent parsing/IO error.
        if not cleanup_confirmed:
            raise CleanupError({"container_name": name, "cleanup_confirmed": False,
                "kind": "error", "exit": code, "argv": argv, "lean_argv": args,
                "seconds": time.monotonic() - start, "log_file": str(log),
                "failure": failure, **guard})
    data = log.read_text(errors="replace") if log.exists() else ""
    peak_match = re.search(r"H28_CGROUP_PEAK_BYTES=(\d+)", data)
    measurement = re.search(r"H28_MEASURE (\{[^\n]+\})", data)
    try:
        measured = json.loads(measurement[1]) if measurement else None
        if not isinstance(measured, dict) or not {"exit", "signal", "maxrss_kib", "seconds"} <= set(measured):
            measured = None
        peak = int(peak_match[1]) if peak_match else None
    except (ValueError, TypeError):
        measured, peak = None, None
        failure = "malformed measurement output"
    kind = "timeout" if timed_out else "exit"
    if not timed_out and (failure is not None or state is None or state["State"]["OOMKilled"] or
            state["HostConfig"]["Memory"] != limit or state["HostConfig"]["MemorySwap"] != limit or
            code in (None, 125, 126, 127, 137) or peak is None or measured is None or measured["signal"] != 0 or measured["exit"] != code or
            state["HostConfig"]["NetworkMode"] != "none" or
            any(m["RW"] for m in state["Mounts"] if m["Destination"] != "/task/.lake")):
        kind = "error"
    return {"container_name": name, "cleanup_confirmed": True, "failure": failure,
            "log_sha256": hashlib.sha256(log.read_bytes() if log.exists() else b"").hexdigest(),
            "runtime_lean_sha256": hashlib.sha256((RUNTIME / "bin/lean").read_bytes()).hexdigest(),
            "measurement_binary_sha256": hashlib.sha256(Path("/workspace/h28-runtime/measure").read_bytes()).hexdigest(),
            "argv": argv, "lean_argv": args, "kind": kind, "exit": code,
            "seconds": time.monotonic() - start, "lean_measurement": measured, "cgroup_peak_bytes": peak,
            "oom_killed": state["State"]["OOMKilled"] if state else None,
            "memory_note": "cgroup peak is charged memory; shared pages may be charged to parent. Actual child RSS is in lean_measurement",
            **guard}
