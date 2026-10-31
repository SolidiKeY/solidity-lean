#!/usr/bin/env python3
"""Run one serial, offline Lean gate under the assignment's aggregate cap.
Use from the repository root; evidence and cache stay outside exported source.
"""
import argparse
import fcntl
import json
import os
from pathlib import Path
import shlex
import shutil
import signal
import re
import uuid
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--toolchain", required=True, type=Path)
parser.add_argument("--evidence", required=True, type=Path)
parser.add_argument("--name", required=True)
parser.add_argument("--seconds", required=True, type=int)
parser.add_argument("command", nargs=argparse.REMAINDER)
a = parser.parse_args()
command = a.command[1:] if a.command[:1] == ["--"] else a.command
if a.seconds <= 0:
    parser.error("seconds must be positive")
if not command:
    parser.error("missing gate command")
repo = Path.cwd().resolve()
a.evidence.mkdir(parents=True, exist_ok=True)
lock_dir = Path("/tmp/solidity-lean-feature-groups-20261025")
lock_dir.mkdir(exist_ok=True)
with (lock_dir / "writer.lock").open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    status = subprocess.check_output(["git", "status", "--short"], text=True)
    wrapper = a.evidence.parent / "lean-serial"
    wrapper.write_text("#!/bin/bash\nexport LD_LIBRARY_PATH=" + shlex.quote(str(a.toolchain / "lib/lean")) +
                       "${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}\nexec /usr/local/bin/flock " +
                       shlex.quote(str(a.evidence.parent / "compiler.lock")) +
                       ' /opt/lean-real/bin/lean -j1 "$@"\n')
    wrapper.chmod(0o755)
    docker_env = os.environ.copy()
    for selector in ["DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"]:
        docker_env.pop(selector, None)
    docker = ["docker", "--host=unix:///var/run/docker.sock"]
    cidfile = a.evidence / (a.name + "-" + uuid.uuid4().hex + ".cid")
    def owned_cid():
        try:
            cid = cidfile.read_text().strip()
        except FileNotFoundError:
            return None
        return cid if re.fullmatch("[0-9a-f]{64}", cid) else None
    invocation = docker + ["run", "--name", "v12-" + a.name, "--memory=12g", "--memory-swap=12g", "--cidfile", str(cidfile),
        "--network=none", "--user", str(os.getuid()) + ":" + str(os.getgid()),
        "-v", "/workspace:/workspace", "-v", str(lock_dir) + ":" + str(lock_dir), "-v", str(a.toolchain) + ":/opt/lean-real:ro",
        "-v", str(wrapper) + ":" + str(a.toolchain / "bin/lean") + ":ro",
        "-v", "/usr/bin/flock:/usr/local/bin/flock:ro", "-w", str(repo),
        "-e", "LEAN_SYSROOT=" + str(a.toolchain),
        "-e", "PATH=" + str(a.toolchain / "bin") + ":/usr/local/bin:/usr/bin:/bin",
        "-e", "LEAN_NUM_THREADS=1"]
    node = shutil.which("node")
    if node:
        invocation += ["-v", node + ":/usr/local/bin/node:ro"]
    invocation += ["-v", "/usr/bin/git:/usr/local/bin/git:ro"]
    if os.environ.get("SOLKEY_RULES"):
        invocation += ["-e", "SOLKEY_RULES=" + os.environ["SOLKEY_RULES"]]
    # The container, not its monitor, owns the canonical lock during the gate.
    # Even SIGKILL of this Python process cannot release the build's lock.
    bounded = ["timeout", "--signal=TERM", "--kill-after=10s", str(a.seconds), "bash", "-c", shlex.join(command)]
    gate = shlex.join(bounded) + '; result=$?; echo CAP_EVIDENCE; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max /sys/fs/cgroup/memory.peak; exit "$result"'
    invocation += ["ubuntu:24.04", "/usr/local/bin/flock", str(lock_dir / "writer.lock"), "bash", "-c", gate]
    start = time.monotonic()
    peak_rss = 0
    samples = 0
    disk_before = shutil.disk_usage(repo)._asdict()
    interruption = None
    process = None
    def interrupt(signum, frame):
        raise InterruptedError("gate monitor interrupted by signal " + str(signum))
    signal.signal(signal.SIGTERM, interrupt)
    try:
        with (a.evidence / (a.name + ".log")).open("w") as log:
            process = subprocess.Popen(invocation, stdout=log, stderr=subprocess.STDOUT, env=docker_env)
            # Let the inner flock acquire ownership; it may wait for another
            # canonical writer and cannot execute the gate until that is safe.
            fcntl.flock(lock, fcntl.LOCK_UN)
            while process.poll() is None:
                cid = owned_cid()
                if cid is None:
                    time.sleep(0.1)
                    continue
                sample = subprocess.run(docker + ["top", cid, "-eo", "pid,comm,rss"],
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=docker_env)
                if sample.returncode == 0:
                    rss = sum(int(line.split()[-1]) for line in sample.stdout.splitlines()[1:]
                              if line.split() and line.split()[-1].isdigit())
                    peak_rss = max(peak_rss, rss)
                    samples += 1
                time.sleep(0.5)
    except (KeyboardInterrupt, InterruptedError) as exc:
        interruption = str(exc) or "KeyboardInterrupt"
    finally:
        # Stop/wait only the CID created by this invocation, never by name.
        # A failed name-collision launch must not stop the existing container.
        # If the monitor was SIGKILLed, the container still holds writer.lock.
        cid = owned_cid()
        if cid is not None:
            running = subprocess.run(docker + ["inspect", "--format", "{{.State.Running}}", cid],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=docker_env)
            if running.returncode == 0 and running.stdout.strip() == "true":
                subprocess.run(docker + ["stop", "--time", "10", cid],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=docker_env, timeout=20)
        if process is not None:
            process.wait(timeout=20)
    result = {"command": command, "docker": invocation, "exit_code": 130 if interruption else process.returncode, "interruption": interruption, "container_id": owned_cid(),
        "wall_time_bound_seconds": a.seconds,
        "elapsed_seconds": round(time.monotonic() - start, 3), "peak_sampled_aggregate_rss_kib": peak_rss,
        "rss_samples": samples, "git_status_before": status, "disk_before": disk_before,
        "disk_after": shutil.disk_usage(repo)._asdict()}
    (a.evidence / (a.name + ".json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["command", "exit_code", "elapsed_seconds", "peak_sampled_aggregate_rss_kib"]}))
    raise SystemExit(result["exit_code"])
