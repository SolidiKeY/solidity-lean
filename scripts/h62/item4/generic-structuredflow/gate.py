#!/usr/bin/env python3
"""Serial pinned-toolchain import-closure probe; outputs exclusively off git.
Not a substitute for run-lean.sh, correspondence, axiom audit, or final timing.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import signal
import uuid
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
IMAGE = "ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852"
PIN = Path("/workspace/h62-coordinator-inputs/toolchain-pin.json")
RUNTIME = Path("/workspace/h62-generic-runtime")


def closure(targets):
    ordered, done, active = [], set(), set()
    def visit(name):
        if name in done or name.startswith(("Lean.", "Init.", "Std.")) or name in ("Lean", "Init", "Std"):
            return
        if name in active:
            raise ValueError("import cycle: " + name)
        path = ROOT / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError("missing local module: " + name)
        active.add(name)
        # Read the comment-masked source using the census lexer.
        from census import mask
        for imports in re.findall(r"(?m)^import +([^\n]+)", mask(path.read_bytes().decode())):
            for dependency in imports.split():
                visit(dependency.replace("«", "").replace("»", ""))
        active.remove(name)
        done.add(name)
        ordered.append(name)
    visit("Solidity.KeySort")
    for name in targets:
        visit(name)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        raise SystemExit("H44: output must be outside repository")
    output.mkdir(parents=True, exist_ok=False)
    pin = json.loads(PIN.read_text())
    if pin["toolchain"] != "leanprover/lean4:v4.35.0":
        raise SystemExit("unexpected toolchain pin")
    archive = RUNTIME / pin["asset"]
    with archive.open("rb") as f:
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    if digest != pin["sha256"]:
        raise SystemExit("archive hash mismatch")
    runtime = RUNTIME / pin["asset"].removesuffix(".tar.zst")
    ordered = closure(args.modules)
    (output/"build").mkdir()
    lines = ["#!/bin/sh", "set -eu", "export LEAN_PATH=/out/build", "/opt/lean/bin/lean --version", "/opt/lean/bin/lake --version",
             'test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888',
             'test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0',
             "trap 'cat /sys/fs/cgroup/memory.peak > /out/memory.peak' EXIT"]
    for module in ordered:
        path = module.replace(".", "/")
        (output/"build"/path).parent.mkdir(parents=True, exist_ok=True)
        command = ["timeout", "300", "/opt/lean/bin/lean", "-j1", "--tstack=131072", "-o", f"/out/build/{path}.olean", path+".lean"]
        lines.extend([f"echo BEGIN_{module}", "start=$(date +%s%N)", "set +e", shlex.join(command), "result=$?", "set -e",
                      f'echo "{module} $result $(($(date +%s%N)-start))" >> /out/modules.tsv',
                      'if [ "$result" != 0 ]; then exit "$result"; fi'])
    (output/"check.sh").write_text("\n".join(lines)+"\n")
    lock = open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    status_before = subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=ROOT, text=True)
    (output/"git-status-before.txt").write_text(status_before)
    sources_before = {m:hashlib.sha256((ROOT/(m.replace(".", "/")+".lean")).read_bytes()).hexdigest() for m in ordered}
    env = os.environ.copy()
    for key in ("DOCKER_HOST", "DOCKER_CONTEXT", "DOCKER_TLS", "DOCKER_TLS_VERIFY", "DOCKER_CERT_PATH"):
        env.pop(key, None)
    docker = ["docker", "--host=unix:///var/run/docker.sock"]
    label = "org.solidity.h62-generic-structuredflow"
    preflight = subprocess.run(docker+["ps", "-a", "--filter", "label="+label, "--format", "{{.Names}} {{.State}}"], env=env, capture_output=True, text=True, timeout=10)
    if preflight.returncode or any(line.split()[-1] != "exited" for line in preflight.stdout.splitlines() if line.strip()):
        (output/"preflight.log").write_text(preflight.stdout+preflight.stderr)
        raise SystemExit("BLOCKED: existing owned gate or Docker inspection failure; see preflight.log")
    name = "h62-generic-" + str(os.getpid()) + "-" + uuid.uuid4().hex[:8]
    command = docker + ["run", "--name", name, "--label", label, "--network", "none", "--memory", "12g", "--memory-swap", "12g", "--cpus", "1", "--user", f"{os.getuid()}:{os.getgid()}",
                       "--mount", f"type=bind,src={ROOT},dst=/repo,readonly",
                       "--mount", f"type=bind,src={runtime},dst=/opt/lean,readonly",
                       "--mount", f"type=bind,src={output},dst=/out", "-w", "/repo", "-e", "LEAN_NUM_THREADS=1", IMAGE, "sh", "/out/check.sh"]
    started = time.monotonic()
    guard = None
    proc = None
    interrupted = None
    def handle_signal(number, _frame):
        nonlocal interrupted
        interrupted = number
    handlers = {number:signal.signal(number, handle_signal) for number in (signal.SIGINT, signal.SIGTERM)}
    with (output/"gate.log").open("w") as log:
        try:
            proc = subprocess.Popen(command, env=env, stdout=log, stderr=subprocess.STDOUT)
            while proc.poll() is None:
                available = int(re.search(r"MemAvailable: +([0-9]+)", Path("/proc/meminfo").read_text()).group(1))*1024
                cgroup = Path("/sys/fs/cgroup")
                maximum = (cgroup/"memory.max").read_text().strip()
                if maximum != "max":
                    available = min(available, int(maximum)-int((cgroup/"memory.current").read_text()))
                if interrupted or available < 4*1024**3:
                    guard = "interrupted signal="+str(interrupted) if interrupted else "available memory below 4 GiB reserve"
                    subprocess.run(docker+["kill", name], env=env, check=False, stdout=log, stderr=log, timeout=10)
                    proc.wait(timeout=15)
                    break
                time.sleep(0.25)
        except Exception as error:
            guard = "gate exception: "+repr(error)
        finally:
            # A disconnected Docker CLI can outlive its client. Inspect and stop
            # only this invocation's unique named container before releasing lock.
            try:
                state = subprocess.run(docker+["inspect", "--format", "{{.State.Running}}", name], env=env, capture_output=True, text=True, timeout=10)
                if state.returncode == 0 and state.stdout.strip() == "true":
                    subprocess.run(docker+["kill", name], env=env, check=False, stdout=log, stderr=log, timeout=10)
                if proc is not None and proc.poll() is None:
                    proc.wait(timeout=15)
            except Exception as error:
                guard = "container cleanup requires inspection: "+repr(error)
            for number, handler in handlers.items():
                signal.signal(number, handler)
    sources_after = {m:hashlib.sha256((ROOT/(m.replace(".", "/")+".lean")).read_bytes()).hexdigest() for m in ordered}
    status_after = subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=ROOT, text=True)
    (output/"git-status-after.txt").write_text(status_after)
    if sources_before != sources_after or status_before != status_after:
        guard = "source or git status drift during gate"
    result_code = proc.returncode if proc is not None and proc.returncode is not None else 1
    result = dict(conditions=dict(toolchain=pin["toolchain"], image=IMAGE, threads=1, lean_j=1,
                  stack=131072, memory=12884901888, swap=0, cpus=1, cache="fresh-private-output", module_timeout_seconds=300, timing_unit="nanoseconds"), command=command, exit=result_code, guard=guard, seconds=time.monotonic()-started,
                  requested=args.modules, closure=ordered, archive_sha256=digest,
                  head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                  source_sha256=sources_after, source_sha256_before=sources_before, git_status_before=status_before, git_status_after=status_after,
                  final_gate=False)
    (output/"receipt.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps(dict(exit=result_code, seconds=result["seconds"], evidence=str(output), guard=guard)))
    raise SystemExit(result_code or bool(guard))


if __name__ == "__main__":
    main()
