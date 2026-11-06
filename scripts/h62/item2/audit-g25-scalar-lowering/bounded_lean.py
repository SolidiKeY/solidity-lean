#!/usr/bin/env python3
"""Serial source check into a toolchain-isolated off-git cache.

No interface edits, no proof-budget overrides, no Lake/v4.24 cache reuse.
Each imported repository module is compiled once in topological order. This
is per-file dependency validation; it DOES NOT replace ./run-lean.sh final gate.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time
import census


def available():
    mem = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    host = int(mem["MemAvailable"].split()[0]) * 1024
    cg = Path("/sys/fs/cgroup")
    cap = (cg/"memory.max").read_text().strip()
    if cap != "max": host = min(host, int(cap)-int((cg/"memory.current").read_text()))
    if int((cg/"memory.swap.current").read_text()): raise RuntimeError("nonzero cgroup swap")
    return host


def dependencies(repo, targets):
    seen, active, ordered = set(), set(), []
    def visit(module):
        if module in seen: return
        if module in active: raise ValueError("cyclic dependency: " + module)
        path = repo / (module.replace(".", "/") + ".lean")
        if not path.exists():
            if module.startswith(("Lean", "Init", "Std")): return
            raise ValueError("missing repository import: " + module)
        active.add(module)
        for line in census.mask(path.read_text()).splitlines():
            if line.startswith("import "):
                for imp in line[7:].split(): visit(imp)
        active.remove(module); seen.add(module); ordered.append(module)
    for target in targets: visit(target)
    return ordered


def limits():
    cap = 12 * 1024**3
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))


def terminate(proc):
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGTERM)
        try: proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()


def interrupted(signum, _frame):
    raise SystemExit(128+signum)


def main():
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--toolchain", type=Path, required=True)
    p.add_argument("--artifacts", type=Path, required=True)
    p.add_argument("--direct", action="store_true",
                   help="check only named files; require imports already built in this isolated cache")
    p.add_argument("modules", nargs="+")
    a = p.parse_args()
    repo, artifacts = a.repo.resolve(), a.artifacts.resolve()
    cache = artifacts/"lib"/"lean"
    cache.mkdir(parents=True, exist_ok=True)
    logs = artifacts/"logs"; logs.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(cache))
    summary = []
    for module in (a.modules if a.direct else dependencies(repo, a.modules)):
        if available() < 4*1024**3: raise RuntimeError("less than 4 GiB headroom")
        source = repo/(module.replace(".", "/")+".lean")
        output = cache/(module.replace(".", "/")+".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(module+".log")
        cmd = [str(a.toolchain/"bin"/"lean"), "-j1", "--tstack=131072",
               "--root="+str(repo), "-o", str(output), str(source)]
        start = time.monotonic()
        with log.open("w") as stream:
            proc = subprocess.Popen(cmd, cwd=repo, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=limits)
            resource_stop = False
            try:
                while proc.poll() is None:
                    if available() < 4*1024**3:
                        resource_stop = True
                        terminate(proc)
                        break
                    time.sleep(1)
                code = proc.wait()
            finally:
                terminate(proc)
        row = dict(module=module, command=cmd, exit=code, resource_stop=resource_stop,
                   seconds=round(time.monotonic()-start, 3), log=str(log),
                   source_sha256=census.digest(source.read_bytes()))
        summary.append(row)
        (artifacts/"results.json").write_text(json.dumps(summary,indent=2)+"\n")
        print(json.dumps(row), flush=True)
        if code or resource_stop: raise SystemExit(1)

if __name__ == "__main__": main()
