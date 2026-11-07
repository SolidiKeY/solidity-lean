#!/usr/bin/env python3
"""Serial source-import prerequisite build, isolated cache, no Lake reuse.
This is a prerequisite diagnostic, never a substitute for run-lean.sh final gates.
"""
import argparse
import json
import os
import pathlib
import resource
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--lean", required=True, type=pathlib.Path)
p.add_argument("--evidence", required=True, type=pathlib.Path)
p.add_argument("module")
a = p.parse_args()
root = pathlib.Path.cwd()
evidence = a.evidence.resolve()
cache = evidence / "lib"
evidence.mkdir(parents=True, exist_ok=True)
seen, order = set(), []
def visit(module):
    if module in seen: return
    seen.add(module)
    source = root / (module.replace(".","/")+".lean")
    if not source.exists(): return  # Toolchain imports are resolved by Lean.
    for line in source.read_text().splitlines():
        if line.startswith("import "):
            for dep in line[7:].split(): visit(dep)
    order.append((module,source))
if not (root / (a.module.replace(".","/")+".lean")).is_file():
    raise SystemExit("TARGET_BLOCK: requested source module does not exist")
visit(a.module)
def limit():
    resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def available():
    mem = dict(line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())
    host = int(mem["MemAvailable"].split()[0])*1024
    cgroup = pathlib.Path("/sys/fs/cgroup")
    cap = (cgroup/"memory.max").read_text().strip()
    if cap != "max": host = min(host,int(cap)-int((cgroup/"memory.current").read_text()))
    return host
rows = []
for module,source in order:
    if available() < 4*1024**3: raise SystemExit("RESOURCE_BLOCK: below 4GiB reserve")
    out = cache / (module.replace(".","/")+".olean")
    out.parent.mkdir(parents=True,exist_ok=True)
    cmd = [str(a.lean.resolve()),"-j1","-M8192","--tstack=131072","-o",str(out),str(source.relative_to(root))]
    start = time.monotonic()
    log = evidence/(module+".log")
    reason = None
    with log.open("w") as stream:
        child = subprocess.Popen(cmd, stdout=stream,stderr=subprocess.STDOUT,
            env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(cache)),preexec_fn=limit)
        while child.poll() is None:
            if available() < 4*1024**3: reason = "RESOURCE_BLOCK: below 4GiB reserve"
            if time.monotonic()-start > 300: reason = "TIME_BLOCK: module exceeded 300 seconds"
            if reason: child.terminate(); break
            try: child.wait(timeout=0.5)
            except subprocess.TimeoutExpired: pass
        try: child.wait(timeout=3)
        except subprocess.TimeoutExpired: child.kill(); child.wait()
    row = dict(module=module,command=cmd,exit=child.returncode,seconds=time.monotonic()-start,
        log=str(log),blocker=reason,maxrss_KiB_cumulative=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    rows.append(row)
    (evidence/"commands.json").write_text(json.dumps(rows,indent=2)+"\n")
    print(json.dumps(row),flush=True)
    if child.returncode or reason: raise SystemExit(1)
