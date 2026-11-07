#!/usr/bin/env python3
"""Clean serial dependency-closure measurement; final repository gate is separate."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--census", type=Path, required=True)
parser.add_argument("--toolchain", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--keysort-only", action="store_true")
args = parser.parse_args()
def interrupted(signum, frame):
    raise KeyboardInterrupt("signal " + str(signum))
signal.signal(signal.SIGTERM, interrupted)
signal.signal(signal.SIGHUP, interrupted)
root = Path.cwd()
lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
lockpath.parent.mkdir(parents=True, exist_ok=True)
lock = lockpath.open("a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
subprocess.run(["git", "status", "--short"], check=True)
args.output.mkdir(parents=True, exist_ok=False) # refuse a warm/reused output
args.output = args.output.resolve()
info = json.loads(args.census.read_text())
subprocess.run(["git", "merge-base", "--is-ancestor", info["base"], "HEAD"], check=True)
# Until source adaptation is authorized, require the exact pinned source tree.
subprocess.run(["git", "diff", "--exit-code", info["base"], "--", "Solidity"], check=True,
               stdout=subprocess.DEVNULL)
if subprocess.check_output(["git","ls-files","--others","--exclude-standard","Solidity"],text=True).strip():
    raise RuntimeError("untracked Solidity sources invalidate the census")
for entry in info["files"]:
    if hashlib.sha256((root/entry["path"]).read_bytes()).hexdigest() != entry["sha256"]:
        raise RuntimeError("stale census: " + entry["path"])
if args.toolchain.resolve() == Path("/workspace/migrate-backend-toolchains/lean-4.35.0-linux"):
    pin = json.loads(Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
    archive = Path("/workspace/migrate-backend-evidence/toolchains")/pin["asset"]
    if hashlib.file_digest(archive.open("rb"), "sha256").hexdigest() != pin["sha256"]:
        raise RuntimeError("official release archive hash mismatch")
    for binary in ("lean", "lake"):
        expected = subprocess.check_output(["tar", "--zstd", "-xOf", str(archive),
                                           "lean-4.35.0-linux/bin/"+binary])
        if hashlib.sha256(expected).digest() != hashlib.sha256((args.toolchain/"bin"/binary).read_bytes()).digest():
            raise RuntimeError("installed binary differs from official archive: " + binary)
else:
    if args.toolchain.resolve() != Path("/workspace/.setup/tools/lean-4.24.0-linux"):
        raise RuntimeError("unapproved toolchain path")
lean = str(args.toolchain.resolve()/"bin/lean")
lake = str(args.toolchain.resolve()/"bin/lake")
env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(args.output/"lib"))
modules = ["Solidity.KeySort"] if args.keysort_only else info["topological_closure"]
if "Solidity.KeySort" in modules:
    modules.remove("Solidity.KeySort")
    modules.insert(0, "Solidity.KeySort")
cap = 12*1024**3
reserve = 4*1024**3
cgroup = Path("/sys/fs/cgroup")
limit = int((cgroup/"memory.max").read_text())
if limit < cap+reserve: raise RuntimeError("VM memory cap cannot preserve 4 GiB reserve")
if Path("/proc/swaps").read_text().splitlines()[1:]:
    raise RuntimeError("swap enabled")
report = {"lean": subprocess.check_output([lean,"--version"],text=True).strip(),
          "lake": subprocess.check_output([lake,"--version"],text=True).strip(),
          "head": subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),
          "purpose":"direct compiler diagnostic; does not replace MCP/run-lean.sh final gate",
          "census_sha256": hashlib.sha256(args.census.read_bytes()).hexdigest(),
          "settings": {"threads":1,"lean_args":["-j1","--tstack=131072","-M8192"],
                       "memory_cap_bytes":cap,"module_lean_memory_limit_mib":8192,"reserve_bytes":reserve,"swap":False,
                       "cache":"empty private output, no .lake or remote artifacts",
                       "page_cache":"OS cache not flushed; no performance comparison claimed",
                       "affinity":sorted(os.sched_getaffinity(0))},
          "modules":[],"status":"running"}
start = time.monotonic()
try:
    for m in modules:
        src = root/(m.replace(".","/")+".lean")
        dest = args.output/"lib"/(m.replace(".","/")+".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        log = args.output/(m+".log")
        cmd = [lean,"-j1","--tstack=131072","-M8192","-o",str(dest),str(src)]
        begin = time.monotonic()
        with log.open("w") as stream:
            child = None
            stopped = None
            try:
                child = subprocess.Popen(cmd, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                while child.poll() is None:
                    current = int((cgroup/"memory.current").read_text())
                    available = int(next(line.split()[1] for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:")))*1024
                    if current > min(cap, limit-reserve) or available < reserve:
                        stopped = "RESOURCE_STOP"
                        os.killpg(child.pid, signal.SIGTERM)
                        try: child.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            os.killpg(child.pid, signal.SIGKILL)
                        break
                    time.sleep(0.25)
            finally:
                if child is not None and child.poll() is None:
                    os.killpg(child.pid, signal.SIGTERM)
                    try: child.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL)
                        child.wait()
            code = child.wait()
        row = {"module":m,"command":cmd,"exit":code,"wall_seconds":time.monotonic()-begin,
               "cumulative_max_child_rss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
               "resource_stop":stopped,"log":str(log)}
        report["modules"].append(row)
        print(json.dumps(row), flush=True)
        if code or stopped:
            report["status"] = "blocked"
            report["blocker"] = {"type":stopped or ("BACKEND_COMPILE" if m.startswith("Solidity.Backend.") else "EXTERNAL_DEPENDENCY_COMPILE"),"module":m}
            break
    else: report["status"] = "pass"
except BaseException as exc:
    report["status"] = "interrupted"
    report["exception"] = repr(exc)
    raise
finally:
    report["wall_seconds"] = time.monotonic()-start
    report["max_child_rss_kib"] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    (args.output/"result.json").write_text(json.dumps(report,indent=2)+"\n")
raise SystemExit(0 if report["status"] == "pass" else 1)
