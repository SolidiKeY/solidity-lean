#!/usr/bin/env python3
"""Run the unchanged repository gate with isolated cold Lake outputs and bounds."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import shlex
import signal
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--toolchain", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--checkout", type=Path, required=True)
args = parser.parse_args()
root = args.checkout.resolve()
args.toolchain = args.toolchain.resolve()
if args.toolchain not in (Path("/workspace/.setup/tools/lean-4.24.0-linux"),Path("/workspace/migrate-backend-toolchains/lean-4.35.0-linux")):
    raise RuntimeError("unapproved installation")
lockdir = Path("/tmp/solidity-lean-feature-groups-20261025")
lockdir.mkdir(parents=True,exist_ok=True)
lock = (lockdir/"writer.lock").open("a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(["git","status","--short"],cwd=root,check=True)
if subprocess.check_output(["git","status","--porcelain"],cwd=root,text=True).strip():
    raise RuntimeError("gate checkout must be clean")
if (root/".lake/build").exists(): raise RuntimeError("clean gate requires absent private .lake/build")
args.output.mkdir(parents=True,exist_ok=False)
args.output = args.output.resolve()
config = (root/"lakefile.toml").read_text().replace('enableArtifactCache = true','enableArtifactCache = false')
# Package sources remain the exact checkout; only outputs/cache change.
config = 'srcDir = '+json.dumps(str(root))+'\n'+config
config = config.replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1", "-M8192"]')
(args.output/"lakefile.toml").write_text(config)
binpath = args.output/"bin"
binpath.mkdir()
lean = str(args.toolchain/"bin/lean")
lake = str(args.toolchain/"bin/lake")
# Lake resolves bin/lean from LEAN_SYSROOT; provide a private symlink layout.
sysroot = args.output/"sysroot"
sysroot.mkdir()
for entry in args.toolchain.iterdir():
    if entry.name != "bin": (sysroot/entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
(sysroot/"bin").mkdir()
for entry in (args.toolchain/"bin").iterdir():
    if entry.name != "lean": (sysroot/"bin"/entry.name).symlink_to(entry)
wrapper = sysroot/"bin/lean"
wrapper.write_text('#!/bin/bash\nexec flock '+shlex.quote(str(lockdir/"heavy-lean.lock"))+' '+shlex.quote(lean)+' -j1 "$@" -j1 -M8192\n')
wrapper.chmod(0o700)
(binpath/"lake").write_text('#!/bin/bash\nexec '+shlex.quote(lake)+' --no-cache -d '+shlex.quote(str(root))+' -f '+shlex.quote(str(args.output/"lakefile.toml"))+' "$@"\n')
for p in binpath.iterdir(): p.chmod(0o700)
env = dict(os.environ, PATH=str(binpath)+":"+str(args.toolchain/"bin")+":"+os.environ["PATH"],
           LEAN_NUM_THREADS="1", LEAN=str(wrapper),LEAN_SYSROOT=str(sysroot),LAKE_OVERRIDE_LEAN="true",
           LAKE_NO_CACHE="1",LAKE_ARTIFACT_CACHE="0",LAKE_CACHE_DIR=str(args.output/"unused-cache"))
rules = root/"tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"
if not rules.is_file(): raise RuntimeError("frozen SolKey rules missing; skip is not acceptable")
env["SOLKEY_RULES"] = str(rules)
cap = 12*1024**3
reserve = 4*1024**3
limit = int(Path("/sys/fs/cgroup/memory.max").read_text())
if limit < cap+reserve or Path("/proc/swaps").read_text().splitlines()[1:]:
    raise RuntimeError("insufficient cap or swap enabled")
def interrupted(signum,frame): raise KeyboardInterrupt("signal "+str(signum))
for sig in (signal.SIGTERM,signal.SIGHUP): signal.signal(sig,interrupted)
report = {"command":["bash","./run-lean.sh"],"purpose":"clean unchanged full repository gate baseline",
          "toolchain":str(args.toolchain),"versions":{name:subprocess.check_output([str(args.toolchain/"bin"/name),"--version"],text=True).strip() for name in ("lean","lake")},
          "config":str(args.output/"lakefile.toml"),"cache":"new empty build-only worktree .lake/build; artifact and remote cache disabled",
          "checkout":str(root),
          "head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),
          "source_tree":subprocess.check_output(["git","rev-parse","HEAD^{tree}"],cwd=root,text=True).strip(),
          "cpu_affinity":sorted(os.sched_getaffinity(0)),"cpu_quota":Path("/sys/fs/cgroup/cpu.max").read_text().strip(),
          "lean_wrapper":str(wrapper),
          "solkey_rules":str(rules),"solkey_rules_sha256":hashlib.sha256(rules.read_bytes()).hexdigest(),
          "page_cache":"OS page cache not flushed; matched policy required for comparison",
          "memory_cap_bytes":cap,"module_lean_memory_limit_mib":8192,"reserve_bytes":reserve,"peak_cgroup_bytes":0,"status":"running"}
start = time.monotonic()
child = None
try:
    with (args.output/"gate.log").open("w") as stream:
        child = subprocess.Popen(["bash","./run-lean.sh"],env=env,cwd=root,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        while child.poll() is None:
            current = int(Path("/sys/fs/cgroup/memory.current").read_text())
            available = int(next(line.split()[1] for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:")))*1024
            report["peak_cgroup_bytes"] = max(report["peak_cgroup_bytes"],current)
            if current > min(cap,limit-reserve) or available < reserve:
                report["status"] = "RESOURCE_STOP"
                break
            (args.output/"progress.json").write_text(json.dumps(dict(report,wall_seconds=time.monotonic()-start),indent=2)+"\n")
            time.sleep(0.5)
        if child.poll() is not None and report["status"] == "running":
            report["exit"] = child.returncode
            report["status"] = "pass" if child.returncode == 0 else "fail"
except BaseException as exc:
    report["status"] = "interrupted"
    report["exception"] = repr(exc)
    raise
finally:
    if child is not None and child.poll() is None:
        os.killpg(child.pid,signal.SIGTERM)
        try: child.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGKILL)
            child.wait()
    report["wall_seconds"] = time.monotonic()-start
    report["max_child_rss_kib"] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    (args.output/"result.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report))
raise SystemExit(0 if report["status"] == "pass" else 1)
