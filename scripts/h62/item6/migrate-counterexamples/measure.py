#!/usr/bin/env python3
"""Serial, cold-artifact directory build in an isolated source export.
No remote/artifact cache. All Lean invocations have -j1. No production edits.
"""
import argparse, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
import census
GIB=1024**3
ap=argparse.ArgumentParser()
ap.add_argument("toolchain", type=Path)
ap.add_argument("label")
ap.add_argument("--area", type=Path, default=Path("/workspace/h62-migrate-counterexamples"))
ap.add_argument("--source-ref", default=census.BASE)
a=ap.parse_args()
a.toolchain=a.toolchain.resolve()
area=a.area.resolve(); tree=area/a.label
lean_version=subprocess.check_output([str(a.toolchain/"bin/lean"),"--version"],text=True).strip()
lake_version=subprocess.check_output([str(a.toolchain/"bin/lake"),"--version"],text=True).strip()
version=next((v for v in ("4.24.0","4.35.0") if f"version {v}," in lean_version),None)
if not version or f"Lean version {version}" not in lake_version: raise SystemExit("Unexpected toolchain binaries")
if version=="4.35.0":
    pin=json.loads(Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
    if pin["toolchain"]!="leanprover/lean4:v4.35.0": raise SystemExit("Unexpected coordinator pin")
    with (area/pin["asset"]).open("rb") as archive_input:
        digest=hashlib.file_digest(archive_input,"sha256").hexdigest()
    if digest!=pin["sha256"]: raise SystemExit("Coordinator archive SHA mismatch")
if len(Path("/proc/swaps").read_text().splitlines())!=1: raise SystemExit("Swap is configured: STOP")
source_ref=subprocess.check_output(["git","rev-parse","--verify",a.source_ref+"^{commit}"],cwd=census.ROOT,text=True).strip()
subprocess.run(["git","merge-base","--is-ancestor",census.BASE,source_ref],cwd=census.ROOT,check=True)
if tree.exists(): raise SystemExit("Refuse reuse: label must name a fresh source export")
area.mkdir(parents=True,exist_ok=True); tree.mkdir()
# Export the explicit committed source; local edits are never implicit inputs.
archive=area/(a.label+".tar")
subprocess.run(["git","archive","--format=tar","-o",str(archive),source_ref],cwd=census.ROOT,check=True)
subprocess.run(["tar","xf",str(archive),"-C",str(tree)],check=True)
archive.unlink()
cfg=tree/"lakefile.toml"
s=cfg.read_text().replace("enableArtifactCache = true", "enableArtifactCache = false")
s=s.replace('["--tstack=131072"]','["--tstack=131072", "-j1"]')
cfg.write_text(s)
(tree/"lean-toolchain").write_text("leanprover/lean4:v" + version + "\n")
env=os.environ.copy(); env.update(LEAN_NUM_THREADS="1",PATH=str(a.toolchain/"bin")+":"+env["PATH"],XDG_CACHE_HOME=str(tree/"empty-cache"))
cpus=os.sched_getaffinity(0); cpu=min(cpus)
logdir=area/"evidence"/a.label; logdir.mkdir(parents=True)
source_census=census.inspect(tree)
graph=source_census["import_graph"]
order=[]; seen=set()
def visit(m):
    if m in seen or graph.get(m) is None: return
    seen.add(m)
    for d in graph[m]: visit(d)
    order.append(m)
for m in sorted(graph): visit(m)
# Dependency-free KeySort is the first explicit prerequisite.
order.remove("Solidity.KeySort"); order.insert(0,"Solidity.KeySort")
results={"label":a.label,"base":census.BASE,"tree":str(tree),"cpu":cpu,
    "lean_threads":1,"lean_args":["--tstack=131072","-j1"],"artifact_cache":False,
    "address_space_limit_gib":11,"cgroup_usage_limit_gib":12,"reserve_gib":4,
    "lean_version":lean_version,"source_ref":source_ref,"source_files":source_census["files"],
    "lake_version":lake_version,"clean_policy":"Fresh source export; empty build and artifact cache; OS page cache not flushed",
    "modules":[],"status":"running"}
def save(): (logdir/"result.json").write_text(json.dumps(results,indent=2)+"\n")
def preexec():
    os.setsid(); os.sched_setaffinity(0,{cpu})
    resource.setrlimit(resource.RLIMIT_AS,(11*GIB,11*GIB))
def memory():
    current=int(Path("/sys/fs/cgroup/memory.current").read_text())
    available=int(next(l.split()[1] for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemAvailable:")))*1024
    return current,available
save(); start=time.monotonic(); peak=0; failed=set()
for m in order:
    blocked=[d for d in graph[m] if d in failed]
    if blocked:
        failed.add(m)
        results["modules"].append({"module":m,"exit":None,"status":"dependency-blocked","dependencies":blocked})
        save(); continue
    current,available=memory()
    if current>12*GIB or available<4*GIB:
        results.update(status="resource-stop",blocked_module=m); break
    cmd=[str(a.toolchain/"bin/lake"),"--no-cache","build","+"+m]
    t=time.monotonic(); guard=None
    with (logdir/(m+".log")).open("w") as out:
        try:
            proc=subprocess.Popen(cmd,cwd=tree,env=env,stdout=out,stderr=subprocess.STDOUT,preexec_fn=preexec)
        except Exception as e:
            results.update(status="launch-failed",blocked_module=m,error=repr(e)); save(); raise
        usage=None
        while True:
            pid,status,ru=os.wait4(proc.pid,os.WNOHANG)
            if pid:
                proc.returncode=os.waitstatus_to_exitcode(status); usage=ru; break
            current,available=memory(); peak=max(peak,current)
            if current>12*GIB or available<4*GIB or time.monotonic()-t>1800:
                guard="resource-or-time-stop"
                try: os.killpg(proc.pid,signal.SIGTERM)
                except ProcessLookupError: pass
                time.sleep(1)
                try: os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                _,status,usage=os.wait4(proc.pid,0)
                proc.returncode=os.waitstatus_to_exitcode(status); break
            time.sleep(0.2)
        code=proc.wait()
    results["modules"].append({"module":m,"command":cmd,"exit":code,"wall_s":time.monotonic()-t,"guard":guard,"max_rss_kib":usage.ru_maxrss,"user_s":usage.ru_utime,"system_s":usage.ru_stime})
    save(); print(m,code,flush=True)
    if code or guard:
        failed.add(m)
        results.update(status="failed" if not guard else guard,blocked_module=m)
        if guard or m=="Solidity.KeySort": break
else: results["status"]="failed" if failed else "pass"
results.update(wall_s=time.monotonic()-start,peak_cgroup_bytes=peak,max_child_rss_kib=max((m.get("max_rss_kib",0) for m in results["modules"]),default=0))
save()
raise SystemExit(0 if results["status"]=="pass" else 1)
