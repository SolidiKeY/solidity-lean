#!/usr/bin/env python3
"""Bounded, serial per-file checking when Lean MCP is not exposed."""
import argparse, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument("toolchain",type=Path);ap.add_argument("tree",type=Path);ap.add_argument("label");ap.add_argument("files",nargs="+",type=Path)
a=ap.parse_args();a.toolchain=a.toolchain.resolve();a.tree=a.tree.resolve()
area=Path("/workspace/h62-migrate-counterexamples/evidence")/a.label;area.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env.update(PATH=str(a.toolchain/"bin")+":"+env["PATH"],LEAN_NUM_THREADS="1")
cpu=min(os.sched_getaffinity(0));GIB=1024**3
if len(Path("/proc/swaps").read_text().splitlines())!=1: raise SystemExit("Swap configured")
def limits():
 os.setsid();os.sched_setaffinity(0,{cpu});resource.setrlimit(resource.RLIMIT_AS,(11*GIB,11*GIB))
def headroom():
 used=int(Path("/sys/fs/cgroup/memory.current").read_text())
 available=int(next(l.split()[1] for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemAvailable:")))*1024
 return used<=12*GIB and available>=4*GIB
provenance={"tree":str(a.tree),"lean_version":subprocess.check_output([str(a.toolchain/"bin/lean"),"--version"],text=True).strip(),"lake_version":subprocess.check_output([str(a.toolchain/"bin/lake"),"--version"],text=True).strip(),"lakefile_sha256":hashlib.sha256((a.tree/"lakefile.toml").read_bytes()).hexdigest(),"cpu":cpu,"lean_threads":1,"address_space_limit_gib":11,"cgroup_usage_limit_gib":12,"reserve_gib":4}
(area/"provenance.json").write_text(json.dumps(provenance,indent=2)+"\n")
results=[]
for f in a.files:
 f=f.resolve();cmd=[str(a.toolchain/"bin/lake"),"env","lean","--tstack=131072","-j1",str(f)]
 if not headroom():
  (area/"blocked.json").write_text(json.dumps({"status":"resource-stop","file":str(f),"command":cmd})+"\n")
  raise SystemExit("Insufficient headroom")
 t=time.monotonic();guard=None
 with (area/(f.stem+".log")).open("w") as log:
  try: p=subprocess.Popen(cmd,cwd=a.tree,env=env,preexec_fn=limits,stdout=log,stderr=subprocess.STDOUT)
  except Exception as error:
   (area/"blocked.json").write_text(json.dumps({"status":"launch-failed","file":str(f),"command":cmd,"error":repr(error)})+"\n")
   raise
  while True:
   pid,status,usage=os.wait4(p.pid,os.WNOHANG)
   if pid:
    p.returncode=os.waitstatus_to_exitcode(status);break
   if not headroom() or time.monotonic()-t>180:
    guard="resource-or-time-stop"
    try: os.killpg(p.pid,signal.SIGKILL)
    except ProcessLookupError: pass
    _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status);break
   time.sleep(.2)
 results.append({"file":str(f),"source_sha256":hashlib.sha256(f.read_bytes()).hexdigest(),"command":cmd,"exit":p.returncode,"wall_s":time.monotonic()-t,"max_rss_kib":usage.ru_maxrss,"guard":guard})
 (area/"result.json").write_text(json.dumps(results,indent=2)+"\n")
 print(f.name,p.returncode,flush=True)
 if guard:break
raise SystemExit(0 if len(results)==len(a.files) and all(r["exit"]==0 and not r["guard"] for r in results) else 1)
