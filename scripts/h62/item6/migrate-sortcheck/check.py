#!/usr/bin/env python3
"""Clean, serial per-file Lean closure check. No Lake/shared cache is read.
Not a replacement for the required final repository run-lean.sh gate.
Run once per compiler with distinct empty output directories on the same VM.
"""
import argparse, fcntl, hashlib, json, os, pathlib, resource, signal, subprocess, time
import sys
sys.dont_write_bytecode = True
from census import ROOT, TARGETS, closure, path
p=argparse.ArgumentParser(); p.add_argument("--toolchain",required=True,type=pathlib.Path)
p.add_argument("--out",required=True,type=pathlib.Path); p.add_argument("--targets",nargs="+",default=TARGETS)
p.add_argument("--dependency-lib",action="append",type=pathlib.Path,default=[])
p.add_argument("--source-root",type=pathlib.Path,default=ROOT)
p.add_argument("--run",action="store_true")
p.add_argument("--run-args",nargs=argparse.REMAINDER,default=[])
a=p.parse_args(); source_root=a.source_root.resolve()
def source(m): return source_root/(m.replace(".","/")+".lean")
out=a.out.resolve(); out.mkdir(parents=True,exist_ok=True)
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(["git","status","--short","--branch"],cwd=ROOT,check=True)
build=out/"lib"; build.mkdir() # refuse a non-clean run, never delete artifacts
lean=a.toolchain.resolve()/"bin/lean"; lake=a.toolchain.resolve()/"bin/lake"
for lib in a.dependency_lib:
    if not lib.is_dir(): raise ValueError("missing prerequisite library: "+str(lib))
# Lean selects a package root before resolving a module. Overlay prerequisites
# into a single private root; never write through a prerequisite symlink.
for lib in a.dependency_lib:
    for item in sorted(lib.resolve().rglob("*")):
        if item.is_file():
            dest=build/item.relative_to(lib.resolve())
            dest.parent.mkdir(parents=True,exist_ok=True)
            if dest.exists():
                if hashlib.sha256(dest.read_bytes()).digest()!=hashlib.sha256(item.read_bytes()).digest():
                    raise ValueError("conflicting prerequisite artifact: "+str(dest))
            else: dest.symlink_to(item)
env=dict(os.environ,LEAN_NUM_THREADS="1",LEAN_PATH=str(build))
versions={x:subprocess.check_output([str(y),"--version"],text=True).strip() for x,y in [("lean",lean),("lake",lake)]}
limit=12*1024**3; reserve=4*1024**3
# RLIMIT_AS is an additional per-process bound; aggregate RSS/headroom guard below.
def bound(): resource.setrlimit(resource.RLIMIT_AS,(limit,limit))
def stats(pgid):
    rss=0
    for d in pathlib.Path("/proc").iterdir():
        if not d.name.isdigit(): continue
        try:
            stat=(d/"stat").read_text().rsplit(")",1)[1].split()
            if int(stat[2])==pgid: rss+=int(stat[21])*os.sysconf("SC_PAGE_SIZE")
        except (OSError,ValueError,IndexError): pass
    mem={k:int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())}
    cgroup=pathlib.Path("/sys/fs/cgroup")
    cap=(cgroup/"memory.max").read_text().strip(); used=int((cgroup/"memory.current").read_text())
    avail=min(mem["MemAvailable"],int(cap)-used) if cap!="max" else mem["MemAvailable"]
    if mem.get("SwapTotal",0): raise RuntimeError("swap configured; refuse Lean")
    return rss,avail
modules=a.targets if a.dependency_lib else closure(a.targets)
for m in modules:
    if not source(m).is_file(): raise ValueError("missing target source: "+m)
def interrupted(signum, frame): raise KeyboardInterrupt("signal "+str(signum))
signal.signal(signal.SIGTERM,interrupted)
def snapshot():
    artifacts={str(lib.resolve()):{str(x.relative_to(lib.resolve())):hashlib.sha256(x.read_bytes()).hexdigest()
      for x in sorted(lib.resolve().rglob("*")) if x.is_file()} for lib in a.dependency_lib}
    return {"runner_sha256":hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
      "census_runner_sha256":hashlib.sha256(pathlib.Path(__file__).with_name("census.py").read_bytes()).hexdigest(),
      "prerequisite_artifact_sha256":artifacts,"head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
      "source_sha256":{m:hashlib.sha256(source(m).read_bytes()).hexdigest() for m in modules}}
archive=pathlib.Path(str(a.toolchain.resolve())+".tar.zst")
archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest() if archive.is_file() else None
before=snapshot()
rows=[]; start=time.monotonic(); failure=None
for m in modules:
    dest=build/(m.replace(".","/")+".olean"); dest.parent.mkdir(parents=True,exist_ok=True)
    if dest.is_symlink(): dest.unlink()
    cmd=[str(lean),"-j1","--tstack=131072","-o",str(dest),str(source(m).relative_to(source_root))]
    if a.run: cmd=[str(lean),"-j1","--tstack=131072","--run",str(source(m).relative_to(source_root)),*a.run_args]
    rss,avail=stats(-1)
    if avail<reserve: failure="preflight available memory below 4 GiB"; break
    tick=time.monotonic(); peak=0; stop=None
    with (out/(m+".log")).open("w") as log:
        proc=subprocess.Popen(cmd,cwd=source_root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=bound)
        try:
            while proc.poll() is None:
                rss,avail=stats(proc.pid); peak=max(peak,rss)
                if rss>limit or avail<reserve or time.monotonic()-tick>300:
                    stop="resource/time guard"; break
                time.sleep(.1)
        except BaseException as error:
            stop="monitor exception: "+repr(error)
        finally:
            if proc.poll() is None:
                try: os.killpg(proc.pid,signal.SIGTERM)
                except ProcessLookupError: pass
            try: code=proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try: os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                code=proc.wait()
    row={"module":m,"command":cmd,"exit":code,"wall_s":time.monotonic()-tick,"sampled_peak_aggregate_rss_bytes":peak,"stop":stop}
    rows.append(row); print(json.dumps(row),flush=True)
    if code or stop: failure=m; break
elapsed=time.monotonic()-start
after=snapshot()
if before!=after: failure="source/head changed during run"
report={"toolchain_archive_sha256":archive_sha256,"source_before":before,"source_after":after,"versions":versions,"targets":a.targets,"source_root":str(source_root),"dependency_libs":[str(x.resolve()) for x in a.dependency_lib],"clean":not bool(a.dependency_lib),"cache":"explicit prerequisite libraries for focused checks; fresh private output; OS page cache not flushed" if a.dependency_lib else "none: fresh private olean directory; OS page cache not flushed",
 "resources":{"threads":1,"lean_j":1,"rss_limit_bytes":limit,"reserve_bytes":reserve,"swap":0,"per_module_timeout_s":300},
 "rows":rows,"wall_s":elapsed,"sampled_peak_aggregate_rss_bytes":max((r["sampled_peak_aggregate_rss_bytes"] for r in rows),default=0),"kernel_children_cumulative_max_rss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"failure":failure,
 "status":"fail" if failure else "pass","boundary":"per-file elaboration/kernel closure; final run-lean.sh and executable conformance separate"}
(out/"result.json").write_text(json.dumps(report,indent=2)+"\n")
raise SystemExit(bool(failure))
