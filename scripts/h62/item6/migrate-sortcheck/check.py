#!/usr/bin/env python3
"""Clean, serial per-file Lean closure check. No Lake/shared cache is read.
Not a replacement for the required final repository run-lean.sh gate.
Run once per compiler with distinct empty output directories on the same VM.
"""
import argparse, fcntl, hashlib, json, os, pathlib, resource, signal, subprocess, time
import sys
sys.dont_write_bytecode = True
from census import ROOT, TARGETS, closure, imports
p=argparse.ArgumentParser(); p.add_argument("--toolchain",required=True,type=pathlib.Path)
p.add_argument("--out",required=True,type=pathlib.Path); p.add_argument("--targets",nargs="+",default=TARGETS)
p.add_argument("--dependency-lib",action="append",type=pathlib.Path,default=[])
p.add_argument("--source-root",type=pathlib.Path,default=ROOT)
p.add_argument("--run",action="store_true")
p.add_argument("--lake-exe",choices=["solkeycheck"],help="native conformance after dependency-ordered object builds")
p.add_argument("--lake-build",action="store_true",help="serial dependency-ordered Lake leanArts in a private cache-disabled project")
p.add_argument("--run-args",nargs=argparse.REMAINDER,default=[])
a=p.parse_args()
if a.lake_build and (a.run or a.dependency_lib): p.error("Lake clean builds cannot use run mode or prerequisite libraries")
if a.lake_exe and (not a.lake_build or a.targets!=["SolkeyCheck"]):
    p.error("native conformance requires --lake-build --targets SolkeyCheck")
frozen_rules=ROOT/"tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"
if a.lake_exe:
    if a.run_args!=["--key",str(frozen_rules)] or hashlib.sha256(frozen_rules.read_bytes()).hexdigest()!="02b7a995c9aaf1a856019d7071ca3e75a57de91b071c93b24ebf6ae7eef989eb":
        p.error("native conformance requires the exact explicit frozen rules input")
source_root=a.source_root.resolve()
def source(m): return source_root/(m.replace(".","/")+".lean")
out=a.out.resolve(); out.mkdir(parents=True,exist_ok=True)
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(["git","status","--short","--branch"],cwd=ROOT,check=True)
build=out/("lake-build/lib/lean" if a.lake_build else "lib")
build.mkdir(parents=True) # refuse a non-clean run, never delete artifacts
lake_profile_template=None
if a.lake_build:
    original=(ROOT/"lakefile.toml").read_text()
    assert original.count("enableArtifactCache = true")==1
    lake_profile_template=original.replace("enableArtifactCache = true", "enableArtifactCache = false")
    lake_profile_template=lake_profile_template.replace('version = "0.1.0"', 'version = "0.1.0"\nsrcDir = "__SOURCE_ROOT__"\nbuildDir = "__PRIVATE_BUILD__"')
    lake_profile_template=lake_profile_template.replace('["--tstack=131072"]','["--tstack=131072", "-j1"]')
    lake_profile_template=lake_profile_template.replace('[[lean_exe]]','[[lean_exe]]\nweakLeanArgs = ["--tstack=131072", "-j1"]')
    project=out/"lake-project"; project.mkdir()
    profile=lake_profile_template.replace("__SOURCE_ROOT__",str(source_root)).replace("__PRIVATE_BUILD__",str(out/"lake-build"))
    (project/"lakefile.toml").write_text(profile)
    (project/"lean-toolchain").write_text("leanprover/lean4:v"+("4.35.0" if "4.35.0" in str(a.toolchain) else "4.24.0")+"\n")
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
env=dict(os.environ,LEAN_NUM_THREADS="1",LEAN_PATH=str(build),PATH=str(lean.parent)+os.pathsep+os.environ.get("PATH",""),XDG_CACHE_HOME=str(out/"cache"))
versions={x:subprocess.check_output([str(y),"--version"],text=True).strip() for x,y in [("lean",lean),("lake",lake)]}
limit=12*1024**3; reserve=4*1024**3
# RLIMIT_AS is an additional per-process bound; aggregate RSS/headroom guard below.
def bound(): resource.setrlimit(resource.RLIMIT_AS,(limit,limit))
def stats(pgid):
    rss=0; workers=0
    for d in pathlib.Path("/proc").iterdir():
        if not d.name.isdigit(): continue
        try:
            stat=(d/"stat").read_text().rsplit(")",1)[1].split()
            if int(stat[2])==pgid:
                rss+=int(stat[21])*os.sysconf("SC_PAGE_SIZE")
                if (d/"comm").read_text().strip()=="lean": workers+=1
        except (OSError,ValueError,IndexError): pass
    mem={k:int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())}
    cgroup=pathlib.Path("/sys/fs/cgroup")
    cap=(cgroup/"memory.max").read_text().strip(); used=int((cgroup/"memory.current").read_text())
    avail=min(mem["MemAvailable"],int(cap)-used) if cap!="max" else mem["MemAvailable"]
    if mem.get("SwapTotal",0): raise RuntimeError("swap configured; refuse Lean")
    return rss,avail,workers
modules=a.targets if a.dependency_lib else closure(a.targets, source_root)
for m in modules:
    if not source(m).is_file(): raise ValueError("missing target source: "+m)
def interrupted(signum, frame): raise KeyboardInterrupt("signal "+str(signum))
signal.signal(signal.SIGTERM,interrupted)
def snapshot():
    artifacts={str(lib.resolve()):{str(x.relative_to(lib.resolve())):hashlib.sha256(x.read_bytes()).hexdigest()
      for x in sorted(lib.resolve().rglob("*")) if x.is_file()} for lib in a.dependency_lib}
    return {"runner_sha256":hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
      "census_runner_sha256":hashlib.sha256(pathlib.Path(__file__).with_name("census.py").read_bytes()).hexdigest(),
      "lake_profile_sha256":hashlib.sha256(lake_profile_template.encode()).hexdigest() if lake_profile_template else None,
      "external_input_sha256":{str(frozen_rules):hashlib.sha256(frozen_rules.read_bytes()).hexdigest()} if a.lake_exe else {},
      "prerequisite_artifact_sha256":artifacts,"head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),
      "imports":{m:imports(m,source_root) for m in modules},
      "source_sha256":{m:hashlib.sha256(source(m).read_bytes()).hexdigest() for m in modules}}
archive=pathlib.Path(str(a.toolchain.resolve())+".tar.zst")
archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest() if archive.is_file() else None
before=snapshot()
rows=[]; start=time.monotonic(); failure=None
jobs=[(m,False) for m in modules]
if a.lake_exe: jobs.append(("executable:"+a.lake_exe,True))
for m,exe_phase in jobs:
    if exe_phase:
        cmd=[str(lake),"--dir",str(project),"--no-cache","--verbose","exe",a.lake_exe,*a.run_args]
    else:
        dest=build/(m.replace(".","/")+".olean"); dest.parent.mkdir(parents=True,exist_ok=True)
        # Never write module-system output siblings through prerequisite links.
        for sibling in dest.parent.glob(dest.stem+".*"):
            if sibling.is_symlink(): sibling.unlink()
        cmd=[str(lean),"-j1","--tstack=131072","-o",str(dest),str(source(m).relative_to(source_root))]
        if a.run: cmd=[str(lean),"-j1","--tstack=131072","--run",str(source(m).relative_to(source_root)),*a.run_args]
        if a.lake_build:
            facet=":o" if a.lake_exe else ""
            cmd=[str(lake),"--dir",str(project),"--no-cache","--verbose","build","+"+m+facet]
    rss,avail,workers=stats(-1)
    if avail<reserve: failure="preflight available memory below 4 GiB"; break
    tick=time.monotonic(); peak=0; max_workers=0; stop=None
    with (out/(m+".log")).open("w") as log:
        proc=subprocess.Popen(cmd,cwd=source_root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=bound)
        try:
            while proc.poll() is None:
                rss,avail,workers=stats(proc.pid); peak=max(peak,rss); max_workers=max(max_workers,workers)
                if rss>limit or avail<reserve or workers>1 or time.monotonic()-tick>300:
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
    row={"module":m,"command":cmd,"exit":code,"wall_s":time.monotonic()-tick,"sampled_peak_aggregate_rss_bytes":peak,"max_concurrent_lean_processes":max_workers,"stop":stop}
    rows.append(row); print(json.dumps(row),flush=True)
    if code or stop: failure=m; break
elapsed=time.monotonic()-start
after=snapshot()
if before!=after: failure="source/head changed during run"
report={"comparison_scope":"directory" if a.targets==TARGETS and not a.dependency_lib and not a.run and not a.lake_exe else "module",
 "build_kind":"lake-native-executable" if a.lake_exe else "lake-leanArts" if a.lake_build else "execution" if a.run else "per-file-elaboration",
 "artifact_root":str(build),"toolchain_archive_sha256":archive_sha256,"source_before":before,"source_after":after,"versions":versions,"targets":a.targets,"source_root":str(source_root),"dependency_libs":[str(x.resolve()) for x in a.dependency_lib],"clean":not bool(a.dependency_lib),"cache":"explicit prerequisite libraries for focused checks; fresh private output; OS page cache not flushed" if a.dependency_lib else "none: fresh private olean directory; OS page cache not flushed",
 "resources":{"threads":1,"lean_j":1,"rss_limit_bytes":limit,"reserve_bytes":reserve,"swap":0,"per_module_timeout_s":300},
 "rows":rows,"wall_s":elapsed,"sampled_peak_aggregate_rss_bytes":max((r["sampled_peak_aggregate_rss_bytes"] for r in rows),default=0),"kernel_children_cumulative_max_rss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"failure":failure,
 "status":"fail" if failure else "pass","boundary":"native Lake solkeycheck against explicit frozen file; not full directory/Faithfulness/run-lean.sh acceptance" if a.lake_exe else "Lake leanArts closure with generated C; full repository run-lean.sh and native executable conformance separate" if a.lake_build else "per-file elaboration/kernel closure; final run-lean.sh and executable conformance separate"}
(out/"result.json").write_text(json.dumps(report,indent=2)+"\n")
raise SystemExit(bool(failure))
