#!/usr/bin/env python3
"""Serial fresh import-closure measurements in a hard 12GiB/no-swap cgroup.
This is a directory measurement, not the repository run-lean.sh final gate.
Never restores old per-master caches; each invocation requires a new output.
"""
import argparse, fcntl, hashlib, importlib.util, json, os, shlex, subprocess, sys, tarfile, time, tomllib
sys.dont_write_bytecode=True
from pathlib import Path
CAP=12*1024**3
RESERVE=4*1024**3
DOCKER=["docker","--host=unix:///var/run/docker.sock"]
ENV=os.environ.copy()
for key in ("DOCKER_HOST","DOCKER_CONTEXT","DOCKER_TLS","DOCKER_TLS_VERIFY","DOCKER_CERT_PATH"): ENV.pop(key,None)
def command(args, **kwargs):
    kwargs.setdefault("timeout",5)
    return subprocess.run(args, env=ENV, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, **kwargs).stdout

def stream_digest(stream):
    h=hashlib.sha256()
    while block:=stream.read(1024*1024): h.update(block)
    return h.hexdigest()
def verify_install(archive,install):
    """Compare every archived regular file/link with the selected extracted tree."""
    rows=[]; roots=set()
    process=subprocess.Popen(["zstd","-q","-d","-c",str(archive)],stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=process.stdout,mode="r|") as tar:
            for member in tar:
                parts=Path(member.name).parts
                if not parts or ".." in parts or Path(member.name).is_absolute(): raise RuntimeError("Unsafe archive member")
                roots.add(parts[0]); relative=Path(*parts[1:]); target=install/relative
                if member.isfile():
                    expected=stream_digest(tar.extractfile(member))
                    with target.open("rb") as actual: observed=stream_digest(actual)
                    if expected!=observed: raise RuntimeError("Extracted installation mismatch: "+str(relative))
                    rows.append([str(relative),expected])
                elif member.issym():
                    if not target.is_symlink() or os.readlink(target)!=member.linkname:
                        raise RuntimeError("Extracted symlink mismatch: "+str(relative))
                    rows.append([str(relative),"symlink:"+member.linkname])
                elif not member.isdir(): raise RuntimeError("Unsupported archive member: "+member.name)
        if process.wait(timeout=10)!=0: raise RuntimeError("Archive decompression failed")
        if len(roots)!=1 or not rows: raise RuntimeError("Invalid toolchain archive layout")
        return dict(files=len(rows),manifest_sha256=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest())
    finally:
        if process.poll() is None: process.kill(); process.wait(timeout=5)
def observe_processes(top):
    """Count live processes; exited/zombie tasks cannot perform Lean work."""
    if top.splitlines()[0].split()!=["PID","PPID","RSS","STAT","COMMAND","COMMAND"]:
        raise RuntimeError("Unexpected process snapshot header")
    rows=[line.split(None,5) for line in top.splitlines()[1:]]
    if not rows or any(len(row)!=6 for row in rows): raise RuntimeError("Invalid process snapshot")
    active=[row for row in rows if not row[3].startswith("Z")]
    lean=[row for row in active if row[4]=="lean"]
    if len(lean)>1: raise RuntimeError("Multiple live Lean processes")
    if any("-j1" not in row[5].split() for row in lean): raise RuntimeError("Live Lean missing explicit -j1")
    return sum(int(row[2])*1024 for row in active)
def validate_inventory(census,fresh,baseline):
    if census!=fresh: raise RuntimeError("Stale, incomplete or modified census; regenerate before running")
    if baseline and any(row["sha256"]!=row["base_sha256"] for row in census["closure_sources"]):
        raise RuntimeError("Baseline source closure differs from pinned base")
def main():
    a=argparse.ArgumentParser(); a.add_argument("--root",required=True); a.add_argument("--toolchain",required=True); a.add_argument("--census",required=True); a.add_argument("--out",required=True); a.add_argument("--image",required=True); a.add_argument("--archive",required=True); a.add_argument("--pin"); a.add_argument("--audit-from"); a.add_argument("--cache-root",action="append",default=[]); a.add_argument("--target",action="append",default=[]); a.add_argument("--exclude-dependency"); a.add_argument("--keep-going",action="store_true"); a.add_argument("--fixture",action="append",default=[]); a.add_argument("--baseline",action="store_true"); a.add_argument("--keysort-only",action="store_true"); args=a.parse_args()
    root=Path(args.root).resolve(); toolchain=Path(args.toolchain).resolve(); out=Path(args.out).resolve()
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a"); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    if out.exists(): raise RuntimeError("Output exists; preserve it and use a fresh measurement directory")
    out.mkdir(parents=True)
    census=json.loads(Path(args.census).read_text())
    spec=importlib.util.spec_from_file_location("census",Path(__file__).with_name("census.py"))
    census_module=importlib.util.module_from_spec(spec); spec.loader.exec_module(census_module)
    fresh=census_module.run(root,out/"verified-census")
    validate_inventory(census,fresh,args.baseline)
    command(["git","-C",str(root),"merge-base","--is-ancestor",census["base"],"HEAD"])
    archive_hash=hashlib.sha256(Path(args.archive).read_bytes()).hexdigest()
    pin=json.loads(Path(args.pin).read_text()) if args.pin else None
    if pin and archive_hash!=pin["sha256"]: raise RuntimeError("Toolchain archive differs from coordinator pin")
    if not args.baseline and not pin: raise RuntimeError("New-toolchain run requires coordinator pin")
    modules=["Solidity.KeySort"] if args.keysort_only else census["ordered_local_closure"]
    imports={r["module"]:census_module.header_imports((root/r["path"]).read_text()) for r in census["closure_sources"]}
    assigned=[r["module"] for r in census["modules"]]
    excluded=[]
    if args.exclude_dependency or args.target:
        if args.baseline and args.exclude_dependency: raise RuntimeError("A baseline cannot exclude any dependency")
        if args.exclude_dependency and args.exclude_dependency not in imports: raise RuntimeError("Unknown exclusion dependency")
        if any(m not in assigned for m in args.target): raise RuntimeError("Explicit target outside assignment")
        if args.target and (args.exclude_dependency or args.keysort_only): raise RuntimeError("Conflicting target selectors")
        memo={}
        def depends(module):
            if module==args.exclude_dependency: return True
            if module not in memo: memo[module]=any(depends(d) for d in imports.get(module,[]))
            return memo[module]
        excluded=[m for m in assigned if depends(m)] if args.exclude_dependency else []
        selected=args.target or [m for m in assigned if m not in excluded]
        ordered=[]; visited=set()
        def visit(module):
            if module in visited or module not in imports: return
            visited.add(module)
            for d in imports[module]: visit(d)
            ordered.append(module)
        for m in ["Solidity.KeySort"]+selected: visit(m)
        modules=ordered
    audit=None
    if args.audit_from:
        if not args.baseline or args.target or args.exclude_dependency or args.keysort_only or not args.fixture:
            raise RuntimeError("Audit mode requires old baseline inputs and standalone fixtures only")
        audit_path=Path(args.audit_from);previous=json.loads(audit_path.read_text())
        if previous["status"]!="pass" or previous["scope"]["planned_modules"]!=census["ordered_local_closure"]:
            raise RuntimeError("Audit requires an accepted full directory baseline")
        if previous["source_provenance"]!=census["closure_sources"] or previous["archive_sha256"]!=archive_hash:
            raise RuntimeError("Audit source/toolchain differs from validated baseline")
        audit=dict(result=str(audit_path),sha256=hashlib.sha256(audit_path.read_bytes()).hexdigest(),build_dir=tomllib.loads(previous["config_text"])["buildDir"])
        modules=[]
    fixture_sources=[]
    for fixture in args.fixture:
        path=(root/fixture).resolve()
        if not path.is_relative_to(root/"tests/h62/item6/migrate-calculus") or path.suffix!=".lean": raise RuntimeError("Fixture is outside assigned tests scope")
        fixture_sources.append(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        modules.append("fixture:"+str(path))
    installation=verify_install(Path(args.archive),toolchain)
    cache_condition=None
    if args.cache_root:
        spec=importlib.util.spec_from_file_location("cache_condition",Path(__file__).with_name("cache.py"))
        cache_module=importlib.util.module_from_spec(spec);spec.loader.exec_module(cache_module)
        cache_condition=cache_module.advise_roots(args.cache_root)
        cache_source=Path(__file__).with_name("cache.py").read_bytes()
        cache_condition["helper_sha256"]=hashlib.sha256(cache_source).hexdigest()
        (out/"executed-cache.py").write_bytes(cache_source)
        (out/"cache-condition.json").write_text(json.dumps(cache_condition,indent=2)+"\n")
    overlay=out/"toolchain"; (overlay/"bin").mkdir(parents=True)
    for path in toolchain.iterdir():
        if path.name!="bin": (overlay/path.name).symlink_to(path,target_is_directory=path.is_dir())
    for path in (toolchain/"bin").iterdir():
        if path.name!="lean": (overlay/"bin"/path.name).symlink_to(path)
    (overlay/"bin/lean").write_text("#!/bin/bash\nexec flock "+shlex.quote(str(out/"lean.lock"))+" "+shlex.quote(str(toolchain/"bin/lean"))+" -j1 \"$@\"\n")
    (overlay/"bin/lean").chmod(0o755)
    config=root/"scripts/h62/item6/migrate-calculus"/(".runtime-"+out.name+".toml")
    if config.exists(): raise RuntimeError("Alternate config already exists")
    text=(root/"lakefile.toml").read_text().replace('enableArtifactCache = true','enableArtifactCache = false')
    text=text.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = '+json.dumps(audit["build_dir"] if audit else str(out/"build")),1)
    config.write_text(text)
    name="h62-calculus-"+str(os.getpid())
    docker=DOCKER+["run","-d","--name",name,"--network=none","--memory="+str(CAP),"--memory-swap="+str(CAP),"--cpus=1","-e","LEAN_NUM_THREADS=1","-e","LAKE_ARTIFACT_CACHE=false","-e","LAKE_NO_CACHE=true","-e","LAKE_OVERRIDE_LEAN=true","-e","LEAN_SYSROOT="+str(overlay),"-e","PATH="+str(overlay/"bin")+":/usr/local/bin:/usr/bin:/bin","-w",str(root)]
    for path in ("/workspace","/usr","/lib","/lib64","/bin"):
        docker += ["--mount","type=bind,src="+path+",dst="+path+(",readonly" if path!="/workspace" else "")]
    if args.audit_from:
        docker += ["-e","H62_INTERFACE_OUTPUT="+str(out/"frozen-types.ndjson")]
    docker += [args.image,"/bin/sleep","infinity"]
    record=dict(root=str(root),head=command(["git","-C",str(root),"rev-parse","HEAD"]).strip(),toolchain=str(toolchain),image=args.image,command=docker,settings=dict(memory=CAP,swap=0,cpus=1,reserve=RESERVE,threads=1),results=[],status="running")
    def save(): (out/"result.json").write_text(json.dumps(record,indent=2)+"\n")
    record["audit_reuses_owned_baseline"]=audit
    record["cache_condition"]=cache_condition
    record["invocation"]=[sys.executable]+sys.argv
    record["scope"]=dict(requested_targets=args.target,assigned_count=len(assigned),excluded_dependency=args.exclude_dependency,excluded_modules=excluded,planned_modules=modules,keysort_only=args.keysort_only)
    record["fixture_sources"]=fixture_sources
    record["verified_installation"]=installation
    record["archive_sha256"]=archive_hash
    record["coordinator_pin"]=pin
    record["source_provenance"]=census["closure_sources"]
    record["census_sha256"]=hashlib.sha256(Path(args.census).read_bytes()).hexdigest()
    record["harness_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    record["census_generator_sha256"]=hashlib.sha256(Path(__file__).with_name("census.py").read_bytes()).hexdigest()
    record["graph_sha256"]=hashlib.sha256((root/"scripts/v08-build-graph.py").read_bytes()).hexdigest()
    record["config_sha256"]=hashlib.sha256(config.read_bytes()).hexdigest()
    record["config_text"]=config.read_text()
    record["git_status"]=command(["git","-C",str(root),"status","--porcelain"])
    (out/"executed-bounded.py").write_bytes(Path(__file__).read_bytes())
    cid=command(docker,timeout=20).strip(); record["container"]=cid; save()
    start=time.monotonic(); peak=0; minimum=2**63
    try:
        limits=command(DOCKER+["exec",cid,"/bin/cat","/sys/fs/cgroup/memory.max","/sys/fs/cgroup/memory.swap.max"]).splitlines()
        if limits!=[str(CAP),"0"]: raise RuntimeError("Hard cgroup limits not observed: "+repr(limits))
        record["observed_limits"]=limits
        record["observed_cpu_max"]=command(DOCKER+["exec",cid,"cat","/sys/fs/cgroup/cpu.max"]).strip()
        if record["observed_cpu_max"]!="100000 100000": raise RuntimeError("One-CPU quota not observed")
        record["lean_version"]=command(DOCKER+["exec",cid,str(toolchain/"bin/lean"),"--version"]).strip()
        record["lake_version"]=command(DOCKER+["exec",cid,str(toolchain/"bin/lake"),"--version"]).strip(); save()
        expected_version="4.24.0" if args.baseline else pin["toolchain"].split(":v",1)[1]
        if "version "+expected_version+"," not in record["lean_version"] or "Lean version "+expected_version+")" not in record["lake_version"]:
            raise RuntimeError("Unexpected Lean/Lake version")
        def headroom():
            nonlocal minimum
            mem={k:int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())}
            current=int(Path("/sys/fs/cgroup/memory.current").read_text()); maximum=int(Path("/sys/fs/cgroup/memory.max").read_text())
            available=min(mem["MemAvailable"],maximum-current)
            minimum=min(minimum,available)
            if available<RESERVE:
                record["rejected_memory_snapshot"]=dict(available=available,mem_available=mem["MemAvailable"],cgroup_current=current,cgroup_maximum=maximum,reserve=RESERVE)
                raise RuntimeError("4GiB reserve violated")
            return available
        failed=set()
        for index,module in enumerate(modules):
            if any(d in failed for d in imports.get(module,[])):
                failed.add(module)
                record["results"].append(dict(module=module,exit=None,reason="failed prerequisite",command=None)); save(); continue
            minimum=min(minimum,headroom())
            cmd=DOCKER+["exec",cid,str(toolchain/"bin/lake"),"-f",str(config),"--no-cache","build","+"+module+":olean"]
            if module.startswith("fixture:"):
                cmd=DOCKER+["exec",cid,str(toolchain/"bin/lake"),"-f",str(config),"--no-cache","env","lean","--tstack=131072","-j1",module[len("fixture:"):]]
            log=out/(Path(module[len("fixture:"):]).name+".log" if module.startswith("fixture:") else module+".log"); began=time.monotonic(); why=None
            with log.open("w") as stream:
                process=subprocess.Popen(cmd,env=ENV,stdout=stream,stderr=subprocess.STDOUT)
                while process.poll() is None:
                    try:
                        available=headroom(); minimum=min(minimum,available)
                        top=command(DOCKER+["top",cid,"-eo","pid,ppid,rss,stat,comm,args"])
                        try: peak=max(peak,observe_processes(top))
                        except Exception:
                            record["rejected_process_snapshot"]=top
                            raise
                        if available<RESERVE: why="4GiB reserve violated"
                        if time.monotonic()-began>300: why="300s per-module limit reached"
                        if why: break
                    except Exception as exc:
                        why="Guard observation failed: "+str(exc); break
                    time.sleep(.5)
                if why:
                    command(DOCKER+["kill",cid]); process.wait(timeout=15)
                else: process.wait()
            item=dict(module=module,command=cmd,exit=process.returncode,wall_seconds=time.monotonic()-began,log=str(log),guard=why)
            record["results"].append(item); save()
            print(json.dumps(dict(index=index+1,total=len(modules),**item)),flush=True)
            if why: raise RuntimeError("Module failed: "+module+": "+why)
            if process.returncode:
                failed.add(module)
                if not args.keep_going: raise RuntimeError("Module failed: "+module)
        after=[dict(row,sha256=hashlib.sha256((root/row["path"]).read_bytes()).hexdigest()) for row in record["source_provenance"]]
        record["sources_unchanged_after"]=after==record["source_provenance"]
        if not record["sources_unchanged_after"]: raise RuntimeError("Source closure changed during measurement")
        if hashlib.sha256(config.read_bytes()).hexdigest()!=record["config_sha256"]: raise RuntimeError("Configuration changed during measurement")
        if any(hashlib.sha256(Path(row["path"]).read_bytes()).hexdigest()!=row["sha256"] for row in fixture_sources): raise RuntimeError("Fixture changed during measurement")
        record["status"]="blocked" if failed else "pass"
        if failed: record["error"]="One or more selected modules failed: "+", ".join(sorted(failed))
    except Exception as exc:
        record["status"]="blocked"; record["error"]=str(exc)
    finally:
        record["wall_seconds"]=time.monotonic()-start; record["sampled_aggregate_peak_rss_bytes"]=peak; record["minimum_available_bytes"]=minimum
        try: record["cgroup_peak_bytes"]=command(DOCKER+["exec",cid,"cat","/sys/fs/cgroup/memory.peak"]).strip()
        except (subprocess.CalledProcessError,subprocess.TimeoutExpired): record["cgroup_peak_bytes"]=None
        save(); subprocess.run(DOCKER+["stop","-t","1",cid],env=ENV,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=10)
        config.unlink()
    print(json.dumps(record),flush=True)
    return 0 if record["status"]=="pass" else 1
if __name__=="__main__": raise SystemExit(main())
