#!/usr/bin/env python3
"""Serial fresh import-closure measurements in a hard 12GiB/no-swap cgroup.
This is a directory measurement, not the repository run-lean.sh final gate.
Never restores old per-master caches; each invocation requires a new output.
"""
import argparse, fcntl, hashlib, importlib.util, json, os, shlex, subprocess, sys, tarfile, time
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
def validate_inventory(census,fresh,baseline):
    if census!=fresh: raise RuntimeError("Stale, incomplete or modified census; regenerate before running")
    if baseline and any(row["sha256"]!=row["base_sha256"] for row in census["closure_sources"]):
        raise RuntimeError("Baseline source closure differs from pinned base")
def main():
    a=argparse.ArgumentParser(); a.add_argument("--root",required=True); a.add_argument("--toolchain",required=True); a.add_argument("--census",required=True); a.add_argument("--out",required=True); a.add_argument("--image",required=True); a.add_argument("--archive",required=True); a.add_argument("--pin"); a.add_argument("--baseline",action="store_true"); a.add_argument("--keysort-only",action="store_true"); args=a.parse_args()
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
    installation=verify_install(Path(args.archive),toolchain)
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
    text=text.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = '+json.dumps(str(out/"build")),1)
    config.write_text(text)
    name="h62-calculus-"+str(os.getpid())
    docker=DOCKER+["run","-d","--name",name,"--network=none","--memory="+str(CAP),"--memory-swap="+str(CAP),"--cpus=1","-e","LEAN_NUM_THREADS=1","-e","LAKE_ARTIFACT_CACHE=false","-e","LAKE_NO_CACHE=true","-e","LAKE_OVERRIDE_LEAN=true","-e","LEAN_SYSROOT="+str(overlay),"-e","PATH="+str(overlay/"bin")+":/usr/local/bin:/usr/bin:/bin","-w",str(root)]
    for path in ("/workspace","/usr","/lib","/lib64","/bin"):
        docker += ["--mount","type=bind,src="+path+",dst="+path+(",readonly" if path!="/workspace" else "")]
    docker += [args.image,"/bin/sleep","infinity"]
    record=dict(root=str(root),head=command(["git","-C",str(root),"rev-parse","HEAD"]).strip(),toolchain=str(toolchain),image=args.image,command=docker,settings=dict(memory=CAP,swap=0,cpus=1,reserve=RESERVE,threads=1),results=[],status="running")
    def save(): (out/"result.json").write_text(json.dumps(record,indent=2)+"\n")
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
        record["lean_version"]=command(DOCKER+["exec",cid,str(toolchain/"bin/lean"),"--version"]).strip()
        record["lake_version"]=command(DOCKER+["exec",cid,str(toolchain/"bin/lake"),"--version"]).strip(); save()
        expected_version="4.24.0" if args.baseline else pin["toolchain"].split(":v",1)[1]
        if "version "+expected_version+"," not in record["lean_version"] or "Lean version "+expected_version+")" not in record["lake_version"]:
            raise RuntimeError("Unexpected Lean/Lake version")
        def headroom():
            mem={k:int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())}
            current=int(Path("/sys/fs/cgroup/memory.current").read_text()); maximum=int(Path("/sys/fs/cgroup/memory.max").read_text())
            available=min(mem["MemAvailable"],maximum-current)
            if available<RESERVE: raise RuntimeError("4GiB reserve violated")
            return available
        for index,module in enumerate(modules):
            minimum=min(minimum,headroom())
            cmd=DOCKER+["exec",cid,str(toolchain/"bin/lake"),"-f",str(config),"--no-cache","build","+"+module+":olean"]
            log=out/(module+".log"); began=time.monotonic(); why=None
            with log.open("w") as stream:
                process=subprocess.Popen(cmd,env=ENV,stdout=stream,stderr=subprocess.STDOUT)
                while process.poll() is None:
                    try:
                        available=headroom(); minimum=min(minimum,available)
                        top=command(DOCKER+["top",cid,"-eo","pid,rss,comm,args"])
                        rows=[line.split(None,3) for line in top.splitlines()[1:]]
                        peak=max(peak,sum(int(row[1])*1024 for row in rows))
                        lean=[row for row in rows if row[2]=="lean"]
                        if len(lean)>1 or any("-j1" not in row[3].split() for row in lean): why="Lean concurrency/explicit -j1 violation"
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
            if why or process.returncode: raise RuntimeError("Module failed: "+module+(": "+why if why else ""))
        after=[dict(row,sha256=hashlib.sha256((root/row["path"]).read_bytes()).hexdigest()) for row in record["source_provenance"]]
        record["sources_unchanged_after"]=after==record["source_provenance"]
        if not record["sources_unchanged_after"]: raise RuntimeError("Source closure changed during measurement")
        if hashlib.sha256(config.read_bytes()).hexdigest()!=record["config_sha256"]: raise RuntimeError("Configuration changed during measurement")
        record["status"]="pass"
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
