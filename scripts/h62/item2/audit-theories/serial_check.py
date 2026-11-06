#!/usr/bin/env python3
"""Serial isolated Lean checks; supplement, never replace ./run-lean.sh final gate.
Acquires the repository writer lock. No swap; 12GiB child VM limit, >=4GiB
container/host available reserve, <=300s per module. All artifacts off Git.
"""
import argparse, fcntl, hashlib, json, os, resource, signal, subprocess, sys, time
from pathlib import Path
from census import ROOT, mask, module_to_path

GIB=1024**3

def available():
    mem=dict(line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())
    host=int(mem["MemAvailable"].split()[0])*1024
    cg=Path("/sys/fs/cgroup")
    cap=(cg/"memory.max").read_text().strip()
    if cap != "max": host=min(host,int(cap)-int((cg/"memory.current").read_text()))
    return host

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(12*GIB,12*GIB))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--fresh-targets",action="store_true",help="Recheck requested targets, retaining dependency cache")
    ap.add_argument("targets",nargs="+")
    a=ap.parse_args(); out=a.out.resolve(); lean=a.lean.resolve()
    if out.is_relative_to(ROOT): raise SystemExit("Evidence must be off Git")
    if "SwapTotal:             0 kB" not in Path("/proc/meminfo").read_text():
        # Parse rather than depend on whitespace on other Linux installations.
        swap=next(l for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("SwapTotal:"))
        if int(swap.split()[1]): raise SystemExit("Swap enabled; no-swap boundary not established")
    lock=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lock.parent.mkdir(parents=True,exist_ok=True)
    with lock.open("a") as lk:
        fcntl.flock(lk,fcntl.LOCK_EX)
        print(subprocess.check_output(["git","status","--short","--branch"],cwd=ROOT,text=True),flush=True)
        out.mkdir(parents=True,exist_ok=True)
        lib=out/"olean"; lib.mkdir(exist_ok=True)
        version=subprocess.check_output([str(lean),"--version"],text=True).strip()
        print(version,flush=True)
        previous=out/"results.json"
        if previous.exists():
            history=out/"history"; history.mkdir(exist_ok=True)
            payload=previous.read_bytes()
            (history/(hashlib.sha256(payload).hexdigest()+".json")).write_bytes(payload)
        results=[]; visited=set(); hashes={}
        def record(row):
            results.append(row)
            pending=out/"results.json.tmp"
            pending.write_text(json.dumps({"version":version,"checks":results},indent=2)+"\n")
            pending.replace(out/"results.json")
        env=os.environ.copy(); env["LEAN_NUM_THREADS"]="1"; env["LEAN_PATH"]=str(lib)
        def check(path):
            path=Path(path); module=".".join(path.with_suffix("").parts)
            key=path.as_posix()
            if key in visited: return
            source=(ROOT/path).read_text()
            deps=[]
            for line in mask(source).splitlines():
                if line.startswith("import "):
                    for imp in line.split()[1:]:
                        dep=module_to_path(imp)
                        if (ROOT/dep).is_file(): check(dep); deps.append(hashes[dep.as_posix()])
            digest=hashlib.sha256((version+source+"".join(deps)).encode()).hexdigest()
            target=lib/path.with_suffix(".olean"); target.parent.mkdir(parents=True,exist_ok=True)
            stamp=target.with_suffix(".audit-hash")
            provenance=target.with_suffix(".audit-result.json")
            # Elaboration emits external JSON; a cache hit cannot replay that IO.
            force = path.name == "ElaboratedCensus.lean" or (a.fresh_targets and str(path) in a.targets)
            if not force and target.exists() and stamp.exists() and provenance.exists() and stamp.read_text()==digest:
                original=json.loads(provenance.read_text())
                old_log=Path(original["log"])
                if (original["exit"]==0 and not original["resource_stop"] and
                    hashlib.sha256(target.read_bytes()).hexdigest()==original["olean_sha256"] and
                    old_log.exists() and hashlib.sha256(old_log.read_bytes()).hexdigest()==original["log_sha256"]):
                    record({"module":module,"cache_hit":True,"seconds":0,"original_check":original})
                    visited.add(key); hashes[key]=digest; return
            if available()<4*GIB: raise RuntimeError("Available reserve below 4GiB before "+module)
            log=out/(module+"."+digest[:12]+".log")
            cmd=[str(lean),"-j1","--tstack=131072","-o",str(target),str(path)]
            started=time.monotonic(); reason=None; peak=0
            with log.open("w") as stream:
                proc=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,
                    start_new_session=True,preexec_fn=limits)
                while proc.poll() is None:
                    try:
                        rss=next(l for l in Path(f"/proc/{proc.pid}/status").read_text().splitlines() if l.startswith("VmRSS:"))
                        peak=max(peak,int(rss.split()[1])*1024)
                    except (FileNotFoundError,StopIteration): pass
                    if available()<4*GIB: reason="available reserve below 4GiB"
                    if time.monotonic()-started>300: reason="300s module budget"
                    if reason:
                        os.killpg(proc.pid,signal.SIGTERM)
                        try: proc.wait(timeout=5)
                        except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); proc.wait()
                        break
                    time.sleep(0.2)
            row={"module":module,"command":cmd,"exit":proc.returncode,"seconds":round(time.monotonic()-started,3),
                "peak_rss_bytes":peak,"resource_stop":reason,"log":str(log),"source_transitive_sha256":digest}
            record(row)
            print(json.dumps(row),flush=True)
            if proc.returncode or reason: raise RuntimeError("Check failed: "+module)
            row["olean_sha256"]=hashlib.sha256(target.read_bytes()).hexdigest()
            row["log_sha256"]=hashlib.sha256(log.read_bytes()).hexdigest()
            provenance.write_text(json.dumps(row,indent=2)+"\n")
            stamp.write_text(digest); visited.add(key); hashes[key]=digest
        # Runtime prerequisite: every invocation checks/reuses the exact KeySort tree first.
        check(Path("Solidity/KeySort.lean"))
        for target in a.targets: check(Path(target))
        print("SERIAL_CHECK_PASS (supplemental only; no RUNTIME_GATE_PASS)",flush=True)

if __name__ == "__main__": main()
