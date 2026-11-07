#!/usr/bin/env python3
"""Serial pinned-toolchain import probe. Evidence only; not the final build gate.

No source edits, root generation, Lake cache, dependency patching or proof-budget
changes. Each module is built once; failed/missing imports block descendants.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

ROOT=Path(__file__).resolve().parents[4]
LIMIT=12*1024**3
RESERVE=4*1024**3

def imports(path):
    return [n for line in re.findall(r"(?m)^import\s+([^\n]+)",path.read_text()) for n in line.split()]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean",type=Path,required=True)
    p.add_argument("--evidence",type=Path,required=True)
    p.add_argument("--module",action="append",default=[])
    p.add_argument("--census",type=Path)
    args=p.parse_args()
    # Verify version here; official archive checksum is separately retained evidence.
    pin=json.loads(Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
    version=subprocess.check_output([str(args.lean),"--version"],text=True)
    if "version 4.35.0," not in version or pin["toolchain"]!="leanprover/lean4:v4.35.0":
        raise SystemExit("pinned toolchain/version mismatch")
    sysroot=args.lean.resolve().parent.parent
    requested=list(args.module)
    if args.census:
        for row in json.loads(args.census.read_text())["files"]:
            name=row["path"].removeprefix("Bridge/").removesuffix(".lean").replace("/", ".")
            requested.append(name)
    if not requested:raise SystemExit("at least one --module or --census required")
    args.evidence.mkdir(parents=True,exist_ok=True)
    out=args.evidence/"olean"; out.mkdir(exist_ok=True)
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    env=dict(os.environ,LEAN_NUM_THREADS="1",LEAN_PATH=str(out))
    statuses={}; results=[]; visiting=set()
    def locate(name):
        path=ROOT/(name.replace(".","/")+".lean")
        if path.is_file():return path
        for prefix in [ROOT/"Bridge", ROOT/"Bridge/vendor"]:
            path=prefix/(name.replace(".","/")+".lean")
            if path.is_file():return path
        return None
    def visit(name):
        if name in statuses:return statuses[name]
        if name in visiting:raise RuntimeError("import cycle: "+name)
        visiting.add(name)
        path=locate(name)
        row={"module":name,"path":str(path) if path else None}
        official=sysroot/"lib/lean"/(name.replace(".","/")+".olean")
        if path is None and official.is_file():
            row.update(status="pass",kind="official-sysroot-artifact",artifact=str(official))
        elif path is None:
            row.update(status="blocked",reason="unprovisioned-package-or-unresolved-source-on-pinned-toolchain")
        else:
            deps=imports(path)
            bad=[n for n in deps if not visit(n)]
            if bad:row.update(status="blocked",dependencies=bad)
            else:
                output=out/(name.replace(".","/")+".olean")
                output.parent.mkdir(parents=True,exist_ok=True)
                log=args.evidence/(name+".log")
                cmd=[str(args.lean),"-j1","--tstack=131072",str(path),"-o",str(output)]
                started=time.monotonic(); killed=None; peak=0
                def bounds():resource.setrlimit(resource.RLIMIT_AS,(LIMIT,LIMIT))
                cgroup=int(Path("/sys/fs/cgroup/memory.max").read_text())
                current=int(Path("/sys/fs/cgroup/memory.current").read_text())
                if current>cgroup-RESERVE:raise SystemExit("insufficient cgroup reserve before spawn")
                if len(Path("/proc/swaps").read_text().splitlines())>1:raise SystemExit("swap enabled; refusing heavy probe")
                with log.open("w") as stream:
                    proc=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=bounds)
                    while proc.poll() is None:
                        # cgroup-wide reserve protects the VM; RSS is measured. Kill only our process group.
                        cgroup=int(Path("/sys/fs/cgroup/memory.max").read_text())
                        current=int(Path("/sys/fs/cgroup/memory.current").read_text())
                        try:
                            stat=Path(f"/proc/{proc.pid}/status").read_text()
                            rss=int(re.search(r"VmRSS:\s+(\d+)",stat)[1])*1024
                            peak=max(peak,rss)
                        except (FileNotFoundError,TypeError):pass
                        if current>cgroup-RESERVE:killed="reserve-breach"
                        if time.monotonic()-started>300:killed="module-time-budget"
                        if killed:os.killpg(proc.pid,signal.SIGTERM);break
                        time.sleep(.1)
                    try:rc=proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid,signal.SIGKILL);rc=proc.wait(timeout=10)
                row.update(status="pass" if rc==0 and not killed else "fail",exit=rc,
                           command=cmd,elapsed_seconds=round(time.monotonic()-started,3),
                           peak_rss_bytes=peak,log=str(log),stop_reason=killed,
                           source_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                print(name,row["status"],flush=True)
        results.append(row);statuses[name]=row["status"]=="pass";visiting.remove(name)
        (args.evidence/"results.json").write_text(json.dumps(dict(version=version,binary_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),requested=requested,results=results),indent=2)+"\n")
        return statuses[name]
    success=all([visit(n) for n in requested])
    raise SystemExit(0 if success else 1)

if __name__=="__main__":main()
