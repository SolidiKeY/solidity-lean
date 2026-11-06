#!/usr/bin/env python3
"""Serial clean elaboration of the assigned modules and their local imports.
This measurement is not a replacement for the final repository run-lean.sh gate.
No shared/master cache is used. Source files and lean-toolchain are never changed.
"""
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

GIB=1024**3
LOCK=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")

def headroom():
    info=dict(line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())
    if int(info["SwapTotal"].split()[0]): raise RuntimeError("swap must be absent")
    avail=int(info["MemAvailable"].split()[0])*1024
    cg=Path("/sys/fs/cgroup")
    cap=(cg/"memory.max").read_text().strip()
    if cap != "max": avail=min(avail,int(cap)-int((cg/"memory.current").read_text()))
    if int((cg/"memory.swap.current").read_text()): raise RuntimeError("cgroup swap is in use")
    if avail < 4*GIB: raise RuntimeError("4 GiB available reserve breached")
    return avail

def group_rss(pgid):
    total=0
    for p in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields=p.read_text().rsplit(")",1)[1].split()
            if int(fields[2]) == pgid:
                total += int(fields[21])*os.sysconf("SC_PAGE_SIZE")
        except (OSError,ValueError,IndexError): pass
    return total

def group_vms(pgid):
    """Diagnostic summed VMS and largest sampled per-process VmPeak; not RAM."""
    total, largest_peak = 0, 0
    for p in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields=p.read_text().rsplit(")",1)[1].split()
            if int(fields[2]) != pgid: continue
            total += int(fields[20])
            for line in (p.parent/"status").read_text().splitlines():
                if line.startswith("VmPeak:"): largest_peak=max(largest_peak,int(line.split()[1])*1024)
        except (OSError,ValueError,IndexError): pass
    return total, largest_peak

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,required=True); ap.add_argument("--toolchain",type=Path,required=True)
    ap.add_argument("--census",type=Path,required=True); ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--keysort-only",action="store_true")
    ap.add_argument("--keep-going",action="store_true")
    a=ap.parse_args(); root=a.root.resolve(); tc=a.toolchain.resolve(); out=a.out.resolve()
    LOCK.parent.mkdir(parents=True,exist_ok=True)
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        subprocess.run(["git","status","--short","--branch"],cwd=root,check=True)
        census=json.loads(a.census.read_text())
        for p,h in census["closure_file_hashes"].items():
            if hashlib.sha256((root/p).read_bytes()).hexdigest()!=h: raise RuntimeError("tree differs from census: "+p)
        if out.exists(): raise RuntimeError("clean output directory must not exist: "+str(out))
        out.mkdir(parents=True); lib=out/"lib"; lib.mkdir(); logs=out/"logs"; logs.mkdir()
        env=os.environ.copy(); env.update(LEAN_NUM_THREADS="1",LEAN_PATH=str(lib),PATH=str(tc/"bin")+":"+env["PATH"])
        versions={n:subprocess.check_output([str(tc/"bin"/n),"--version"],text=True).strip() for n in ("lean","lake")}
        archive=tc.parent/(tc.name+".tar.zst")
        digest=hashlib.sha256()
        with archive.open("rb") as release:
            for block in iter(lambda:release.read(1024*1024),b""): digest.update(block)
            os.posix_fadvise(release.fileno(),0,0,os.POSIX_FADV_DONTNEED)
        archive_sha256=digest.hexdigest()
        if "version 4.35.0," in versions["lean"]:
            pin=json.loads(Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
            if archive_sha256!=pin["sha256"]: raise RuntimeError("target release archive differs from coordinator pin")
        report={"archive_sha256":archive_sha256,"cgroup_memory_max":Path("/sys/fs/cgroup/memory.max").read_text().strip(),"cpu_quota":Path("/sys/fs/cgroup/cpu.max").read_text().strip(),"cpuset":Path("/sys/fs/cgroup/cpuset.cpus.effective").read_text().strip(),"census_revision":census.get("revision",census["base"]),"effective_lean_path":str(lib),"schema":1,"base":census["base"],"versions":versions,"clean":True,"cache":"fresh private LEAN_PATH; no master cache", "lean_threads":1,"lean_heap_mib":10000,"sampled_rss_stop_bytes":12*GIB,"parent_rlimit_as":resource.getrlimit(resource.RLIMIT_AS),"reserve_bytes":4*GIB,"stack_kib":131072,"modules":[],"status":"running"}
        print(json.dumps(versions),flush=True); start=time.monotonic(); peak=0
        order=["Solidity.KeySort"] if a.keysort_only else census["serial_build_order"]
        failed=set()
        from census import imports
        try:
            for i,m in enumerate(order):
                deps=imports((root/(m.replace(".","/")+".lean")).read_text())
                blocked=sorted(set(deps)&failed)
                if blocked:
                    failed.add(m); report["modules"].append({"module":m,"status":"blocked","blocked_by":blocked}); continue
                headroom(); file=m.replace(".","/")+".lean"; artifact=lib/(m.replace(".","/")+".olean"); artifact.parent.mkdir(parents=True,exist_ok=True)
                cmd=[str(tc/"bin/lake"),"env","env","LEAN_PATH="+str(lib),str(tc/"bin/lean"),"--tstack=131072","-j1","-M10000","-o",str(artifact),file]
                then=time.monotonic(); rss=0; vms=0; vmpeak=0; proc=None; error=None
                try:
                    with (logs/(m+".log")).open("w") as log:
                        proc=subprocess.Popen(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
                        while proc.poll() is None:
                            rss=max(rss,group_rss(proc.pid)); mem=group_vms(proc.pid); vms=max(vms,mem[0]); vmpeak=max(vmpeak,mem[1])
                            if rss > 12*GIB: raise RuntimeError("12 GiB sampled group RSS threshold exceeded")
                            headroom(); time.sleep(0.05)
                except BaseException as exc:
                    error=type(exc).__name__+": "+str(exc)
                    if proc and proc.poll() is None:
                        os.killpg(proc.pid,signal.SIGTERM); proc.wait()
                    raise
                finally:
                    peak=max(peak,rss)
                    row={"module":m,"command":cmd,"exit":None if proc is None else proc.returncode,"wall_seconds":time.monotonic()-then,"sampled_peak_group_rss_bytes":rss,"monitor_error":error,"sampled_peak_group_vms_bytes":vms,"sampled_largest_process_vmpeak_bytes":vmpeak}
                    report["modules"].append(row)
                    print(f"{i+1}/{len(order)} {m} exit={row['exit']} wall={row['wall_seconds']:.3f}s rss={rss}",flush=True)
                if proc.returncode:
                    failed.add(m)
                    if not a.keep_going: raise RuntimeError("module failed: "+m)
                elif not artifact.is_file(): raise RuntimeError("missing olean: "+m)
            if failed: raise RuntimeError("failed or transitively blocked modules: "+str(len(failed)))
            report["status"]="pass"
        except BaseException as error:
            report["status"]="fail"; report["error"]=type(error).__name__+": "+str(error)
        finally:
            report["wall_seconds"]=time.monotonic()-start; report["sampled_peak_group_rss_bytes"]=peak
            report["child_maxrss_kib"]=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            (out/"result.json").write_text(json.dumps(report,indent=2)+"\n")
        if report["status"]!="pass": raise SystemExit(report.get("error","failed"))

if __name__=="__main__": main()
