#!/usr/bin/env python3
"""Clean serial Syntax closure probe. Not a substitute for run-lean.sh."""
import argparse, fcntl, hashlib, json, os, signal, subprocess, time
from pathlib import Path
from census import inventory, imports
GIB=1024**3

def available():
    vals=dict(line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())
    host=int(vals["MemAvailable"].split()[0])*1024
    cg=Path("/sys/fs/cgroup")
    cap=(cg/"memory.max").read_text().strip()
    return min(host, int(cap)-int((cg/"memory.current").read_text())) if cap != "max" else host

def run(args):
    root=args.source_root.resolve(); out=args.output.resolve()
    if out.exists(): raise SystemExit("Refusing non-clean output directory")
    if len(Path("/proc/swaps").read_text().splitlines()) != 1: raise SystemExit("Swap present")
    if available()<4*GIB: raise SystemExit("4 GiB reserve unavailable")
    out.mkdir(parents=True)
    inv=inventory(root); (out/"census.json").write_text(json.dumps(inv,indent=2)+"\n")
    bins=args.toolchain.resolve()/"bin"; env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(out/"lib"), PATH=str(bins)+":"+os.environ["PATH"])
    cpu=min(os.sched_getaffinity(0)); os.sched_setaffinity(0,{cpu})
    result=dict(source_root=str(root), runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), command=[str(bins/"lean"), "-j1", "-M11000", "--tstack=131072", "-o", "<clean-lib/module.olean>", "<module.lean>"],
        lean=subprocess.check_output([str(bins/"lean"),"--version"],env=env,text=True).strip(),
        lake=subprocess.check_output([str(bins/"lake"),"--version"],env=env,text=True).strip(),
        cpu=cpu, threads=1, timeout_seconds=args.timeout, lean_memory_mib=11000, reserve_gib=4, swap="none", cache="empty private output, no Lake artifact cache", modules=[])
    owned={r["module"] for r in inv["files"]}; failed=set(); start=time.monotonic()
    for mod in inv["build_order"]:
        source=root/(mod.replace(".","/")+".lean")
        deps=imports(source.read_text())
        row=dict(module=mod, owned=mod in owned, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
        if any(dep in failed for dep in deps):
            row.update(status="blocked",dependencies=[dep for dep in deps if dep in failed]); failed.add(mod)
        else:
            dest=out/"lib"/(mod.replace(".","/")+".olean"); dest.parent.mkdir(parents=True,exist_ok=True)
            cmd=[str(bins/"lean"),"-j1","-M11000","--tstack=131072","-o",str(dest),str(source.relative_to(root))]
            row["command"]=cmd; t=time.monotonic(); reason=None
            log=out/(mod+".log"); stats=out/(mod+".time")
            with log.open("w") as f:
                proc=subprocess.Popen(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
                while True:
                    pid, status, usage=os.wait4(proc.pid, os.WNOHANG)
                    if pid:
                        proc.returncode=os.waitstatus_to_exitcode(status); break
                    if available()<4*GIB: reason="reserve-stop"
                    if args.timeout > 0 and time.monotonic()-t>args.timeout: reason="module-time-stop"
                    if reason:
                        os.killpg(proc.pid,signal.SIGTERM)
                        deadline=time.monotonic()+2
                        while True:
                            pid,status,usage=os.wait4(proc.pid,os.WNOHANG)
                            if pid: break
                            if time.monotonic()>deadline:
                                os.killpg(proc.pid,signal.SIGKILL)
                                _,status,usage=os.wait4(proc.pid,0); break
                            time.sleep(.1)
                        proc.returncode=os.waitstatus_to_exitcode(status); break
                    time.sleep(.2)
                row["exit"]=proc.returncode
                row["max_rss_kib"]=usage.ru_maxrss
                stats.write_text(json.dumps(dict(max_rss_kib=usage.ru_maxrss,user_seconds=usage.ru_utime,system_seconds=usage.ru_stime))+"\n")
            row.update(status=reason or ("pass" if row["exit"]==0 else "fail"), wall_seconds=round(time.monotonic()-t,3),log=str(log), time=str(stats))
            if row["status"]!="pass": failed.add(mod)
            print(mod,row["status"],row["wall_seconds"],flush=True)
        result["modules"].append(row)
        result["wall_seconds"]=round(time.monotonic()-start,3)
        result["expected_modules"]=len(inv["build_order"])
        result["completed_modules"]=len(result["modules"])
        result["status"]="running"
        (out/"result.tmp").write_text(json.dumps(result,indent=2)+"\n")
        (out/"result.tmp").replace(out/"result.json")
        if row["status"] in ("reserve-stop","module-time-stop"): break
    result["status"]="fail" if failed else ("pass" if result["completed_modules"]==result["expected_modules"] else "incomplete")
    (out/"result.tmp").write_text(json.dumps(result,indent=2)+"\n")
    (out/"result.tmp").replace(out/"result.json")
    return 0 if result["status"]=="pass" else 1

if __name__=="__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--source-root",type=Path,default=Path.cwd()); ap.add_argument("--toolchain",required=True,type=Path); ap.add_argument("--output",required=True,type=Path); ap.add_argument("--timeout",default=0,type=int); a=ap.parse_args()
    with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","w") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        changed=subprocess.check_output(["git","diff","--name-only","c6f550e281a7e5affa9a99bc2cdaed556dec00e4","--","Solidity"],text=True).splitlines()
        allowed={r["path"] for r in inventory(Path.cwd())["files"]}
        if not set(changed)<=allowed: raise SystemExit("Outside-scope production edit")
        raise SystemExit(run(a))
