#!/usr/bin/env python3
"""Serial cold closure build. Private outputs/config/cache; no tracked toolchain edit.
Run under the repository writer lock. Not a replacement for run-lean.sh final gate.
"""
import argparse, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
from census import scan
GiB=1024**3

def bounded(cmd, env, log):
    cg=Path("/sys/fs/cgroup")
    if (cg/"memory.max").read_text().strip()!=str(12*GiB) or (cg/"memory.swap.max").read_text().strip()!="0":
        raise RuntimeError("RESOURCE_REQUIRES_HARD_12G_NO_SWAP_CGROUP")
    if resource.getrlimit(resource.RLIMIT_AS)!=(-1,-1): raise RuntimeError("RESOURCE_VIRTUAL_ADDRESS_LIMIT_PRESENT")
    for key,var in (("memory.max","H62_PARENT_MEMORY_MAX"),("cpu.max","H62_PARENT_CPU_MAX"),("memory.swap.max","H62_PARENT_SWAP_MAX")):
        if Path("/h62-parent-cgroup",key).read_text().strip()!=os.environ.get(var):
            raise RuntimeError("RESOURCE_PARENT_MOUNT_MISMATCH: "+key)
    start=time.monotonic(); peak=0; reason=None
    with log.open("w") as out:
        p=subprocess.Popen(cmd,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            rss=0
            for d in Path("/proc").iterdir():
                if not d.name.isdigit(): continue
                try:
                    stat=(d/"stat").read_text().rsplit(")",1)[1].split()
                    if int(stat[2])==p.pid: rss+=int(stat[21])*os.sysconf("SC_PAGE_SIZE")
                except (OSError,ValueError,IndexError): pass
            peak=max(peak,rss)
            mem={k:int(v.split()[0])*1024 for k,v in (l.split(":",1) for l in Path("/proc/meminfo").read_text().splitlines())}
            cg=Path("/h62-parent-cgroup")
            stats=dict(line.split() for line in (cg/"memory.stat").read_text().splitlines())
            remaining=int((cg/"memory.max").read_text())-int((cg/"memory.current").read_text())+int(stats.get("inactive_file","0"))
            if rss>12*GiB or min(mem["MemAvailable"],remaining)<4*GiB: reason="RESOURCE_RESERVE_STOP"
            if time.monotonic()-start>3600: reason="MODULE_TIMEOUT_STOP"
            if reason:
                os.killpg(p.pid,signal.SIGTERM)
                try: p.wait(timeout=5)
                except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL)
                break
            time.sleep(.2)
        p.wait()
    return {"command":cmd,"exit":p.returncode,"wall_s":time.monotonic()-start,"sampled_aggregate_peak_rss_bytes":peak,"stop":reason,"log":str(log)}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--toolchain",required=True,type=Path); ap.add_argument("--out",required=True,type=Path); ap.add_argument("--only",default=""); a=ap.parse_args()
    root=Path.cwd(); out=a.out.resolve(); out.mkdir(parents=True,exist_ok=False)
    if Path("/proc/swaps").read_text().splitlines()[1:]: raise RuntimeError("RESOURCE_SWAP_ENABLED")
    census=scan(root); (out/"census.json").write_text(json.dumps(census,sort_keys=True,indent=2))
    env=os.environ.copy()
    for key in ("LEAN_PATH","LEAN_SRC_PATH","LAKE_HOME","LEAN_SYSROOT"): env.pop(key,None)
    env.update(PATH=str(a.toolchain.resolve()/"bin")+":"+env["PATH"],LEAN_NUM_THREADS="1",XDG_CACHE_HOME=str(out/"cache"))
    config=(root/"lakefile.toml").read_text().replace('enableArtifactCache = true','enableArtifactCache = false').replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
    config=config.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = '+json.dumps(str(out/"build")))
    cfg=out/"lakefile.toml"; cfg.write_text(config)
    records=[]; summary={"config_sha256":hashlib.sha256(config.encode()).hexdigest(),"settings":{"hard_job_memory_limit_bytes":12*GiB,"hard_job_swap_limit_bytes":0,"aggregate_rss_stop_threshold_bytes":12*GiB,"reserve_enforcement":"sampled min(MemAvailable,parent cap-current+inactive_file); hard job cgroup cap","reserve_bytes":4*GiB,"threads":1,"swap":False,"clean_private_outputs":True,"artifact_cache":False},"head":subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),"versions":{},"results":records,"status":"running"}
    for tool in ("lean","lake"): summary["versions"][tool]=subprocess.check_output([str(a.toolchain.resolve()/"bin"/tool),"--version"],env=env,text=True).strip()
    order=["Solidity.KeySort"]+[m for m in census["build_order"] if m!="Solidity.KeySort"]
    if a.only:
        if a.only!="Solidity.KeySort": raise RuntimeError("SUBSET_REQUIRES_SERIAL_CLOSURE: only KeySort supported")
        order=[a.only]
    summary.update(runtime_image=os.environ.get("H62_RUNTIME_IMAGE"),requested_modules=order,full_assigned_build=not bool(a.only),source_hashes=census["closure_sha256"],resources={k:Path("/sys/fs/cgroup",k).read_text().strip() for k in ("cpu.max","cpuset.cpus.effective","memory.max","memory.swap.max")},parent_resources={k:Path("/h62-parent-cgroup",k).read_text().strip() for k in ("cpu.max","memory.max","memory.swap.max")},cpu_affinity=sorted(os.sched_getaffinity(0)))
    start=time.monotonic()
    for i,m in enumerate(order):
        print(f"{i+1}/{len(order)} {m}",flush=True)
        r=bounded([str(a.toolchain.resolve()/"bin/lake"),"-f",str(cfg),"--no-cache","build",m+":olean"],env,out/(m+".log")); r["module"]=m; records.append(r)
        summary["wall_s"]=time.monotonic()-start; summary["status"]="fail" if r["exit"] or r["stop"] else "running"
        (out/"summary.json").write_text(json.dumps(summary,indent=2))
        if summary["status"]=="fail": return 1
    summary["status"]="pass"; (out/"summary.json").write_text(json.dumps(summary,indent=2)); return 0
if __name__=="__main__": raise SystemExit(main())
