#!/usr/bin/env python3
"""Measure one serial process group with fail-closed RSS/headroom/swap guards.

The VM cgroup supplies the hard aggregate cap. RLIMIT_AS additionally bounds
individual processes. Polling guards are supplementary, not a cgroup claim.
"""
import argparse, json, os, pathlib, resource, signal, subprocess, time
GIB=1024**3

def sample(pgid):
    rss=0; leans=0
    for p in pathlib.Path("/proc").glob("[0-9]*"):
        try:
            stat=(p/"stat").read_text(); fields=stat[stat.rfind(")")+2:].split()
            if int(fields[2])!=pgid: continue
            status=(p/"status").read_text().splitlines()
            rss+=sum(int(s.split()[1])*1024 for s in status if s.startswith("VmRSS:"))
            if (p/"comm").read_text().strip()=="lean": leans+=1
        except (OSError,ValueError,IndexError): pass
    mem={s.split(":")[0]:int(s.split()[1])*1024 for s in pathlib.Path("/proc/meminfo").read_text().splitlines()}
    cap=pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip()
    current=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
    available=min(mem["MemAvailable"],int(cap)-current) if cap!="max" else mem["MemAvailable"]
    return rss,leans,available,mem["SwapTotal"]-mem["SwapFree"]

def main():
    p=argparse.ArgumentParser();p.add_argument("--output",required=True);p.add_argument("--cwd",required=True)
    p.add_argument("--timeout",type=float,default=7200);p.add_argument("command",nargs=argparse.REMAINDER);a=p.parse_args()
    command=a.command[1:] if a.command[:1]==["--"] else a.command
    output=pathlib.Path(a.output); output.mkdir(parents=True,exist_ok=False)
    def limits(): resource.setrlimit(resource.RLIMIT_AS,(12*GIB,12*GIB))
    # Refuse to start without sufficient headroom or on an actively swapping VM.
    _,_,available,swap=sample(os.getpgrp())
    if available<4*GIB or swap: raise SystemExit("resource prerequisite failed")
    env=dict(os.environ,LEAN_NUM_THREADS="1")
    start=time.monotonic(); peak=0; max_leans=0; reason=None
    with (output/"output.log").open("wb") as log:
        proc=subprocess.Popen(command,cwd=a.cwd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
        while proc.poll() is None:
            rss,leans,available,swap=sample(proc.pid);peak=max(peak,rss);max_leans=max(max_leans,leans)
            if rss>11*GIB: reason="aggregate RSS exceeds 11 GiB guard"
            elif available<4*GIB:reason="available memory below 4 GiB"
            elif swap:reason="swap in use"
            elif leans>1:reason="multiple Lean jobs"
            elif time.monotonic()-start>a.timeout:reason="timeout"
            if reason:
                os.killpg(proc.pid,signal.SIGKILL);break
            time.sleep(.05)
        code=proc.wait()
    result={"command":command,"cwd":a.cwd,"exit":code,"wall_seconds":time.monotonic()-start,
        "sampled_peak_group_rss_bytes":peak,"wait_rusage_max_single_process_rss_kib":resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,"max_concurrent_lean_processes":max_leans,"guard_stop":reason,
        "LEAN_NUM_THREADS":"1","per_process_address_space_cap_bytes":12*GIB,
        "aggregate_rss_guard_bytes":11*GIB,"reserve_bytes":4*GIB,"sample_interval_seconds":.05,
        "swap_total_bytes":int(next(s.split()[1] for s in pathlib.Path("/proc/meminfo").read_text().splitlines() if s.startswith("SwapTotal:")))*1024,
        "headroom_basis":"min(host MemAvailable, finite cgroup memory.max - memory.current)",
        "cgroup_memory_max":pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip(),
        "cgroup_swap_max":pathlib.Path("/sys/fs/cgroup/memory.swap.max").read_text().strip()}
    (output/"result.json").write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result))
    raise SystemExit(0 if code==0 and reason is None else 1)
if __name__=="__main__":main()
