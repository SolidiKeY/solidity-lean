#!/usr/bin/env python3
"""Run one audit job with a process-group budget, headroom guard, and evidence."""
import argparse, json, os, pathlib, resource, signal, subprocess, time
GIB=1024**3

def available():
    mem={line.split()[0].rstrip(":"):int(line.split()[1])*1024 for line in pathlib.Path("/proc/meminfo").read_text().splitlines() if len(line.split())>=3 and line.split()[2]=="kB"}
    cg=pathlib.Path("/sys/fs/cgroup"); cap=(cg/"memory.max").read_text().strip()
    free=mem["MemAvailable"]
    if cap!="max": free=min(free,int(cap)-int((cg/"memory.current").read_text()))
    if mem["SwapTotal"]: raise RuntimeError("swap is enabled")
    return free

def group_info(group):
    total=0; lean=[]
    for p in pathlib.Path("/proc").iterdir():
        if not p.name.isdigit(): continue
        try:
            stat=(p/"stat").read_text().rsplit(")",1)[1].split()
            if int(stat[2])!=group: continue
            total+=max(0,int(stat[21]))*os.sysconf("SC_PAGE_SIZE")
            args=(p/"cmdline").read_bytes().decode(errors="replace").strip("\0").split("\0")
            if pathlib.Path(args[0]).name=="lean": lean.append((int(p.name),args))
        except (FileNotFoundError,ProcessLookupError,PermissionError,IndexError): continue
    return total,lean

def run(a):
    reserve=4*GIB; free=available(); budget=min(12*GIB,free-reserve-512*1024**2)
    if budget<=0: raise SystemExit("RESOURCE_BLOCK: insufficient headroom")
    def bounds(): resource.setrlimit(resource.RLIMIT_AS,(budget,budget))
    env=dict(os.environ,LEAN_NUM_THREADS="1"); start=time.monotonic(); seen={}; peak=0; minimum=free; reason=None
    with open(a.output+".log","w") as log:
        proc=subprocess.Popen(a.command,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=bounds)
        try:
            while proc.poll() is None:
                rss,leans=group_info(proc.pid); peak=max(peak,rss)
                for pid,args in leans: seen[pid]=args
                try: minimum=min(minimum,available())
                except RuntimeError as e: reason=str(e)
                if time.monotonic()-start>a.seconds: reason="timeout"
                elif rss>budget: reason="aggregate RSS budget exceeded"
                elif minimum<reserve: reason="four GiB reserve crossed"
                elif len(leans)>1: reason="concurrent Lean processes"
                elif any("-j1" not in args for _,args in leans): reason="Lean process without explicit -j1"
                if reason: break
                time.sleep(0.1)
        finally:
            # Only this job owns the new process group; reap/stop all descendants.
            try: os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            code=proc.wait()
    if reason: code=124 if reason=="timeout" else 125
    usage=resource.getrusage(resource.RUSAGE_CHILDREN)
    record=dict(command=a.command,exit=code,elapsed_seconds=time.monotonic()-start,peak_sampled_group_rss_bytes=peak,largest_waited_child_maxrss_kib=usage.ru_maxrss,minimum_available_bytes=minimum,available_before=free,address_space_limit_per_process=budget,aggregate_rss_budget_bytes=budget,reserve_bytes=reserve,stop_reason=reason,lean_processes_observed=len(seen),explicit_j1_observed=all("-j1" in x for x in seen.values()),sample_interval_seconds=0.1,lean_num_threads="1")
    pathlib.Path(a.output+".json").write_text(json.dumps(record,indent=2)+"\n"); print(json.dumps(record)); return code

def main():
    p=argparse.ArgumentParser(); p.add_argument("--seconds",type=int,default=300); p.add_argument("--output",required=True); p.add_argument("command",nargs=argparse.REMAINDER); a=p.parse_args()
    if a.command[:1]==["--"]: a.command=a.command[1:]
    if not a.command:p.error("missing command")
    raise SystemExit(run(a))
if __name__=="__main__":main()
