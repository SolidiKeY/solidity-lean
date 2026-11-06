#!/usr/bin/env python3
"""Sample aggregate owned-group RSS; VM has a hard cgroup cap. No swap allowed.

The 0.5s guard is sampled, not a hard per-job memory limit. Never reports a
resource stop as success. Process-group members may not detach themselves.
"""
import argparse,json,os,pathlib,signal,subprocess,time
RESERVE=4*1024**3
CAP=12*1024**3

def cgroup_headroom(current, limit, stats):
    # Estimate only clean inactive cache; exclude active cache and reclaimable slab.
    reclaimable=min(current,max(0,stats.get("inactive_file",0)-stats.get("file_dirty",0)-stats.get("file_writeback",0)))
    return min(limit,max(0,limit-current+reclaimable)),reclaimable

def resource_snapshot(rss):
    mem={r.split()[0].rstrip(":"):int(r.split()[1])*1024 for r in pathlib.Path("/proc/meminfo").read_text().splitlines() if r.split()[0] in ("MemAvailable:","SwapTotal:")}
    current=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
    limit_text=pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip()
    if limit_text=="max":raise RuntimeError("finite VM hard memory cap required")
    limit=int(limit_text)
    stats={r.split()[0]:int(r.split()[1]) for r in pathlib.Path("/sys/fs/cgroup/memory.stat").read_text().splitlines()}
    available,reclaimable=cgroup_headroom(current,limit,stats)
    swap_current=int(pathlib.Path("/sys/fs/cgroup/memory.swap.current").read_text())
    snapshot={"group_rss_bytes":rss,"host_available_bytes":mem["MemAvailable"],"host_swap_total_bytes":mem["SwapTotal"],"vm_cap_bytes":limit,"cgroup_current_bytes":current,"raw_cgroup_headroom_bytes":limit-current,"estimated_cgroup_headroom_bytes":available,"clean_inactive_file_bytes":reclaimable,"cgroup_swap_current_bytes":swap_current}
    violations=[]
    if rss>CAP:violations.append("group_rss_cap")
    if mem["MemAvailable"]<RESERVE:violations.append("host_available_reserve")
    if available<RESERVE:violations.append("estimated_cgroup_available_reserve")
    if mem["SwapTotal"]!=0 or swap_current!=0:violations.append("swap_present")
    return snapshot,violations

def kill_group(pgid):
    try:os.killpg(pgid,signal.SIGKILL)
    except ProcessLookupError:pass

def main():
    p=argparse.ArgumentParser();p.add_argument("--output",type=pathlib.Path,required=True);p.add_argument("command",nargs=argparse.REMAINDER);a=p.parse_args()
    cmd=a.command[1:] if a.command[:1]==["--"] else a.command
    if not cmd:p.error("missing command")
    start=time.monotonic();peak=0;reason=None;proc=None;code=125;last={};violations=[]
    try:
        last,violations=resource_snapshot(0)
        if violations:reason="RESOURCE_PREFLIGHT_STOP"
        else:
            with a.output.with_suffix(".log").open("w") as log:
                proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
                while True:
                    rows=subprocess.check_output(["ps","-eo","pid=,pgid=,rss=,stat="],text=True).splitlines()
                    rss=sum(int(row.split()[2])*1024 for row in rows if int(row.split()[1])==proc.pid);peak=max(peak,rss)
                    last,violations=resource_snapshot(rss)
                    if violations:reason="RESOURCE_STOP";break
                    if proc.poll() is not None:
                        rows=subprocess.check_output(["ps","-eo","pid=,pgid=,rss=,stat="],text=True).splitlines()
                        if any(int(row.split()[1])==proc.pid and int(row.split()[0])!=proc.pid and not row.split()[3].startswith("Z") for row in rows):reason="ORPHAN_GROUP_STOP"
                        break
                    time.sleep(0.5)
                if reason:kill_group(proc.pid)
                code=proc.wait()
    except BaseException as exc:
        reason="MONITOR_ERROR:"+type(exc).__name__
        raise
    finally:
        # Also terminate descendants after an apparently successful leader exit.
        if proc is not None:kill_group(proc.pid);proc.wait()
        result={"command":cmd,"exit":code,"wall_seconds":time.monotonic()-start,"peak_group_rss_bytes":peak,"sample_seconds":0.5,"cap_bytes":CAP,"reserve_bytes":RESERVE,"stop":reason,"no_swap_required":True,"resource_snapshot":last,"resource_violations":violations,"boundary":"sampled RSS and estimated clean-inactive cgroup headroom; existing hard VM cap; no detached children"}
        a.output.write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result))
    return code if code else (1 if reason else 0)
if __name__=="__main__":raise SystemExit(main())
