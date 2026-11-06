#!/usr/bin/env python3
"""Sample aggregate owned-group RSS; VM has a hard cgroup cap. No swap allowed.

The 0.5s guard is sampled, not a hard per-job memory limit. Never reports a
resource stop as success. Process-group members may not detach themselves.
"""
import argparse,json,os,pathlib,signal,subprocess,time
RESERVE=4*1024**3
CAP=12*1024**3

def resource_ok(rss):
    mem={r.split()[0].rstrip(":"):int(r.split()[1])*1024 for r in pathlib.Path("/proc/meminfo").read_text().splitlines() if r.split()[0] in ("MemAvailable:","SwapTotal:")}
    current=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
    limit=pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip()
    return rss<=CAP and mem["MemAvailable"]>=RESERVE and (limit!="max" and int(limit)-current>=RESERVE) and mem["SwapTotal"]==0

def kill_group(pgid):
    try:os.killpg(pgid,signal.SIGKILL)
    except ProcessLookupError:pass

def main():
    p=argparse.ArgumentParser();p.add_argument("--output",type=pathlib.Path,required=True);p.add_argument("command",nargs=argparse.REMAINDER);a=p.parse_args()
    cmd=a.command[1:] if a.command[:1]==["--"] else a.command
    if not cmd:p.error("missing command")
    start=time.monotonic();peak=0;reason=None;proc=None;code=125
    try:
        if not resource_ok(0):reason="RESOURCE_PREFLIGHT_STOP"
        else:
            with a.output.with_suffix(".log").open("w") as log:
                proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
                while True:
                    rows=subprocess.check_output(["ps","-eo","pid=,pgid=,rss=,stat="],text=True).splitlines()
                    rss=sum(int(row.split()[2])*1024 for row in rows if int(row.split()[1])==proc.pid);peak=max(peak,rss)
                    if not resource_ok(rss):reason="RESOURCE_STOP";break
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
        result={"command":cmd,"exit":code,"wall_seconds":time.monotonic()-start,"peak_group_rss_bytes":peak,"sample_seconds":0.5,"cap_bytes":CAP,"reserve_bytes":RESERVE,"stop":reason,"no_swap_required":True,"boundary":"sampled guard under existing VM hard cgroup cap; no detached children permitted"}
        a.output.write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result))
    return code if code else (1 if reason else 0)
if __name__=="__main__":raise SystemExit(main())
