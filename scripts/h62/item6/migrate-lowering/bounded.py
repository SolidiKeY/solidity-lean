#!/usr/bin/env python3
"""Foreground commands only; sampled headroom/RSS evidence and owned-group cleanup."""
import argparse, fcntl, json, os, signal, subprocess, time
from datetime import datetime, timezone
from pathlib import Path
from process_group import members, stop_owned

p=argparse.ArgumentParser()
p.add_argument("--output",type=Path,required=True)
p.add_argument("--lock-fd",type=int)
p.add_argument("command",nargs=argparse.REMAINDER)
a=p.parse_args(); cmd=a.command[1:] if a.command[:1]==["--"] else a.command
if not cmd: p.error("command required")
lock=os.fdopen(a.lock_fd,"a",closefd=False) if a.lock_fd is not None else open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
print(subprocess.check_output(["git","status","--short"],text=True),flush=True)
cg=Path("/sys/fs/cgroup"); cap=int((cg/"memory.max").read_text()); reserve=4*1024**3
if cap<reserve+1024**3: raise SystemExit("insufficient cgroup capacity")
if len(Path("/proc/swaps").read_text().splitlines())>1: raise SystemExit("configured host swap")
if int((cg/"memory.swap.current").read_text()): raise SystemExit("active cgroup swap")
if int((cg/"memory.current").read_text())>cap-reserve: raise SystemExit("insufficient cgroup headroom")
def atomic_json(path,value):
    tmp=path.with_suffix(path.suffix+".tmp")
    tmp.write_text(json.dumps(value,indent=2)+"\n"); tmp.replace(path)
def interrupted(signum,frame): raise InterruptedError(f"runner signal {signum}")
for sig in (signal.SIGTERM,signal.SIGINT): signal.signal(sig,interrupted)
start=time.monotonic(); peak=0; reason=None; last_heartbeat=0
started_utc=datetime.now(timezone.utc).isoformat(); live=a.output.with_suffix(".live.json")
env=dict(os.environ,LEAN_NUM_THREADS="1"); log=a.output.with_suffix(".log")
with log.open("w") as out:
    child=None
    try:
        child=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,start_new_session=True)
        while child.poll() is None:
            peak=max(peak,sum(rss for _,rss in members(child.pid)))
            if time.monotonic()-last_heartbeat>=5:
                atomic_json(live,{"status":"running","runner_pid":os.getpid(),"process_group":child.pid,"command":cmd,"started_utc":started_utc,"heartbeat_utc":datetime.now(timezone.utc).isoformat(),"wall_seconds":time.monotonic()-start,"sampled_peak_group_rss_bytes":peak})
                last_heartbeat=time.monotonic()
            available=int(next(x.split()[1] for x in Path("/proc/meminfo").read_text().splitlines() if x.startswith("MemAvailable:")))*1024
            if available<reserve: reason="4GiB host reserve"
            if int((cg/"memory.current").read_text())>cap-reserve: reason="4GiB cgroup reserve"
            if int((cg/"memory.swap.current").read_text()): reason="swap detected"
            if reason: break
            time.sleep(0.25)
    except BaseException as exc:
        reason=f"runner interrupted: {type(exc).__name__}: {exc}"
    finally:
        for sig in (signal.SIGTERM,signal.SIGINT): signal.signal(sig,signal.SIG_IGN)
        if child is not None and members(child.pid):
            if reason is None: reason="foreground descendants survived leader"
            stop_owned(child.pid,Path.cwd())
        if child is not None: child.wait(timeout=10)
rc=125 if reason or child is None else child.returncode
result={"started_utc":started_utc,"finished_utc":datetime.now(timezone.utc).isoformat(),"runner_pid":os.getpid(),"process_group":child.pid if child is not None else None,"command":cmd,"cwd":os.getcwd(),"exit":rc,"stop_reason":reason,"wall_seconds":time.monotonic()-start,"sampled_peak_group_rss_bytes":peak,"sample_interval_seconds":0.25,"cgroup_cap_bytes":cap,"reserve_bytes":reserve,"LEAN_NUM_THREADS":1,"log":str(log)}
atomic_json(a.output,result); atomic_json(live,dict(result,status="finished"))
print(json.dumps(result),flush=True)
raise SystemExit(rc)
