#!/usr/bin/env python3
"""Foreground Lean/build commands only; sampled headroom and RSS evidence. No detaching."""
import argparse, fcntl, json, os, signal, subprocess, time
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument("--output",type=Path,required=True); p.add_argument("--lock-fd",type=int); p.add_argument("command",nargs=argparse.REMAINDER); a=p.parse_args()
cmd=a.command; cmd=cmd[1:] if cmd[:1]==["--"] else cmd
if not cmd: p.error("command required")
lock=os.fdopen(a.lock_fd,"a",closefd=False) if a.lock_fd is not None else open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
print(subprocess.check_output(["git","status","--short"],text=True),flush=True)
cg=Path("/sys/fs/cgroup"); cap=int((cg/"memory.max").read_text()); reserve=4*1024**3
if cap<reserve+1024**3: raise SystemExit("insufficient cgroup capacity")
if len(Path("/proc/swaps").read_text().splitlines())>1: raise SystemExit("active host swap configuration")
if int((cg/"memory.swap.current").read_text()): raise SystemExit("active cgroup swap")
if int((cg/"memory.current").read_text())>cap-reserve: raise SystemExit("insufficient cgroup headroom")
start=time.monotonic(); peak=0; reason=None
env=dict(os.environ,LEAN_NUM_THREADS="1")
log=a.output.with_suffix(".log")
with log.open("w") as out:
    child=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env,start_new_session=True)
    while child.poll() is None:
        rss=0
        for proc in Path("/proc").glob("[0-9]*"):
            try:
                stat=(proc/"stat").read_text().rsplit(")",1)[1].split()
                if int(stat[2])==child.pid: rss+=int(stat[21])*os.sysconf("SC_PAGE_SIZE")
            except (OSError,ValueError,IndexError): pass
        peak=max(peak,rss)
        available=int(next(x.split()[1] for x in Path("/proc/meminfo").read_text().splitlines() if x.startswith("MemAvailable:")))*1024
        if available<reserve: reason="4GiB host reserve"
        if int((cg/"memory.current").read_text())>cap-reserve: reason="4GiB cgroup reserve"
        if int((cg/"memory.swap.current").read_text()): reason="swap detected"
        if reason:
            os.killpg(child.pid,signal.SIGTERM)
            try: child.wait(timeout=10)
            except subprocess.TimeoutExpired: os.killpg(child.pid,signal.SIGKILL)
            break
        time.sleep(0.25)
    rc=child.wait()
result={"command":cmd,"cwd":os.getcwd(),"exit":rc,"stop_reason":reason,"wall_seconds":time.monotonic()-start,"sampled_peak_group_rss_bytes":peak,"sample_interval_seconds":0.25,"cgroup_cap_bytes":cap,"reserve_bytes":reserve,"LEAN_NUM_THREADS":1,"log":str(log)}
a.output.write_text(json.dumps(result,indent=2)+"\n"); print(json.dumps(result),flush=True)
raise SystemExit(125 if reason else rc)
