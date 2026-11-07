#!/usr/bin/env python3
"""One serial child process group; sampled RSS stop 12GiB, reserve 4GiB, no swap.
Run with repository writer.lock held. Logs/metrics must remain outside git.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time

p=argparse.ArgumentParser()
p.add_argument("--log",type=Path,required=True)
p.add_argument("--timeout",type=int,default=300)
p.add_argument("command",nargs=argparse.REMAINDER)
a=p.parse_args()
cmd=a.command
if cmd and cmd[0]=="--": cmd=cmd[1:]
if not cmd: p.error("command required")
if a.timeout <= 0: p.error("timeout must be positive")
root=Path(__file__).resolve().parents[4]
if a.log.resolve().is_relative_to(root): p.error("log must be off git")

def memory():
    d={}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key,value,*_=line.split(); d[key.rstrip(":")]=int(value)*1024
    return d

def group_rss(pgid):
    total=0
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit(): continue
        try:
            s=(proc/"stat").read_text().rsplit(")",1)[1].split()
            if int(s[2])==pgid: total+=int(s[21])*os.sysconf("SC_PAGE_SIZE")
        except (OSError,ValueError,IndexError): pass
    return total

if memory()["SwapTotal"]: raise SystemExit("REFUSE: host swap configured")
if memory()["MemAvailable"]<4*1024**3: raise SystemExit("REFUSE: reserve unavailable")
env=dict(os.environ,LEAN_NUM_THREADS="1")
started=time.monotonic(); peak=0; reason=None
with a.log.open("w") as log:
    child=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    while child.poll() is None:
        peak=max(peak,group_rss(child.pid))
        if peak>12*1024**3: reason="rss-cap"
        elif memory()["MemAvailable"]<4*1024**3: reason="reserve"
        elif time.monotonic()-started>a.timeout: reason="timeout"
        if reason:
            os.killpg(child.pid,signal.SIGTERM)
            try: child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid,signal.SIGKILL); child.wait()
            break
        time.sleep(0.1)
    status=child.wait()
    if group_rss(child.pid)>0:
        reason=reason or "surviving-descendants"
        try: os.killpg(child.pid,signal.SIGKILL)
        except ProcessLookupError: pass
wrapper_exit=124 if reason else (status if status>=0 else 128-status)
metrics=dict(command=cmd,exit=wrapper_exit,child_exit=status,stop=reason,seconds=time.monotonic()-started,
    peak_group_rss_bytes=peak,threads=1,swap_total=memory()["SwapTotal"],
    cap_bytes=12*1024**3,reserve_bytes=4*1024**3)
a.log.with_suffix(a.log.suffix+".json").write_text(json.dumps(metrics,indent=2)+"\n")
print(json.dumps(metrics))
raise SystemExit(wrapper_exit)
