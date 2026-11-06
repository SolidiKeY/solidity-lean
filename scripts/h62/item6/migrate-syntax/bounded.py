#!/usr/bin/env python3
"""Run one owned command tree with serial writer ownership and 4 GiB reserve."""
import argparse,fcntl,json,os,signal,subprocess,time
from pathlib import Path
from measure import available,GIB
p=argparse.ArgumentParser();p.add_argument("--output",type=Path,required=True);p.add_argument("command",nargs=argparse.REMAINDER);a=p.parse_args()
cmd=a.command[1:] if a.command[:1]==["--"] else a.command
assert cmd and not a.output.exists()
assert len(Path("/proc/swaps").read_text().splitlines())==1
with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","w") as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 assert available()>=4*GIB
 a.output.mkdir(parents=True);start=time.monotonic();stop=None
 with (a.output/"command.log").open("w") as log:
  child=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,env=dict(os.environ,LEAN_NUM_THREADS="1"))
  while True:
   pid,status,usage=os.wait4(child.pid,os.WNOHANG)
   if pid: child.returncode=os.waitstatus_to_exitcode(status);break
   if available()<4*GIB:
    stop="reserve-stop";os.killpg(child.pid,signal.SIGTERM);deadline=time.monotonic()+2
    while True:
     pid,status,usage=os.wait4(child.pid,os.WNOHANG)
     if pid: break
     if time.monotonic()>deadline:
      os.killpg(child.pid,signal.SIGKILL);_,status,usage=os.wait4(child.pid,0);break
     time.sleep(.1)
    child.returncode=os.waitstatus_to_exitcode(status);break
   time.sleep(.2)
 result=dict(command=cmd,exit=child.returncode,status=stop or ("pass" if child.returncode==0 else "fail"),wall_seconds=time.monotonic()-start,max_rss_kib=usage.ru_maxrss,threads=1,reserve_gib=4,swap="none")
 (a.output/"result.json").write_text(json.dumps(result,indent=2)+"\n")
 print(json.dumps(result));raise SystemExit(0 if result["status"]=="pass" else 1)
