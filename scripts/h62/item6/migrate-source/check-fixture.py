#!/usr/bin/env python3
"""Bounded serial check of an isolated fixture; does not certify original modules."""
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from build import LOCK, GIB, headroom, group_rss
# Arguments: toolchain, fixture, import library, output prefix.
tc,fixture,lib,out=map(lambda p:Path(p).resolve(),sys.argv[1:])
with LOCK.open("a") as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB); headroom()
    cmd=["prlimit","--as="+str(12*GIB),"--",str(tc/"bin/lean"),"--root="+str(fixture.parent),"--tstack=131072","-j1","-M10000",str(fixture)]
    env=os.environ.copy();env.update(LEAN_NUM_THREADS="1",LEAN_PATH=str(lib))
    start=time.monotonic();rss=0;proc=None;error=None
    try:
        with out.with_suffix(".log").open("w") as log:
            proc=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            while proc.poll() is None:
                rss=max(rss,group_rss(proc.pid));headroom();time.sleep(0.05)
    except BaseException as e:
        error=type(e).__name__+": "+str(e)
        if proc and proc.poll() is None: os.killpg(proc.pid,signal.SIGTERM);proc.wait()
    report={"command":cmd,"exit":None if proc is None else proc.returncode,"error":error,"wall_seconds":time.monotonic()-start,"sampled_peak_group_rss_bytes":rss,"lean_path":str(lib),"boundary":"isolated fixture only; original module unchanged"}
    out.with_suffix(".json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report));sys.exit(1 if error or report["exit"] else 0)
