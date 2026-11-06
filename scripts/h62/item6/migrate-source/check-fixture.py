#!/usr/bin/env python3
"""Bounded serial check of an isolated fixture; does not certify original modules."""
import fcntl
import hashlib
import resource
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from build import LOCK, GIB, headroom, group_rss, group_vms
# Arguments: toolchain, fixture, import library, output prefix.
tc,fixture,lib,out=map(lambda p:Path(p).resolve(),sys.argv[1:])
with LOCK.open("a") as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB); headroom()
    cmd=[str(tc/"bin/lean"),"--root="+str(fixture.parent),"--tstack=131072","-j1","-M10000",str(fixture)]
    env=os.environ.copy();env.update(LEAN_NUM_THREADS="1",LEAN_PATH=str(lib))
    fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest()
    compiler_version=subprocess.check_output([str(tc/"bin/lean"),"--version"],text=True).strip()
    start=time.monotonic();rss=0;vms=0;vmpeak=0;proc=None;error=None
    try:
        with out.with_suffix(".log").open("w") as log:
            proc=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            while proc.poll() is None:
                rss=max(rss,group_rss(proc.pid));mem=group_vms(proc.pid);vms=max(vms,mem[0]);vmpeak=max(vmpeak,mem[1])
                if rss > 12*GIB: raise RuntimeError("12 GiB sampled group RSS threshold exceeded")
                headroom();time.sleep(0.05)
    except BaseException as e:
        error=type(e).__name__+": "+str(e)
        if proc and proc.poll() is None: os.killpg(proc.pid,signal.SIGTERM);proc.wait()
    if hashlib.sha256(fixture.read_bytes()).hexdigest()!=fixture_sha256: error="input changed during check"
    report={"fixture_sha256":fixture_sha256,"compiler_version":compiler_version,"parent_rlimit_as":resource.getrlimit(resource.RLIMIT_AS),"sampled_rss_stop_bytes":12*GIB,"sampled_peak_group_vms_bytes":vms,"sampled_largest_process_vmpeak_bytes":vmpeak,"command":cmd,"exit":None if proc is None else proc.returncode,"error":error,"wall_seconds":time.monotonic()-start,"sampled_peak_group_rss_bytes":rss,"lean_path":str(lib),"boundary":"single-file resource/fixture check; not a complete clean build"}
    out.with_suffix(".json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report));sys.exit(1 if error or report["exit"] else 0)
