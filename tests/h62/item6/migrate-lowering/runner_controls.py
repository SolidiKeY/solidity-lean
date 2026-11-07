#!/usr/bin/env python3
"""Exercise inherited-lock, signal, and dead-leader cleanup with lightweight processes."""
import fcntl, json, os, signal, subprocess, sys, tempfile, time
from pathlib import Path
root=Path(__file__).resolve().parents[4]; script=root/"scripts/h62/item6/migrate-lowering"
sys.path.insert(0,str(script))
from process_group import members, stop_owned
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
with tempfile.TemporaryDirectory() as tmp:
    out=Path(tmp)/"normal.json"
    args=[sys.executable,str(script/"bounded.py"),"--output",str(out),"--lock-fd",str(lock.fileno()),"--",sys.executable,"-c","import time; data=bytearray(1048576); time.sleep(0.8)"]
    r=subprocess.run(args,cwd=root,pass_fds=(lock.fileno(),),stdout=subprocess.DEVNULL)
    data=json.loads(out.read_text())
    assert r.returncode==0 and data["sampled_peak_group_rss_bytes"]>0 and data["stop_reason"] is None
    assert json.loads(out.with_suffix(".live.json").read_text())["status"]=="finished"
    out=Path(tmp)/"interrupted.json"
    args[3]=str(out); args[-1]="import subprocess,sys,time; subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); time.sleep(30)"
    r=subprocess.Popen(args,cwd=root,pass_fds=(lock.fileno(),),stdout=subprocess.DEVNULL)
    live=out.with_suffix(".live.json"); deadline=time.monotonic()+5
    while not live.exists() and time.monotonic()<deadline: time.sleep(0.05)
    assert live.exists()
    group=json.loads(live.read_text())["process_group"]
    r.send_signal(signal.SIGTERM); assert r.wait(timeout=15)==125
    assert not members(group) and "runner signal" in json.loads(out.read_text())["stop_reason"]
    # A leader exits while its descendant remains. Cleanup must not require leader cwd.
    orphan=subprocess.Popen([sys.executable,"-c","import subprocess,sys,time; subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); time.sleep(0.2)"],cwd=root,start_new_session=True)
    orphan.wait(timeout=5)
    assert members(orphan.pid)
    stop_owned(orphan.pid,root)
    assert not members(orphan.pid)
print("PASS: inherited lock, atomic metrics, signal cleanup, and dead-leader descendant cleanup")
