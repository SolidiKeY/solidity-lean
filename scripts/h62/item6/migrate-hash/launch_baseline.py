#!/usr/bin/env python3
"""Launch one owned, bounded baseline controller; caller must hold writer lock.
The child waits for this caller to finish exporting before taking the same lock.
This executes the authorized baseline only; it creates no goal or continuation.
"""
import json, os, pathlib, subprocess, sys
root=pathlib.Path.cwd(); evidence=pathlib.Path("/workspace/migrate-hash-evidence")
output=pathlib.Path("/workspace/migrate-hash-full/old-full-2")
assert not output.exists(),"baseline already exists; inspect it, never duplicate/reset"
assert not subprocess.check_output(["git","status","--porcelain"],text=True),"commit first"
controller=evidence/"baseline-controller.json"
if controller.exists():
    old=json.loads(controller.read_text())
    assert not pathlib.Path(f"/proc/{old['pid']}").exists(),"existing controller alive"
log=output.parent/"old-full-2-driver.log"
cmd=["flock","/tmp/solidity-lean-feature-groups-20261025/writer.lock",sys.executable,str(root/"scripts/h62/item6/migrate-hash/full_measure.py"),"/workspace/.setup/tools/lean-4.24.0-linux",str(output)]
with log.open("wb") as stream:
    child=subprocess.Popen(cmd,cwd=root,stdin=subprocess.DEVNULL,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
data={"pid":child.pid,"command":cmd,"log":str(log),"directory":str(output),"head":subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),"state":"launched; takes writer lock after export; inspect results.json and summary.json for progress/outcome","no_duplicate_job":True,"not_a_new_goal":True}
controller.write_text(json.dumps(data,indent=2)+"\n")
try:
    subprocess.run([sys.executable,"scripts/h62/item6/migrate-hash/export.py"],check=True)
except BaseException:
    # Child is still blocked on our caller's lock; cancel this owned pending launch.
    child.terminate(); child.wait(); raise
print(json.dumps(data,indent=2))
