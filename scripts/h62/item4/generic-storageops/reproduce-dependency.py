#!/usr/bin/env python3
"""Reproduce pinned toolchain prerequisite/dependency check without old artifacts.

Run under writer.lock. Locates the pinned archive beside --toolchain, verifies
it, then freshly extracts and invokes that archive. Build artifacts stay off git.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

p=argparse.ArgumentParser()
p.add_argument("--toolchain",type=Path,required=True)
p.add_argument("--inputs",type=Path,default=Path("/workspace/h62-coordinator-inputs"))
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
root=Path(__file__).resolve().parents[4]
if a.output.resolve().is_relative_to(root): p.error("build output must be off git")
pin=json.loads((a.inputs/"toolchain-pin.json").read_text())
archive=a.toolchain.parent/pin["asset"]
sha=hashlib.file_digest(archive.open("rb"),"sha256").hexdigest()
if sha!=pin["sha256"]: raise SystemExit("FAIL: toolchain archive pin mismatch")
a.output.mkdir(parents=True,exist_ok=True)
# Never trust an existing extracted directory; freshly extract the pinned archive.
fresh=Path(tempfile.mkdtemp(prefix="official-toolchain-",dir=a.output))
subprocess.run(["tar","--zstd","-xf",str(archive),"-C",str(fresh)],check=True)
version=pin["toolchain"].split(":v")[-1]
extracted=fresh/("lean-"+version+"-linux")
lean=extracted/"bin/lean"; lake=extracted/"bin/lake"
for tool in (lean,lake):
    output=subprocess.check_output([str(tool),"--version"],text=True)
    print(output.strip(),flush=True)
    if ("version "+version) not in output: raise SystemExit("FAIL: extracted tool version mismatch")
build=a.output/"build"
build.mkdir(exist_ok=True)
config=f'''name = "h62-storageops-validation"
version = "0.1.0"
enableArtifactCache = false
buildDir = {json.dumps(str(build/".lake/build"))}
[[lean_lib]]
name = "Solidity"
srcDir = {json.dumps(str(root))}
weakLeanArgs = ["--tstack=131072", "-j1", "-M12288"]
'''
(build/"lakefile.toml").write_text(config)
env=dict(os.environ,PATH=str(lean.parent)+os.pathsep+os.environ["PATH"],LEAN_NUM_THREADS="1")
env.update(LAKE_ARTIFACT_CACHE="false",LAKE_RESTORE_ARTIFACTS="false",LAKE_CACHE_DIR="",
    XDG_CACHE_HOME=str(a.output/"cache"))
for name in ("LEAN_PATH","LEAN_SRC_PATH","LEAN_SYSROOT"):
    env.pop(name,None)
guard=root/"scripts/h62/item4/generic-storageops/bounded.py"
commands=[("keysort",[str(lean),"-j1","-M12288","--tstack=131072","Solidity/KeySort.lean"]),
 ("dependencies",[str(lake),"-d",str(build),"--no-cache","build","Solidity.Backend.StorageOps.OperationFamilies"])]
for name,command in commands:
    completed=subprocess.run([sys.executable,"-B",str(guard),"--timeout","300","--log",str(a.output/(name+".log")),"--"]+command,cwd=root,env=env)
    if completed.returncode: raise SystemExit(completed.returncode)
print("DEPENDENCY_PREREQUISITES_PASS (not a full runtime gate)")
