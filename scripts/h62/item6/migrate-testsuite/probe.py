#!/usr/bin/env python3
"""Bounded isolated fixture/type-export checks, separate from clean build timings."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
from measure import bounded
ap=argparse.ArgumentParser();ap.add_argument("--toolchain",required=True,type=Path);ap.add_argument("--fixture",required=True,type=Path);ap.add_argument("--out",required=True,type=Path);ap.add_argument("--lean-path",type=Path);a=ap.parse_args()
out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
env=os.environ.copy()
for key in ("LEAN_PATH","LEAN_SRC_PATH","LAKE_HOME","LEAN_SYSROOT"): env.pop(key,None)
env.update(PATH=str(a.toolchain.resolve()/"bin")+":"+env["PATH"],LEAN_NUM_THREADS="1",XDG_CACHE_HOME=str(out/"cache"))
if a.lean_path: env["LEAN_PATH"]=str(a.lean_path.resolve())
result=bounded([str(a.toolchain.resolve()/"bin/lean"),"--tstack=131072","-j1",str(a.fixture.resolve())],env,out/"lean.log")
result.update(fixture_sha256=hashlib.sha256(a.fixture.read_bytes()).hexdigest(),runtime_image=os.environ.get("H62_RUNTIME_IMAGE"),versions={tool:subprocess.check_output([str(a.toolchain.resolve()/"bin"/tool),"--version"],env=env,text=True).strip() for tool in ("lean","lake")},boundary="isolated fixture/export only; not the full assigned build",status="pass" if result["exit"]==0 and result["stop"] is None else "fail")
(out/"summary.json").write_text(json.dumps(result,indent=2));print(json.dumps(result));raise SystemExit(0 if result["status"]=="pass" else 1)
