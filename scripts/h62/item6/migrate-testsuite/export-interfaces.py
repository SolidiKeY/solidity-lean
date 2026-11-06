#!/usr/bin/env python3
"""Export all assigned kernel interfaces serially, separately from build timings."""
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path
from measure import bounded
ap=argparse.ArgumentParser();ap.add_argument("--toolchain",type=Path,required=True);ap.add_argument("--census",type=Path,required=True);ap.add_argument("--lean-path",type=Path,required=True);ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
repo=Path.cwd();census_path=a.census.resolve();census=json.loads(census_path.read_text());toolchain=a.toolchain.resolve();lean_path=a.lean_path.resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
generator=repo/"scripts/h62/item6/migrate-testsuite/generate-interface.py"
env=os.environ.copy()
for key in ("LEAN_PATH","LEAN_SRC_PATH","LAKE_HOME","LEAN_SYSROOT"): env.pop(key,None)
env.update(PATH=str(toolchain/"bin")+":"+env["PATH"],LEAN_NUM_THREADS="1",LEAN_PATH=str(lean_path),XDG_CACHE_HOME=str(out/"cache"))
summary={"status":"running","boundary":"compiled interface export only; not full-build timing","runtime_image":os.environ.get("H62_RUNTIME_IMAGE"),"generator_sha256":hashlib.sha256(generator.read_bytes()).hexdigest(),"encoder_sha256":hashlib.sha256((generator.parent/"expr_dag.py").read_bytes()).hexdigest(),"schema":"expr-dag-v2","versions":{t:subprocess.check_output([str(toolchain/"bin"/t),"--version"],env=env,text=True).strip() for t in ("lean","lake")},"requested_modules":sorted(census["owned"]),"results":[]}
os.chdir(out);start=time.monotonic()
with (out/"raw.log").open("wb") as combined:
    for index,module in enumerate(summary["requested_modules"]):
        print(f"{index+1}/{len(summary['requested_modules'])} {module}",flush=True)
        stem=module.replace(".","_");source=out/(stem+".lean");log=out/(stem+".log")
        source.write_bytes(subprocess.check_output([sys.executable,str(generator),str(census_path),"--module",module],env=env))
        r=bounded([str(toolchain/"bin/lean"),"--tstack=131072","-j1",str(source)],env,log);r.update(module=module,fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest());summary["results"].append(r)
        with log.open("rb") as stream: shutil.copyfileobj(stream,combined)
        combined.flush();summary["wall_s"]=time.monotonic()-start
        if r["exit"] or r["stop"]: summary["status"]="fail"
        (out/"summary.json").write_text(json.dumps(summary,indent=2))
        if summary["status"]=="fail": raise SystemExit(1)
summary["status"]="pass";(out/"summary.json").write_text(json.dumps(summary,indent=2))
