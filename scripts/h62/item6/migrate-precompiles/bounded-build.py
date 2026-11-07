#!/usr/bin/env python3
"""Clean, serial per-file Lean compilation without Lake/master artifact caches.
Output must be absent; imported oleans come only from this run and toolchain.
Process virtual memory hard-capped at 12 GiB; no swap admission, 4 GiB reserve.
"""
import argparse, fcntl, importlib.util, json, os, resource, signal, subprocess, time
from pathlib import Path
GIB=1024**3
spec=importlib.util.spec_from_file_location("census",Path(__file__).with_name("census.py"));census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(12*GIB,12*GIB))
    os.setsid()
def available():
    d={k:int(v.split()[0])*1024 for k,v in (s.split(":",1) for s in Path("/proc/meminfo").read_text().splitlines())}
    if d["SwapTotal"]: raise RuntimeError("no-swap prerequisite failed")
    cg=Path("/sys/fs/cgroup"); mx=(cg/"memory.max").read_text().strip()
    return min(d["MemAvailable"], int(mx)-int((cg/"memory.current").read_text())) if mx!="max" else d["MemAvailable"]
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--toolchain",type=Path,required=True);ap.add_argument("--out",type=Path,required=True);ap.add_argument("--keysort-only",action="store_true");ap.add_argument("--fixture",type=Path);ap.add_argument("--import-products",type=Path);a=ap.parse_args()
    root=Path.cwd();out=a.out.resolve();lean=a.toolchain.resolve()/"bin/lean"
    lock=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock").open("a")
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    if out.exists(): raise RuntimeError("output exists: clean measurement requires a fresh path")
    if available()<4*GIB: raise RuntimeError("4 GiB reserve unavailable")
    out.mkdir(parents=True); products=out/"olean";products.mkdir()
    env=os.environ.copy();env.update(LEAN_NUM_THREADS="1",LEAN_PATH=str(products))
    modules=["Solidity.KeySort"] if a.keysort_only else census.census(root)["topological_closure"]
    if a.fixture:
        fixture=a.fixture.resolve().relative_to(root)
        if not str(fixture).startswith("tests/h62/item6/migrate-precompiles/") or fixture.suffix != ".lean":
            raise ValueError("fixture outside assigned backfill scope")
        modules=[]
        def visit(m):
            if m in modules:return
            for dep in census.imports((root/(m.replace(".","/")+".lean")).read_text()):visit(dep)
            modules.append(m)
        for dep in census.imports((root/fixture).read_text()):visit(dep)
        modules.append(str(fixture.with_suffix("")).replace("/","."))
    if a.import_products:
        if not a.fixture: raise ValueError("existing products permitted only for diagnostic fixtures")
        modules=modules[-1:]
        env["LEAN_PATH"] += os.pathsep + str(a.import_products.resolve())
    versions={x:subprocess.check_output([str(a.toolchain.resolve()/"bin"/x),"--version"],text=True).strip() for x in ("lean","lake")}
    summary=dict(versions=versions,settings=dict(threads=1,jobs=1,address_space_bytes=12*GIB,reserve_bytes=4*GIB,swap=0,cache="existing diagnostic import products" if a.import_products else "empty private olean directory; no Lake cache"),expected_modules=modules,completed_modules=0,modules=[],status="running")
    start=time.monotonic()
    for m in modules:
        src=m.replace(".","/")+".lean";dest=products/(m.replace(".","/")+".olean");dest.parent.mkdir(parents=True,exist_ok=True)
        cmd=[str(lean),"-j1","--tstack=131072","-o",str(dest),src]
        log=out/(m+".log");tick=time.monotonic();reason=None
        with log.open("w") as f:
            proc=subprocess.Popen(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,pass_fds=(lock.fileno(),))
            try:
                while True:
                    pid, status, usage = os.wait4(proc.pid, os.WNOHANG)
                    if pid:
                        proc.returncode = os.waitstatus_to_exitcode(status); break
                    if available()<4*GIB:
                        reason="available memory below 4 GiB reserve";os.killpg(proc.pid,signal.SIGTERM)
                        _, status, usage = os.wait4(proc.pid, 0)
                        proc.returncode = os.waitstatus_to_exitcode(status); break
                    time.sleep(0.1)
            finally:
                if proc.returncode is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(proc.pid, 0)
                    proc.returncode = os.waitstatus_to_exitcode(status)
        if proc.returncode == 0 and not dest.is_file(): reason="successful compiler produced no olean"
        rec=dict(module=m,command=cmd,exit=proc.returncode,wall_seconds=time.monotonic()-tick,peak_rss_kib=usage.ru_maxrss,resource_stop=reason)
        summary["modules"].append(rec);summary["wall_seconds"]=time.monotonic()-start
        summary["completed_modules"]=len(summary["modules"])
        summary["status"]="running" if proc.returncode==0 and not reason else "fail"
        (out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
        print(json.dumps(rec),flush=True)
        if summary["status"]=="fail": return 1
    summary["status"]="pass"
    (out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    return 0
if __name__=="__main__":raise SystemExit(main())
