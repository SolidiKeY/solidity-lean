#!/usr/bin/env python3
"""Bounded Bridge measurement or full run-lean gate, with serial compiler calls.
No toolchain or tracked configuration edits. Never treat a resource stop as pass.
"""
import argparse, fcntl, hashlib, json, os, pathlib, shlex, signal, subprocess, time

BUILD_TREE_POLICY="Lean library outputs cold; prebuilt ProofWidgets JS only"

def check_cold_build(root):
    for build in (root/".lake/build",root/"Bridge/.lake/build"):
        if build.exists() or build.is_symlink(): raise ValueError("Refusing non-clean build tree: "+str(build))
    for build in root.glob("Bridge/.lake/packages/*/.lake/build"):
        entries=list(build.iterdir()) if not build.is_symlink() else []
        if build.parent.parent.name=="proofwidgets" and not build.is_symlink() and len(entries)==1 and entries[0].name=="js" and entries[0].is_dir() and not entries[0].is_symlink():
            js=entries[0]
            def allowed_asset(path):
                return not path.is_symlink() and (path.is_dir() or (path.is_file() and (path.suffix==".js" or path==js/"lake.trace")))
            if all(allowed_asset(path) for path in js.rglob("*")):
                continue
        raise ValueError("Refusing dependency Lean build outputs: "+str(build))

def require_js_assets(root):
    manifest=json.loads((root/"Bridge/lake-manifest.json").read_text())
    if any(p.get("name")=="proofwidgets" for p in manifest["packages"]):
        js=root/"Bridge/.lake/packages/proofwidgets/.lake/build/js"
        trace=js/"lake.trace"
        if not trace.is_file() or not trace.stat().st_size or not any(p.is_file() and not p.is_symlink() for p in js.glob("*.js")):
            raise ValueError("Prepare pinned ProofWidgets JS assets before starting a Bridge measurement")

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root",type=pathlib.Path,required=True)
    ap.add_argument("--toolchain",type=pathlib.Path,required=True)
    ap.add_argument("--evidence",type=pathlib.Path,required=True)
    ap.add_argument("--solkey-rules",type=pathlib.Path,required=True)
    ap.add_argument("--bridge-measurement",action="store_true",help="measure Bridge package; final full run-lean gate remains required")
    args=ap.parse_args(); root=args.root.resolve(); tc=args.toolchain.resolve(); out=args.evidence.resolve()
    if out.exists() and any(out.iterdir()): raise SystemExit("Refusing nonempty evidence directory; preserve each attempt separately")
    out.mkdir(parents=True,exist_ok=True)
    rules=args.solkey_rules.resolve()
    if not rules.is_file(): raise SystemExit("Missing required SolKey rules input")
    lockpath=pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    with lockpath.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        try:
            check_cold_build(root)
            if args.bridge_measurement: require_js_assets(root)
        except (ValueError,OSError) as error: raise SystemExit(str(error))
        status=subprocess.check_output(["git","status","--short"],cwd=root,text=True)
        (out/"starting-status.log").write_text(status)
        def meminfo():
            return {k:int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())}
        if meminfo()["SwapTotal"]: raise SystemExit("Refusing: swap must be disabled")
        # A private sysroot keeps tracked toolchain files and installed binaries unchanged.
        mirror=out/"sysroot"; (mirror/"bin").mkdir(parents=True,exist_ok=True)
        for child in tc.iterdir():
            target=mirror/child.name
            if child.name!="bin" and not target.exists(): target.symlink_to(child,target_is_directory=child.is_dir())
        for child in (tc/"bin").iterdir():
            target=mirror/"bin"/child.name
            if child.name not in ("lean","lake") and not target.exists(): target.symlink_to(child)
        lean=mirror/"bin/lean"
        lean.write_text("#!/bin/sh\nexec flock "+shlex.quote(str(out/"compiler.lock"))+" timeout --foreground --kill-after=10 300 "+shlex.quote(str(tc/"bin/lean"))+" -j1 -M10240 \"$@\"\n")
        lean.chmod(0o755)
        lake=mirror/"bin/lake"
        lake.write_text("#!/bin/sh\nexec "+shlex.quote(str(tc/"bin/lake"))+" --no-cache \"$@\"\n"); lake.chmod(0o755)
        env=dict(os.environ,PATH=str(mirror/"bin")+os.pathsep+os.environ["PATH"],LEAN_SYSROOT=str(mirror),LAKE_OVERRIDE_LEAN="true",LEAN_NUM_THREADS="1",LAKE_CACHE_DIR="",LAKE_NO_CACHE="true",SOLKEY_RULES=str(rules))
        versions={x:subprocess.check_output([str(tc/"bin"/x),"--version"],text=True).strip() for x in ("lean","lake")}
        command=["bash","./scripts/check-bridge.sh"] if args.bridge_measurement else ["bash","./run-lean.sh","--bridge"]; start=time.monotonic(); stopped=None; peak=0
        with (out/"build.log").open("w") as log:
            proc=subprocess.Popen(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                while proc.poll() is None:
                    current=int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text()); peak=max(peak,current)
                    maximum=pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip()
                    vm_available=int(maximum)-current if maximum!="max" else meminfo()["MemAvailable"]
                    if min(meminfo()["MemAvailable"],vm_available)<4*1024**3:
                        stopped="host or VM cgroup headroom below 4 GiB reserve"; break
                    if time.monotonic()-start>10*3600:
                        stopped="10 hour runtime limit"; break
                    time.sleep(1)
            finally:
                # The owned session is retained until every member has exited.
                # --foreground keeps timeout/Lean inside this process group.
                try: os.killpg(proc.pid,signal.SIGTERM)
                except ProcessLookupError: pass
                deadline=time.monotonic()+10
                while time.monotonic()<deadline:
                    try: os.killpg(proc.pid,0)
                    except ProcessLookupError: break
                    time.sleep(0.1)
                try: os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                proc.wait()
        receipt={"command":command,"build_tree_policy":BUILD_TREE_POLICY,"measurement_scope":"Bridge" if args.bridge_measurement else "full-root-and-Bridge","root":str(root),"head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),"versions":versions,"exit":proc.returncode,"elapsed_seconds":time.monotonic()-start,"resource_stop":stopped,"peak_vm_cgroup_bytes":peak,"compiler_args":["-j1","-M10240"],"module_timeout_seconds":300,"reserve_gib":4,"swap_bytes":0,"cache":"disabled via empty LAKE_CACHE_DIR and --no-cache","status":"command-pass" if proc.returncode==0 and not stopped else "fail","full_gate_acceptance":"pending independent decisive-output review","solkey_rules_sha256":hashlib.sha256(rules.read_bytes()).hexdigest()}
        (out/"receipt.json").write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n"); print(json.dumps(receipt))
        return 0 if receipt["status"]=="command-pass" else 1
if __name__=="__main__": raise SystemExit(main())
