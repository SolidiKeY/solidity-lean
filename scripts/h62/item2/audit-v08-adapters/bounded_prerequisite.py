#!/usr/bin/env python3
"""Serial master-v4.24.0 prerequisite or additive audit check; fresh by default.
Optional reuse requires a completed stable run and verified artifact digests.
Hard child address-space cap 12 GiB, no host swap, 4 GiB available reserve,
one Lean thread/CPU, 600s per file. Not the final run-lean.sh gate.
"""
import argparse, fcntl, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
CAP = 12 * 1024**3
RESERVE = 4 * 1024**3
PIN = "b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec"
MODULES = ["Solidity.KeySort", "Solidity.AST", "Solidity.SortCheck.Annotations", "Solidity.SortCheck.Parser", "SolkeyCheck"]

def memory():
    return {k: int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    ap.add_argument("--toolchain", type=Path, required=True)
    ap.add_argument("--key", type=Path, required=True)
    ap.add_argument("--reuse-from", type=Path, help="Reuse passing v4.24.0 frozen-source dependencies from an owned recorded run")
    ap.add_argument("--audit-module", type=Path, help="Compile an owned additive fixture and its unchanged local import closure instead of the checker prerequisite")
    args=ap.parse_args(); repo=args.repo.resolve(); evidence=args.evidence.resolve()
    if repo == evidence or repo in evidence.parents: raise SystemExit("Evidence must be off Git")
    if memory()["SwapTotal"]: raise SystemExit("Host swap is enabled")
    if memory()["MemAvailable"] < RESERVE: raise SystemExit("Insufficient OS reserve")
    archive=args.toolchain.parent/"lean-4.24.0-linux.tar.zst"
    if hashlib.file_digest(archive.open("rb"),"sha256").hexdigest()!=PIN: raise SystemExit("Toolchain archive hash mismatch")
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    subprocess.run(["git","status","--short","--branch"],cwd=repo,check=True)
    if evidence.exists(): raise SystemExit("Fresh evidence directory required")
    evidence.mkdir(parents=True)
    output=evidence/"olean"; output.mkdir()
    lean=str(args.toolchain/"bin/lean")
    versions=[subprocess.check_output([str(args.toolchain/"bin"/exe),"--version"],text=True).strip() for exe in ["lean","lake"]]
    if (repo/"lean-toolchain").read_text().strip() != "leanprover/lean4:v4.24.0":
        raise SystemExit("Assigned lane must retain the frozen master v4.24.0 toolchain")
    if not versions[0].startswith("Lean (version 4.24.0,") or "797c613eb9b6d4ec95db23e3e00af9ac6657f24b" not in versions[0]:
        raise SystemExit("Unexpected Lean binary: frozen master requires official v4.24.0")
    (evidence/"versions.txt").write_text("\n".join(versions)+"\n")
    env=os.environ.copy(); env.update(LEAN_NUM_THREADS="1", LEAN_PATH=str(output))
    env.pop("LEAN_SRC_PATH",None)
    def limits():
        os.setsid()
        resource.setrlimit(resource.RLIMIT_AS,(CAP,CAP))
        os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    modules=MODULES+["CHECKER_RUN"]
    if args.audit_module:
        import importlib.util, sys
        sys.dont_write_bytecode=True
        fixture=args.audit_module
        if fixture.is_absolute() or ".." in fixture.parts or not str(fixture).startswith("tests/h62/item2/audit-v08-adapters/"):
            raise SystemExit("Audit fixture must remain within exclusive tests scope")
        specification=importlib.util.spec_from_file_location("audit_graph",repo/"scripts/v08-build-graph.py")
        graph_module=importlib.util.module_from_spec(specification);specification.loader.exec_module(graph_module)
        graph=graph_module.SourceGraph(repo)
        modules=graph.closure([name for name in graph_module.header_imports((repo/fixture).read_text()) if graph.source(name) is not None])
        modules.append(str(fixture).removesuffix(".lean").replace("/","."))
    source_hashes={}
    for module in modules:
        if module == "CHECKER_RUN": continue
        relative=module.replace(".","/")+".lean"
        data=(repo/relative).read_bytes()
        source_hashes[relative]=hashlib.sha256(data).hexdigest()
        if not relative.startswith("tests/h62/item2/audit-v08-adapters/"):
            original=subprocess.check_output(["git","show",BASE+":"+relative],cwd=repo)
            if original != data: raise SystemExit("Frozen source differs: "+relative)
    (evidence/"source-start-sha256.json").write_text(json.dumps(source_hashes,sort_keys=True,indent=2)+"\n")
    reusable={}
    if args.reuse_from:
        import shutil
        old=json.loads((args.reuse_from/"results.json").read_text())
        if old["versions"] != versions: raise SystemExit("Reuse toolchain version mismatch")
        old_sources=json.loads((args.reuse_from/"source-start-sha256.json").read_text())
        if not (args.reuse_from/"source-sha256.json").is_file():
            raise SystemExit("Reuse requires a completed, source-stable successful run")
        old_final=json.loads((args.reuse_from/"source-sha256.json").read_text())
        if old_sources != old_final or not old["records"] or any(r["exit"] or r["stop"] is not None for r in old["records"]):
            raise SystemExit("Reuse requires a completed, source-stable successful run")
        for record in old["records"]:
            name=record["module"]; relative=name.replace(".","/")+".lean"
            if record["exit"] or record["stop"] is not None or relative.startswith("tests/"): continue
            if relative not in source_hashes or old_sources.get(relative)!=source_hashes[relative]: continue
            source_artifact=args.reuse_from/"olean"/(name.replace(".","/")+".olean")
            expected=record.get("artifact_sha256")
            if not expected: raise SystemExit("Reuse artifact lacks a production digest: " + name)
            if not source_artifact.is_file() or hashlib.file_digest(source_artifact.open("rb"),"sha256").hexdigest()!=expected:
                raise SystemExit("Reuse artifact digest mismatch: " + name)
            reusable[name]=(source_artifact,expected)
    records=[]
    for module in modules:
        if module=="CHECKER_RUN":
            command=[lean,"-j1","--tstack=131072","--run","SolkeyCheck.lean","--key",str(args.key)]
        else:
            relative=module.replace(".","/")+".lean"
            dest=output/(module.replace(".","/")+".olean");dest.parent.mkdir(parents=True,exist_ok=True)
            command=[lean,"-j1","--tstack=131072","-o",str(dest),relative]
        logpath=evidence/(module+".log")
        started=time.monotonic(); stopped=None
        with logpath.open("w") as log:
            log.write("$ "+json.dumps(command)+"\n");log.flush()
            if module in reusable:
                source_artifact,expected=reusable[module]
                shutil.copy2(source_artifact, dest)
                if hashlib.file_digest(dest.open("rb"),"sha256").hexdigest()!=expected:
                    raise SystemExit("Copied artifact digest mismatch")
                log.write("REUSED_PASSING_FROZEN_DEPENDENCY " + str(source_artifact) + "\n")
                record=dict(module=module,command=command,exit=0,stop=None,seconds=0,
                    log=str(logpath),reused_from=str(source_artifact),artifact_sha256=expected)
                records.append(record)
                (evidence/"results.json").write_text(json.dumps(dict(versions=versions,cap_bytes=CAP,reserve_bytes=RESERVE,
                    no_swap=True,records=records),sort_keys=True,indent=2)+"\n")
                print(json.dumps(record),flush=True)
                continue
            proc=subprocess.Popen(command,cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
            while proc.poll() is None:
                if memory()["MemAvailable"] < RESERVE: stopped="OS_RESERVE"
                if time.monotonic()-started>600: stopped="TIMEOUT"
                if stopped:
                    os.killpg(proc.pid,signal.SIGTERM)
                    try: proc.wait(timeout=5)
                    except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                    break
                time.sleep(0.2)
        record=dict(module=module,command=command,exit=proc.returncode,stop=stopped,
                    seconds=round(time.monotonic()-started,3),log=str(logpath))
        if not proc.returncode and not stopped and module!="CHECKER_RUN":
            record["artifact_sha256"]=hashlib.file_digest(dest.open("rb"),"sha256").hexdigest()
        records.append(record)
        (evidence/"results.json").write_text(json.dumps(dict(versions=versions,cap_bytes=CAP,reserve_bytes=RESERVE,
            no_swap=True,records=records),sort_keys=True,indent=2)+"\n")
        print(json.dumps(record),flush=True)
        if proc.returncode or stopped: raise SystemExit(1)
    for path,digest in source_hashes.items():
        if hashlib.sha256((repo/path).read_bytes()).hexdigest()!=digest:
            raise SystemExit("Source changed during validation: "+path)
    (evidence/"source-sha256.json").write_text(json.dumps(source_hashes,sort_keys=True,indent=2)+"\n")
    print("ADDITIVE_FIXTURE_CLOSURE_PASS" if args.audit_module else "KEYSORT_AND_CHECKER_PREREQUISITE_PASS")

if __name__=="__main__": main()
