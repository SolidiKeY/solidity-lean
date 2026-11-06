#!/usr/bin/env python3
"""Serial fresh pinned-toolchain KeySort and checker prerequisite; no old cache.
Hard child address-space cap 12 GiB, no host swap, 4 GiB available reserve,
one Lean thread/CPU, 600s per file. Not the final run-lean.sh gate.
"""
import argparse, fcntl, hashlib, json, os, resource, signal, subprocess, time
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
CAP = 12 * 1024**3
RESERVE = 4 * 1024**3
PIN = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
MODULES = ["Solidity.KeySort", "Solidity.AST", "Solidity.SortCheck.Annotations", "Solidity.SortCheck.Parser", "SolkeyCheck"]

def memory():
    return {k: int(v.split()[0])*1024 for k,v in (line.split(":",1) for line in Path("/proc/meminfo").read_text().splitlines())}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--evidence", type=Path, required=True)
    ap.add_argument("--toolchain", type=Path, required=True)
    ap.add_argument("--key", type=Path, required=True)
    ap.add_argument("--audit-module", type=Path, help="Compile an owned additive fixture and its unchanged local import closure instead of the checker prerequisite")
    args=ap.parse_args(); repo=args.repo.resolve(); evidence=args.evidence.resolve()
    if repo == evidence or repo in evidence.parents: raise SystemExit("Evidence must be off Git")
    if memory()["SwapTotal"]: raise SystemExit("Host swap is enabled")
    if memory()["MemAvailable"] < RESERVE: raise SystemExit("Insufficient OS reserve")
    archive=args.toolchain.parent/"lean-4.35.0-linux.tar.zst"
    if hashlib.file_digest(archive.open("rb"),"sha256").hexdigest()!=PIN: raise SystemExit("Toolchain archive hash mismatch")
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    subprocess.run(["git","status","--short","--branch"],cwd=repo,check=True)
    if evidence.exists(): raise SystemExit("Fresh evidence directory required")
    evidence.mkdir(parents=True)
    output=evidence/"olean"; output.mkdir()
    lean=str(args.toolchain/"bin/lean")
    versions=[subprocess.check_output([str(args.toolchain/"bin"/exe),"--version"],text=True).strip() for exe in ["lean","lake"]]
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
        modules=graph.closure(graph_module.header_imports((repo/fixture).read_text()))
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
