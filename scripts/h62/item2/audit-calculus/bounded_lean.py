#!/usr/bin/env python3
"""Serial diagnostics with private artifacts, immutable receipts and live bounds.

The VM's cgroup is the hard memory limit. Lean allocations are capped at12GiB;
RSS and4GiB reserve are monitored. Virtual address space is NOT capped:131072KB
thread stacks reserve address space without consuming that much resident RAM.
This driver supplements, and never replaces, the final repository gates.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time
sys.dont_write_bytecode = True
from census import mask
from receipts import find_direct_compile, parse_export_log, probe_total_or_tombstone, validate_statement_encoding, CHUNK_HELPER, DAG_HELPER

GIB = 1024**3
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
LOCK = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
HELPER = "tests/h62/item2/audit-calculus/KernelCensus.lean"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def headroom():
    mem = dict(re.findall(r"^(\w+):\s+(\d+)", Path("/proc/meminfo").read_text(), re.M))
    available = int(mem["MemAvailable"]) * 1024
    limit = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    if limit != "max":
        available = min(available, int(limit)-int(Path("/sys/fs/cgroup/memory.current").read_text()))
    if available < 4*GIB: raise RuntimeError("RESOURCE_RESERVE: less than4GiB available")
    if len(Path("/proc/swaps").read_text().splitlines()) > 1:
        raise RuntimeError("RESOURCE_SWAP: swap is enabled")
    return available


def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (1800, 1800))


def group_usage(group):
    rss, virtual, threads = 0, 0, 0
    for path in Path("/proc").iterdir():
        if not path.name.isdigit(): continue
        try:
            fields = (path/"stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) != group: continue
            status = dict(re.findall(r"^(\w+):\s+(\d+)", (path/"status").read_text(), re.M))
            rss += int(status.get("VmRSS", 0))*1024
            virtual += int(status.get("VmSize", 0))*1024
            threads += int(status.get("Threads", 0))
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
    return rss, virtual, threads


def terminate_group(proc):
    try: os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError: pass
    try: proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try: os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError: pass
        proc.wait()


def execute(command, root, env, log):
    reserve = headroom()
    start = time.monotonic()
    peaks = [0, 0, 0]
    stopped = None
    with log.open("w") as stream:
        proc = subprocess.Popen(command, cwd=root, env=env, stdout=stream,
            stderr=subprocess.STDOUT, preexec_fn=limits, start_new_session=True)
        try:
            while proc.poll() is None:
                try:
                    headroom()
                    current = group_usage(proc.pid)
                    peaks = [max(a,b) for a,b in zip(peaks,current)]
                    if current[0] > 12*GIB:
                        raise RuntimeError("RESOURCE_RSS: owned process group exceeds12GiB")
                except RuntimeError as failure:
                    stopped = str(failure)
                    print(stopped, file=stream, flush=True)
                    terminate_group(proc)
                    break
                time.sleep(0.25)
            exit_code = 88 if stopped else proc.returncode
        finally:
            if proc.poll() is None: terminate_group(proc)
    return {"command": command, "exit": exit_code, "wall_seconds": time.monotonic()-start,
            "log": str(log), "log_sha256": sha(log), "available_before": reserve,
            "peak_group_rss_bytes": peaks[0], "peak_group_virtual_bytes": peaks[1],
            "peak_group_threads": peaks[2], "resource_stop": stopped,
            "lean_allocation_limit_mb": 12288, "rss_monitor_limit_bytes": 12*GIB,
            "cpu_seconds_cap": 1800, "reserve_bytes": 4*GIB,
            "monitor_interval_seconds": 0.25,
            "cgroup_memory_max": Path("/sys/fs/cgroup/memory.max").read_text().strip()}


def module_for(relative):
    relative = relative.removeprefix("vendor/LeanTeX/")
    return relative.removesuffix(".lean").replace("/", ".")


def quoted_module(module):
    return ".".join(part if re.fullmatch(r"[A-Za-z_][\w]*",part) else "«"+part+"»" for part in module.split("."))


def imports(root, relative):
    result = []
    for line in mask((root/relative).read_text()).splitlines():
        match = re.match(r"^[ \t]*(?:public[ \t]+)?import[ \t]+([^\s;]+)", line)
        if not match: continue
        module = match[1].replace("«", "").replace("»", "")
        candidate = module.replace(".", "/")+".lean"
        if (root/candidate).is_file(): result.append(candidate)
        elif (root/"vendor/LeanTeX"/candidate).is_file(): result.append("vendor/LeanTeX/"+candidate)
        elif module.split(".")[0] not in {"Init", "Lean", "Std", "Lake"}:
            raise RuntimeError("UNRESOLVED_IMPORT: "+module)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--deps", action="store_true")
    parser.add_argument("--export-census", action="store_true")
    parser.add_argument("--reuse-private", action="store_true")
    parser.add_argument("--export-only", action="store_true")
    parser.add_argument("--chunked-export", action="store_true")
    parser.add_argument("--chunk-size", type=int, default=16)
    parser.add_argument("--dag-export", action="store_true")
    parser.add_argument("files", nargs="+")
    args = parser.parse_args()
    root, evidence, lean = args.root.resolve(), args.evidence.resolve(), args.lean.resolve()
    if evidence.is_relative_to(root): parser.error("H44: outputs must be outside git")
    if args.dag_export and not (args.export_census and args.chunked_export): parser.error("--dag-export requires --export-census --chunked-export")
    if args.chunked_export and not args.export_census: parser.error("--chunked-export requires --export-census")
    if not 1 <= args.chunk_size <= 64: parser.error("chunk size must be in 1..64")
    if args.export_only and not args.export_census: parser.error("--export-only requires --export-census")
    evidence.mkdir(parents=True, exist_ok=True)
    build = evidence/"private-olean"; build.mkdir(exist_ok=True)
    run = evidence/"runs"/(str(time.time_ns())+"-"+str(os.getpid()));run.mkdir(parents=True)
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        subprocess.run(["git","diff","--exit-code",BASE,"--","Solidity","vendor/LeanTeX","docs/module-map"],cwd=root,check=True,stdout=subprocess.DEVNULL)
        print(subprocess.check_output(["git","status","--short","--branch"],cwd=root,text=True),flush=True)
        env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(build))
        version = subprocess.check_output([str(lean),"--version"],text=True).strip()
        binary_hash = sha(lean)
        common = {"schema":2,"run":str(run),"version":version,"lean_sha256":binary_hash,
                  "driver_sha256":sha(Path(__file__)),"head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip()}
        print(version,flush=True)
        records = evidence/"lean-commands.jsonl"
        history = [json.loads(line) for line in records.read_text().splitlines()] if records.exists() else []
        latest = {r["file"]:r for r in history if r.get("kind","compile") in {"compile","compile-cache"}}
        seen, pending = set(), set()

        def save(record):
            record = dict(common,**record)
            history.append(record)
            with records.open("a") as stream: stream.write(json.dumps(record,sort_keys=True)+"\n")
            print(json.dumps(record,sort_keys=True),flush=True)
            if record.get("kind","compile") in {"compile","compile-cache"}: latest[record["file"]]=record
            return record

        def artifact(relative):
            return (build/relative.removeprefix("vendor/LeanTeX/")).with_suffix(".olean")

        def check(relative, force=False):
            if relative in seen:return
            if relative in pending:raise RuntimeError("import cycle: "+relative)
            pending.add(relative)
            dependencies = imports(root,relative)
            if args.deps:
                for dep in dependencies:check(dep)
            path,output = root/relative,artifact(relative)
            output.parent.mkdir(parents=True,exist_ok=True)
            dependency_hashes = {dep:sha(artifact(dep)) for dep in dependencies if artifact(dep).exists()}
            previous = latest.get(relative,{})
            matches = (previous.get("exit")==0 and previous.get("source_sha256")==sha(path)
                       and previous.get("version")==version and output.exists()
                       and len(dependency_hashes)==len(dependencies))
            direct=find_direct_compile(history,relative,sha(path),sha(output) if output.exists() else None,dependency_hashes,binary_hash)
            exact = matches and direct is not None
            if not force and relative.startswith(("Solidity/", "vendor/LeanTeX/")) and (args.reuse_private or args.export_only) and exact:
                save({"kind":"compile-cache","file":relative,"exit":0,"source_sha256":sha(path),
                      "artifact":str(output),"artifact_sha256":sha(output),"dependency_artifact_hashes":dependency_hashes,
                      "source_compilation_verified":True,"origin_compile_log":direct["log"],
                      "origin_compile_log_sha256":direct["log_sha256"],"origin_run":direct["run"],"wall_seconds":0})
            else:
                if args.export_only and not force:
                    raise RuntimeError("NO_CURRENT_PASSED_PRIVATE_ARTIFACT: "+relative)
                log=run/"logs"/Path(relative).with_suffix(".log");log.parent.mkdir(parents=True,exist_ok=True)
                command=[str(lean),"-j1","--tstack=131072","--memory=12288"]
                if relative.startswith("vendor/LeanTeX/"):command.append("--root=vendor/LeanTeX")
                command += ["-o",str(output),relative]
                execution=execute(command,root,env,log)
                receipt=save(dict(execution,kind="compile",file=relative,source_compilation_verified=execution["exit"]==0,
                                 source_sha256=sha(path),dependency_artifact_hashes=dependency_hashes,
                                 artifact=str(output),artifact_sha256=sha(output) if output.exists() else None))
                if receipt["exit"]:
                    print("\n".join(line[:500] for line in log.read_text().splitlines() if "H62_KERNEL_CENSUS" not in line)[:4000],flush=True)
                    raise SystemExit(receipt["exit"])
            seen.add(relative);pending.remove(relative)

        helper=DAG_HELPER if args.dag_export else CHUNK_HELPER if args.chunked_export else HELPER
        if args.export_census:check(helper,force=True)
        for relative in args.files:
            check(relative)
            if not args.export_census:continue
            module=module_for(relative)
            scratch=run/"scratch"/Path(relative);scratch.parent.mkdir(parents=True,exist_ok=True)
            preamble="import "+quoted_module(module)+"\nimport "+quoted_module(module_for(helper))+"\n"
            index=(evidence/"kernel"/relative).with_suffix(".json");index.parent.mkdir(parents=True,exist_ok=True)
            index.unlink(missing_ok=True)
            export_format="chunks-v1" if args.chunked_export else "module-v1"
            helper_binding=dict(helper_file=helper,helper_source_sha256=sha(root/helper),
                helper_artifact=str(artifact(helper)),helper_artifact_sha256=sha(artifact(helper)))
            if args.chunked_export:
                chunk_command="#audit_module_dag_chunk" if args.dag_export else "#audit_module_chunk"
                probe=scratch.with_suffix(".probe.lean")
                probe.write_text(preamble+f'{chunk_command} "{module}" from 0 count {args.chunk_size}\n')
                probe_log=run/"probe"/Path(relative).with_suffix(".log");probe_log.parent.mkdir(parents=True,exist_ok=True)
                execution=execute([str(lean),"-j1","--tstack=131072","--memory=12288","--root=/workspace",str(probe)],root,env,probe_log)
                probe_record=dict(execution,kind="kernel-census-probe",file=relative,module=module,
                    source_sha256=sha(root/relative),scratch=str(probe),scratch_sha256=sha(probe),**helper_binding)
                if execution["exit"]:
                    save(dict(probe_record,kind="kernel-census"))
                    raise SystemExit(execution["exit"])
                save(probe_record)
                try:
                    total=probe_total_or_tombstone(probe_record,args.chunk_size,save)
                except RuntimeError:
                    raise SystemExit(89)
                offsets=list(range(0,total,args.chunk_size)) or [0]
                scratch.write_text(preamble+"".join(f'{chunk_command} "{module}" from {offset} count {args.chunk_size}\n' for offset in offsets))
            else:
                scratch.write_text(preamble+'#audit_module "'+module+'"\n')
            log=run/"kernel"/Path(relative).with_suffix(".log");log.parent.mkdir(parents=True,exist_ok=True)
            command=[str(lean),"-j1","--tstack=131072","--memory=12288","--root=/workspace",str(scratch)]
            receipt=dict(execute(command,root,env,log),kind="kernel-census",file=relative,module=module,
                         export_format=export_format,
                         source_sha256=sha(root/relative),artifact=str(artifact(relative)),artifact_sha256=sha(artifact(relative)),
                         scratch=str(scratch),scratch_sha256=sha(scratch),**helper_binding)
            if receipt["exit"]==0:
                try:
                    data=parse_export_log(log.read_text(),module,export_format)
                    for theorem in data["theorems"]:
                        validate_statement_encoding(theorem)
                        if args.dag_export and theorem.get("type_expression_format")!="expr-dag-v1":
                            raise RuntimeError("DAG helper returned another expression encoding")
                except (RuntimeError,ValueError,KeyError,TypeError) as failure:
                    save(dict(receipt,exit=89,assembly_error=str(failure)))
                    raise SystemExit(89)
                output=log.with_suffix(".json");output.write_text(json.dumps(data,indent=2)+"\n")
                receipt.update(json=str(output),json_sha256=sha(output),index=str(index))
                index.write_bytes(output.read_bytes())
            receipt=save(receipt)
            if receipt["exit"]:raise SystemExit(receipt["exit"])


if __name__=="__main__":main()
