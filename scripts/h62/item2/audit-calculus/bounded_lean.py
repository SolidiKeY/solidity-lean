#!/usr/bin/env python3
"""Serial, private-output per-file Lean diagnostics and dependency build.

Does not replace the final repository run-lean.sh gate. No cached artifacts
from the checkout or other workers are reused. Each invocation retains the
repository writer lock and records actual commands, exit codes and timing.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time

GIB = 1024**3
LOCK = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")


def headroom():
    mem = dict(re.findall(r"^(\w+):\s+(\d+)", Path("/proc/meminfo").read_text(), re.M))
    available = int(mem["MemAvailable"]) * 1024
    limit_path = Path("/sys/fs/cgroup/memory.max")
    if limit_path.exists() and limit_path.read_text().strip() != "max":
        available = min(available, int(limit_path.read_text()) - int(Path("/sys/fs/cgroup/memory.current").read_text()))
    if available < 4*GIB: raise RuntimeError("RESOURCE_RESERVE: less than 4GiB available")
    if len(Path("/proc/swaps").read_text().splitlines()) > 1:
        raise RuntimeError("RESOURCE_SWAP: swap is enabled")
    return available


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (12*GIB, 12*GIB))
    resource.setrlimit(resource.RLIMIT_CPU, (1800, 1800))


def execute(command, root, env, stream):
    proc = subprocess.Popen(command, cwd=root, env=env, stdout=stream,
                            stderr=subprocess.STDOUT, preexec_fn=limits)
    try:
        while proc.poll() is None:
            try:
                headroom()
            except RuntimeError as failure:
                print(str(failure), file=stream, flush=True)
                proc.terminate()
                try: proc.wait(timeout=5)
                except subprocess.TimeoutExpired: proc.kill(); proc.wait()
                return 88
            time.sleep(0.25)
        return proc.returncode
    finally:
        if proc.poll() is None:
            proc.terminate(); proc.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--deps", action="store_true")
    parser.add_argument("--export-census", action="store_true")
    parser.add_argument("files", nargs="+")
    args = parser.parse_args()
    root, evidence, lean = args.root.resolve(), args.evidence.resolve(), args.lean.resolve()
    if evidence.is_relative_to(root): parser.error("H44: outputs must be outside git")
    evidence.mkdir(parents=True, exist_ok=True)
    build = evidence/"private-olean"; build.mkdir(exist_ok=True)
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    with LOCK.open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        print(subprocess.check_output(["git", "status", "--short", "--branch"], cwd=root, text=True), flush=True)
        env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(build))
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        print(version, flush=True)
        seen, pending = set(), set()
        records = evidence/"lean-commands.jsonl"

        def check(relative):
            if relative in seen: return
            if relative in pending: raise RuntimeError("import cycle: "+relative)
            pending.add(relative)
            path = root/relative
            if args.deps:
                # Lean resolves imports in source order; build that closure serially.
                for line in path.read_text().splitlines():
                    match = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z][\w.]*)", line)
                    if not match: continue
                    module = match[1]
                    candidate = module.replace(".", "/")+".lean"
                    if (root/candidate).is_file(): check(candidate)
                    elif (root/"vendor/LeanTeX"/candidate).is_file(): check("vendor/LeanTeX/"+candidate)
                    elif module.split(".")[0] not in {"Init", "Lean", "Std", "Lake"}:
                        raise RuntimeError("UNRESOLVED_IMPORT: "+module)
            output_relative = relative.removeprefix("vendor/LeanTeX/")
            output = (build/output_relative).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            log = (evidence/"logs"/relative).with_suffix(".log")
            log.parent.mkdir(parents=True, exist_ok=True)
            command = [str(lean), "-j1", "--tstack=131072", "-o", str(output), relative]
            reserve = headroom()
            start = time.monotonic()
            with log.open("w") as stream:
                exit_code = execute(command, root, env, stream)
            elapsed = time.monotonic()-start
            record = {"command": command, "file": relative, "exit": exit_code,
                      "wall_seconds": elapsed, "available_before": reserve, "version": version,
                      "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                      "log": str(log), "address_space_cap": 12*GIB,
                      "cpu_seconds_cap": 1800, "threads": 1}
            with records.open("a") as stream: stream.write(json.dumps(record, sort_keys=True)+"\n")
            print(json.dumps(record, sort_keys=True), flush=True)
            if exit_code:
                print("\n".join(line[:500] for line in log.read_text().splitlines() if "H62_KERNEL_CENSUS" not in line)[:4000], flush=True)
                raise SystemExit(exit_code)
            seen.add(relative); pending.remove(relative)

        for relative in args.files:
            check(relative)
            if args.export_census:
                module = relative.removesuffix(".lean").replace("/", ".")
                scratch = evidence/"export-scratch.lean"
                scratch.write_text('import '+module+'\nimport tests.h62.item2.«audit-calculus».KernelCensus\n#audit_module "'+module+'"\n')
                log = (evidence/"kernel"/relative).with_suffix(".log")
                log.parent.mkdir(parents=True, exist_ok=True)
                command = [str(lean), "-j1", "--tstack=131072", "--root=/workspace", str(scratch)]
                reserve = headroom()
                start = time.monotonic()
                with log.open("w") as stream:
                    exit_code = execute(command, root, env, stream)
                record = {"kind": "kernel-census", "file": relative, "command": command,
                          "exit": exit_code, "wall_seconds": time.monotonic()-start, "log": str(log),
                          "available_before": reserve, "version": version}
                with records.open("a") as stream: stream.write(json.dumps(record, sort_keys=True)+"\n")
                print(json.dumps(record, sort_keys=True), flush=True)
                if exit_code: raise SystemExit(exit_code)
                result = [line.split("H62_KERNEL_CENSUS ",1)[1] for line in log.read_text().splitlines() if "H62_KERNEL_CENSUS " in line]
                if len(result) != 1: raise RuntimeError("expected exactly one kernel census record")
                log.with_suffix(".json").write_text(json.dumps(json.loads(result[0]), indent=2)+"\n")


if __name__ == "__main__":
    main()
