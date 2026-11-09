#!/usr/bin/env python3
"""Recheck the existing SolCases producer serially, without touching its sources/cache.
Guarded regression: boundary witnesses must come from the actual unchanged producer
and a successful bounded execution, never a fabricated host arithmetic oracle.
Run under the repository writer lock. Private fresh artifacts, Lean -j1, no server.
"""
import argparse
import hashlib
import json
import os
import re
import resource
import signal
import subprocess
import time
from pathlib import Path


def run(command, repo, env, log, timeout=300):
    if type(timeout) is not int or timeout <= 0:
        raise ValueError("invalid external timeout")
    memory = Path("/proc/meminfo").read_text()
    swap = int(re.search(r"^SwapTotal:\s+(\d+)", memory, re.M)[1])*1024
    minimum_available = int(re.search(r"^MemAvailable:\s+(\d+)", memory, re.M)[1])*1024
    if swap or minimum_available < 4*1024**3:
        raise RuntimeError("external no-swap/reserve prerequisite")
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3))
        assert resource.getrlimit(resource.RLIMIT_AS) == (12*1024**3, 12*1024**3)
    started = time.monotonic()
    with log.open("w") as output:
        child = subprocess.Popen(command, cwd=repo, env=env, stdout=output, stderr=subprocess.STDOUT,
                                 start_new_session=True, preexec_fn=limits)
        peak = 0
        stopped = None
        while child.poll() is None:
            processes = {}
            for path in Path("/proc").glob("[0-9]*/status"):
                try:
                    text = path.read_text()
                    parent = int(re.search(r"^PPid:\s+(\d+)", text, re.M)[1])
                    rss = re.search(r"^VmRSS:\s+(\d+)", text, re.M)
                    processes[int(path.parent.name)] = (parent, int(rss[1])*1024 if rss else 0)
                except (OSError, TypeError):
                    continue
            owned = {child.pid}
            while True:
                expanded = owned | {pid for pid, (parent, _) in processes.items() if parent in owned}
                if expanded == owned: break
                owned = expanded
            rss = sum(processes.get(pid, (0, 0))[1] for pid in owned)
            peak = max(peak, rss)
            memory = Path("/proc/meminfo").read_text()
            swap = int(re.search(r"^SwapTotal:\s+(\d+)", memory, re.M)[1])*1024
            available = int(re.search(r"^MemAvailable:\s+(\d+)", Path("/proc/meminfo").read_text(), re.M)[1])*1024
            minimum_available = min(minimum_available, available)
            if swap or rss > 12*1024**3 or available < 4*1024**3 or time.monotonic()-started > timeout:
                stopped = "resource/time guard"
                os.killpg(child.pid, signal.SIGTERM)
                try: child.wait(timeout=10)
                except subprocess.TimeoutExpired: os.killpg(child.pid, signal.SIGKILL)
                break
            time.sleep(0.5)
        code = child.wait()
    result = dict(command=command, exit=code, seconds=round(time.monotonic()-started, 3),
                  peak_rss=peak, stopped=stopped, log=str(log))
    result['external_guard'] = dict(schema=1, timeout_seconds=timeout,
        aggregate_rss_limit_bytes=12*1024**3, address_space_soft_bytes=12*1024**3,
        address_space_hard_bytes=12*1024**3, available_reserve_bytes=4*1024**3,
        swap_total_bytes=swap, sampling_interval_seconds=0.5, termination_grace_seconds=10,
        process_group=True, rlimit_as_applied=True, lean_num_threads=env.get('LEAN_NUM_THREADS'),
        minimum_available_bytes=minimum_available,
        runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print(json.dumps(result), flush=True)
    return result


def main():
    p = argparse.ArgumentParser(__doc__)
    p.add_argument("--boundary-only", action="store_true", help="emit the additive boundary corpus using an existing verified producer build")
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--bulk", type=Path, required=True)
    p.add_argument("--lean-bin", type=Path, required=True)
    a = p.parse_args()
    repo = a.repo.resolve(); bulk = a.bulk.resolve()
    if bulk == repo or repo in bulk.parents: p.error("H44 build must stay outside repository")
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(bulk/"lean-build"))
    env["PATH"] = str(a.lean_bin.resolve()) + os.pathsep + env["PATH"]
    if int(re.search(r"^SwapTotal:\s+(\d+)", Path("/proc/meminfo").read_text(), re.M)[1]):
        raise RuntimeError("no-swap prerequisite is not met")
    logs = bulk/"evidence/lean"; logs.mkdir(parents=True, exist_ok=True)
    versions = {name: subprocess.check_output([str(a.lean_bin/name), "--version"], text=True).strip()
                for name in ("lean", "lake")}
    if "version 4.24.0" not in versions["lean"]: raise RuntimeError("wrong repository toolchain")
    print(json.dumps(versions), flush=True)
    if a.boundary_only:
        build = json.loads((logs/"results.json").read_text())
        if not build["complete"] or any(row["exit"] != 0 or row["stopped"] for row in build["modules"]):
            raise RuntimeError("producer build incomplete")
        source_pins = json.loads((bulk/"evidence/producer-sources.json").read_text())["source_sha256"]
        for name, digest in source_pins.items():
            if hashlib.sha256((repo/name).read_bytes()).hexdigest() != digest:
                raise RuntimeError("producer source changed: " + name)
        driver = repo/"tests/h62/item3/g52-differential/BoundaryWitness.lean"
        output = bulk/"evidence/boundary-cases.jsonl"
        result = run([str(a.lean_bin/"lean"), "-j1", "--tstack=131072", "--run", str(driver)], repo, env, output)
        if result["exit"] != 0 or result["stopped"] is not None: raise SystemExit(result["exit"] or 1)
        records = [json.loads(line) for line in output.read_text().splitlines()]
        original = [json.loads(line) for line in (bulk/"evidence/typed-cases.jsonl").read_text().splitlines()]
        if len(records) != 480 or [row["index"] for row in records] != list(range(480)) or len({row["source"] for row in records}) != 480:
            raise RuntimeError("incomplete or duplicate boundary enumeration")
        if {row["source"] for row in records} & {row["source"] for row in original}:
            raise RuntimeError("boundary corpus pads original cases")
        binding = dict(driver=str(driver.relative_to(repo)), driver_sha256=hashlib.sha256(driver.read_bytes()).hexdigest(),
                       output_sha256=hashlib.sha256(output.read_bytes()).hexdigest(), case_count=480, original_overlap=0, bounded_run=result)
        (bulk/"evidence/boundary-generator.json").write_text(json.dumps(binding, indent=2)+"\n")
        raise SystemExit(0)
    seen = set(); order = []
    def visit(name):
        source = repo/(name.replace(".", "/")+".lean")
        if name in seen or not source.exists(): return
        seen.add(name)
        for imported in re.findall(r"^import\s+(\S+)", source.read_text(), re.M): visit(imported)
        order.append(name)
    visit("SolCases")
    sources = {name.replace(".", "/")+".lean": hashlib.sha256((repo/(name.replace(".", "/")+".lean")).read_bytes()).hexdigest()
               for name in order}
    (bulk/"evidence/producer-sources.json").write_text(json.dumps(dict(base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4", source_sha256=sources), indent=2)+"\n")
    results = []
    for name in order:
        source = repo/(name.replace(".", "/")+".lean")
        dest = bulk/"lean-build"/(name.replace(".", "/")+".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        result = run([str(a.lean_bin/"lean"), "-j1", "--tstack=131072", "-o", str(dest), str(source)],
                     repo, env, logs/(name+".log"))
        result["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        result["source"] = str(source.relative_to(repo))
        result["artifact_sha256"] = hashlib.sha256(dest.read_bytes()).hexdigest() if dest.exists() else None
        results.append(result)
        if result["exit"] != 0:
            (logs/"results.json").write_text(json.dumps(dict(versions=versions, modules=results, complete=False), indent=2)+"\n")
            raise SystemExit(result["exit"] or 1)
    result = run([str(a.lean_bin/"lean"), "-j1", "--tstack=131072", "--run", str(repo/"SolCases.lean"), "0"],
                 repo, env, bulk/"evidence/typed-cases.jsonl")
    results.append(result)
    (logs/"results.json").write_text(json.dumps(dict(versions=versions, modules=results, complete=result["exit"]==0), indent=2)+"\n")
    raise SystemExit(result["exit"])

if __name__ == "__main__": main()
