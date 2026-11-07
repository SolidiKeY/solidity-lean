#!/usr/bin/env python3
"""Serial source-only Lean fallback when no per-file Lean MCP is exposed.

Run under the repository writer lock. This is a bounded audit-file check,
not a substitute for the required final run-lean.sh gate. No Lake artifact
cache is read, no source options are changed, and all products stay off Git.
"""
import argparse
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time
from census import BASE, mask
import hashlib

DEFAULT_ROOTS = ["tests/h62/item2/audit-bytecode-selection/" + name + ".lean"
                 for name in ["Witnesses", "LiteralSuccess", "RuntimePremiseWitness", "ValueGateSuccess", "HypothesisDomains", "BoolBindingSuccess", "FailurePathsWitnesses"]]


def import_path(module):
    part = r"(?:[A-Za-z_]\w*|«[^»/.\s]+»)"
    if not re.fullmatch(part + r"(?:\." + part + r")*", module):
        raise ValueError("unsupported import: " + module)
    return "/".join(segment[1:-1] if segment.startswith("«") else segment for segment in module.split(".")) + ".lean"


def file_sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def memory_available():
    host = next(int(line.split()[1]) * 1024 for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:"))
    cap = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    used = int(Path("/sys/fs/cgroup/memory.current").read_text())
    return min(host, int(cap) - used) if cap != "max" else host


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--root", action="append", help="repo-relative Lean root; repeat to extend the audit closure")
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    if len(Path("/proc/swaps").read_text().splitlines()) != 1:
        raise SystemExit("STOP: swap enabled")
    evidence.mkdir(parents=True, exist_ok=True)
    build = evidence / "lean"
    if build.exists():
        raise SystemExit("STOP: verification build directory must be fresh")
    build.mkdir()
    seen, active, order = set(), set(), []

    def visit(path):
        if path in active:
            raise ValueError("dependency cycle: " + path)
        if path in seen:
            return
        active.add(path)
        clean = mask((repo / path).read_text())
        for imports in re.findall(r"(?m)^import[ \t]+([^\n]+)", clean):
            for module in imports.split():
                dependency = import_path(module)
                if (repo / dependency).is_file():
                    visit(dependency)
                elif not module.startswith(("Lean", "Init", "Std")):
                    raise ValueError("unresolved import: " + module)
        active.remove(path)
        seen.add(path)
        order.append(path)

    roots = args.root or DEFAULT_ROOTS
    for root in roots:
        path = (repo / root).resolve()
        if not path.is_relative_to(repo):
            raise ValueError("root escapes repository: " + root)
        visit(str(path.relative_to(repo)))
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(build), MIMALLOC_PURGE_DELAY="0")
    records = []
    # The VM already has a hard cgroup memory cap. Bound Lean's heap and
    # continuously preserve 4 GiB of physical/cgroup headroom. Do not impose a
    # virtual-address cap: reserved address ranges are not resident memory.
    cap = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    if cap == "max" or int(cap) > 16 * 1024**3:
        raise SystemExit("STOP: expected existing <=16 GiB VM memory cap")

    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    for index, path in enumerate(order):
        if memory_available() < 4 * 1024**3:
            raise SystemExit("STOP: less than 4 GiB reserve")
        source_bytes = (repo / path).read_bytes()
        source_sha256 = hashlib.sha256(source_bytes).hexdigest()
        if path.startswith("Solidity/") and source_bytes != subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo):
            raise SystemExit("STOP: original source differs from frozen base: " + path)
        output = build / Path(path).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(args.lean), "-j1", "-M8192", "--tstack=131072", "-o", str(output), path]
        logfile = evidence / (str(index).zfill(3) + "-" + Path(path).stem + ".log")
        start = time.monotonic()
        reason = None
        peak_rss_kib, peak_virtual_kib = 0, 0
        with logfile.open("w") as log:
            process = subprocess.Popen(command, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limits)
            while process.poll() is None:
                try:
                    status = Path(f"/proc/{process.pid}/status").read_text()
                    for line in status.splitlines():
                        if line.startswith("VmRSS:"):
                            peak_rss_kib = max(peak_rss_kib, int(line.split()[1]))
                        elif line.startswith("VmSize:"):
                            peak_virtual_kib = max(peak_virtual_kib, int(line.split()[1]))
                except FileNotFoundError:
                    pass
                if memory_available() < 4 * 1024**3:
                    reason = "resource-reserve"
                if time.monotonic() - start > 300:
                    reason = "300s-timeout"
                if reason:
                    process.terminate()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
                    break
                time.sleep(0.2)
        record = {"path": path, "command": command, "exit": process.returncode,
                  "seconds": round(time.monotonic() - start, 3), "stop": reason, "log": str(logfile),
                  "peak_rss_kib": peak_rss_kib, "peak_virtual_kib": peak_virtual_kib,
                  "source_sha256": source_sha256,
                  "source_unchanged_during_check": file_sha256(repo / path) == source_sha256,
                  "output_sha256": file_sha256(output) if process.returncode == 0 and output.exists() else None}
        records.append(record)
        (evidence / "verification.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if process.returncode != 0 or reason or not record["source_unchanged_during_check"] or record["output_sha256"] is None:
            raise SystemExit(1)
    print("AUDIT_FILES_SOURCE_CHECK_PASS (not RUNTIME_GATE_PASS)", flush=True)


if __name__ == "__main__":
    main()
