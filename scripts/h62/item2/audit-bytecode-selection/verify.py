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
from census import mask


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
                if not re.fullmatch(r"[A-Za-z_][\w.]*", module):
                    raise ValueError("unsupported import: " + module)
                dependency = module.replace(".", "/") + ".lean"
                if (repo / dependency).is_file():
                    visit(dependency)
                elif not module.startswith(("Lean", "Init", "Std")):
                    raise ValueError("unresolved import: " + module)
        active.remove(path)
        seen.add(path)
        order.append(path)

    for name in ["Witnesses", "LiteralSuccess"]:
        visit("tests/h62/item2/audit-bytecode-selection/" + name + ".lean")
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(build))
    records = []
    # A hard address-space cap in addition to Lean's allocation cap. The VM has
    # 16 GiB cgroup memory; poll for >=4 GiB remaining throughout every job.
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3))

    for index, path in enumerate(order):
        if memory_available() < 4 * 1024**3:
            raise SystemExit("STOP: less than 4 GiB reserve")
        output = build / Path(path).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(args.lean), "-j1", "-M8192", "--tstack=131072", "-o", str(output), path]
        logfile = evidence / (str(index).zfill(3) + "-" + Path(path).stem + ".log")
        start = time.monotonic()
        reason = None
        with logfile.open("w") as log:
            process = subprocess.Popen(command, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limits)
            while process.poll() is None:
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
                  "seconds": round(time.monotonic() - start, 3), "stop": reason, "log": str(logfile)}
        records.append(record)
        (evidence / "verification.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if process.returncode != 0 or reason:
            raise SystemExit(1)
    print("AUDIT_FILES_SOURCE_CHECK_PASS (not RUNTIME_GATE_PASS)", flush=True)


if __name__ == "__main__":
    main()
