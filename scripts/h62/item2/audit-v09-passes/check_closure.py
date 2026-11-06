#!/usr/bin/env python3
"""Serial, isolated-cache Lean dependency check; never edits producer sources.

Fallback for absent Lean MCP. This does not replace run-lean.sh final gates.
All source inputs must match the assigned frozen base, including dependencies.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time
from census import masked

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
PIN_SHA = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
GiB = 1024 ** 3


def available():
    info = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    headroom = int(info["MemAvailable"].split()[0]) * 1024
    # The VM is cgroup-v2 bounded. Include every visible ancestor limit;
    # host MemAvailable alone can substantially overstate usable memory.
    memberships = Path("/proc/self/cgroup").read_text().splitlines()
    membership = next((line[3:] for line in memberships if line.startswith("0::")), None)
    if membership is None:
        raise RuntimeError("cgroup-v2 membership unavailable; refusing unchecked memory guard")
    cgroot = Path("/sys/fs/cgroup")
    current = cgroot / membership.lstrip("/")
    found_limit = False
    while current == cgroot or cgroot in current.parents:
        limitfile = current / "memory.max"
        if limitfile.exists():
            limit = limitfile.read_text().strip()
            if limit != "max":
                used = int((current / "memory.current").read_text())
                headroom = min(headroom, int(limit) - used)
                found_limit = True
        if current == cgroot:
            break
        current = current.parent
    if not found_limit:
        raise RuntimeError("no visible hard cgroup memory limit; refusing unchecked run")
    return headroom


def bounded():
    resource.setrlimit(resource.RLIMIT_AS, (12 * GiB, 12 * GiB))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[4]
    args.output = args.output.resolve()
    args.toolchain = args.toolchain.resolve()
    archive = args.toolchain.parent / "lean-4.35.0-linux.tar.zst"
    if hashlib.file_digest(archive.open("rb"), "sha256").hexdigest() != PIN_SHA:
        raise SystemExit("pinned archive SHA256 mismatch")
    lean = args.toolchain / "bin/lean"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if "version 4.35.0," not in version:
        raise SystemExit("wrong Lean version")
    if len(Path("/proc/swaps").read_text().splitlines()) > 1:
        raise SystemExit("swap enabled: refusing heavy check")
    args.output.mkdir(parents=True, exist_ok=True)
    cache = args.output / "olean"
    cache.mkdir(exist_ok=True)
    seen, order = set(), []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        path = Path(module.replace(".", "/") + ".lean")
        if not (root / path).is_file():
            if module.startswith(("Lean", "Std", "Init")):
                return
            raise ValueError(f"missing source {module}")
        data = (root / path).read_bytes()
        frozen = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root)
        if data != frozen:
            raise ValueError(f"changed frozen input {path}")
        for line in masked(data.decode()).splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    visit(dep)
        order.append((module, path, hashlib.sha256(data).hexdigest()))

    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(cache))
    report = {"base": BASE, "toolchain": version, "archive_sha256": PIN_SHA,
              "cache": str(cache), "targets": args.modules, "records": [],
              "boundary": "Dependency baseline check only; not full affected/final gates."}
    lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        report["git_status_under_lock"] = subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=root, text=True)
        for module in args.modules:
            visit(module)
        report["initial_effective_available_bytes"] = available()
        report["reserve_bytes"] = 4 * GiB
        report["address_space_cap_bytes"] = 12 * GiB
        for module, path, source_sha in order:
            if available() < 4 * GiB:
                raise SystemExit("less than 4GiB available reserve")
            out = cache / path.with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            logfile = args.output / (module + ".log")
            command = [str(lean), "-j1", "--tstack=131072", "-o", str(out), str(path)]
            start = time.monotonic()
            stopped = None
            with logfile.open("w") as log:
                child = subprocess.Popen(command, cwd=root, env=env, stdout=log,
                                         stderr=subprocess.STDOUT, start_new_session=True,
                                         preexec_fn=bounded)
                while child.poll() is None:
                    if available() < 4 * GiB:
                        stopped = "available-memory reserve"
                    elif time.monotonic() - start > 300:
                        stopped = "300-second per-file budget"
                    if stopped:
                        os.killpg(child.pid, signal.SIGKILL)
                        child.wait()
                        break
                    time.sleep(0.2)
            record = {"module": module, "source_sha256": source_sha, "command": command,
                      "exit": child.returncode, "seconds": round(time.monotonic() - start, 3),
                      "log": str(logfile), "resource_stop": stopped}
            report["records"].append(record)
            (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
            print(json.dumps(record), flush=True)
            if child.returncode:
                raise SystemExit(1)
    print("CLOSURE_BASELINE_PASS: final gates remain required")


if __name__ == "__main__":
    main()
