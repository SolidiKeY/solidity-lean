#!/usr/bin/env python3
"""Serial isolated Lean checks of unchanged core imports and additive audit files.
No .lake or old-toolchain cache reuse. Results are off Git; this focused check
does not replace run-lean.sh or certify unbuilt dependencies/Bridge packages.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("files", type=Path, nargs="+")
    args = p.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    lib = args.output / "lib"
    lib.mkdir(exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(lib),
               XDG_CACHE_HOME=str(args.output / "cache"))
    results = []
    visited = set()
    reserve = 4 * 1024**3
    def available_memory():
        host = int(next(x.split()[1] for x in open("/proc/meminfo") if x.startswith("MemAvailable:"))) * 1024
        maximum = Path("/sys/fs/cgroup/memory.max").read_text().strip()
        current = int(Path("/sys/fs/cgroup/memory.current").read_text())
        return min(host, int(maximum) - current) if maximum != "max" else host

    def compile_file(path):
        if path in visited: return True
        visited.add(path)
        source = ROOT / path
        text = source.read_text()
        if str(path).startswith("Solidity/"):
            frozen = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)
            if frozen != source.read_bytes(): raise RuntimeError(f"frozen source differs: {path}")
        for line in text.splitlines():
            if line.startswith("import "):
                for name in line[7:].split():
                    if name.startswith("--"): break
                    if name.startswith("Solidity."):
                        dep = Path(name.replace(".", "/") + ".lean")
                        if not compile_file(dep): return False
                    elif not name.startswith(("Lean", "Std", "Init")):
                        raise RuntimeError(f"external import requires owner toolchain/package: {name}")
        available = available_memory()
        swap = int(next(x.split()[1] for x in open("/proc/meminfo") if x.startswith("SwapTotal:")))
        cap = min(12 * 1024**3, available - reserve - 256 * 1024**2)
        if cap < 1024**3 or swap:
            raise RuntimeError(f"resource guard: available={available}, swap={swap}")
        artifact = lib / path.with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        log = args.output / (str(path).replace("/", "__") + ".log")
        cmd = [str(args.lean), "-j1", "--tstack=131072", "-o", str(artifact), str(path)]
        start = time.monotonic()
        minimum_available = available
        outcome = "exit"
        def bound(): resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        with log.open("w") as f:
            process = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT,
                                       preexec_fn=bound, start_new_session=True)
            while process.poll() is None:
                free = available_memory()
                minimum_available = min(free, minimum_available)
                if free < reserve or time.monotonic() - start > 300:
                    outcome = "reserve-stop" if free < reserve else "timeout"
                    os.killpg(process.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            code = process.wait()
        record = {"file": str(path), "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "command": cmd, "exit": code, "outcome": outcome, "wall_seconds": time.monotonic()-start,
                  "log": str(log), "virtual_memory_cap": cap, "reserve": reserve,
                  "minimum_available": minimum_available,
                  "available_before": available, "swap_total": swap}
        results.append(record)
        (args.output / "checks.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        return code == 0 and outcome == "exit"
    for path in args.files:
        if not compile_file(path): return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
