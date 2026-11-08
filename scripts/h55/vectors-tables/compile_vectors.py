#!/usr/bin/env python3
"""Serial kernel check of emitted vector modules in an isolated output tree."""
import json
import os
import pathlib
import signal
import subprocess
import sys
import time
import vector_census as c

LEAN = "/workspace/.setup/tools/lean-4.24.0-linux/bin/lean"
OUT = pathlib.Path("/workspace/scratch/h55-vectors-tables/lean-objects")
GENERATED = pathlib.Path("/workspace/scratch/h55-vectors-tables/rendered")
DEPS = ["Solidity.Hash.CollisionBound", "Solidity.Keccak", "Solidity.Roadmap.Evm", "Solidity.Roadmap.Contracts", "Solidity.Yul.Builtins", "Solidity.Yul.Words"]

def available():
    with open("/proc/meminfo") as f:
        host = int(next(line.split()[1] for line in f if line.startswith("MemAvailable:")))
    limit = pathlib.Path("/sys/fs/cgroup/memory.max").read_text().strip()
    current = int(pathlib.Path("/sys/fs/cgroup/memory.current").read_text())
    return min(host, (int(limit) - current) // 1024) if limit != "max" else host

def run(source, target, root):
    if available() < 4194304: raise RuntimeError("preflight: less than 4 GiB available")
    target.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(OUT))
    cmd = [LEAN, "-j1", "--tstack=131072", "--root=" + str(root), "-o", str(target), str(source)]
    print("RUN", " ".join(cmd), flush=True)
    start = time.monotonic()
    with subprocess.Popen(cmd, cwd=c.ROOT, env=env, start_new_session=True) as proc:
        while proc.poll() is None:
            if available() < 4194304:
                os.killpg(proc.pid, signal.SIGTERM); proc.wait()
                raise RuntimeError("resource guard: less than 4 GiB available; stopped own Lean process")
            time.sleep(0.5)
        print(f"EXIT {proc.returncode} WALL {time.monotonic()-start:.3f}s", flush=True)
        if proc.returncode: raise RuntimeError("Lean check failed")

def authenticate_generated(root):
    """Reject unauthenticated or redirected sources before compiler side effects."""
    absolute = root.absolute()
    if any(path.is_symlink() for path in (absolute, *absolute.parents)):
        raise RuntimeError("generated source path contains a symlink")
    if not root.is_dir():
        raise RuntimeError("emit generated sources into a regular directory first")
    entries = list(root.rglob("*"))
    if any(path.is_symlink() for path in entries):
        raise RuntimeError("generated source tree contains a symlink")
    actual_paths = {path.relative_to(root).as_posix() for path in entries if path.is_file()}
    if actual_paths != set(c.PATHS):
        raise RuntimeError("generated source file inventory differs from frozen inventory")
    expected = json.loads(c.MANIFEST.read_text())
    if (expected["base"] != "4d3790eadb8a5212233bc7d5e345817476b2f590"
            or list(expected["files"]) != c.PATHS
            or c.census(root) != expected["files"]):
        raise RuntimeError("generated declarations or source bytes differ from frozen manifest")

def main():
    if OUT.exists(): raise RuntimeError("refusing to reuse existing object tree")
    authenticate_generated(GENERATED)
    OUT.mkdir(parents=True)
    for module in DEPS:
        path = pathlib.Path(*module.split("."))
        run(c.ROOT / path.with_suffix(".lean"), OUT / path.with_suffix(".olean"), c.ROOT)
    for name in c.PATHS:
        path = pathlib.Path(name)
        run(GENERATED / path, OUT / path.with_suffix(".olean"), GENERATED)
    print("PASS: six dependencies and nine emitted modules checked serially", flush=True)

if __name__ == "__main__":
    try: main()
    except (OSError, RuntimeError, ValueError) as e:
        print("FAIL:", e, file=sys.stderr); sys.exit(1)
