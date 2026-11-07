#!/usr/bin/env python3
"""Build frozen static-checker controls, reusing only hash-validated v4.24 artifacts."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
EVIDENCE = Path("/workspace/h62-audit-typing-evidence/v4.24.0")
LEAN = Path("/workspace/.setup/tools/lean-4.24.0-linux/bin/lean")

def main():
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lockpath.parent.mkdir(exist_ok=True)
    with lockpath.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert (ROOT/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.24.0"
        versions = subprocess.check_output([str(LEAN), "--version"], text=True)
        assert "version 4.24.0," in versions
        lake_version = subprocess.check_output([str(LEAN.with_name("lake")), "--version"], text=True)
        (EVIDENCE/"versions.txt").write_text(versions+lake_version)
        ordered = []
        seen = set()
        def visit(module):
            if module in seen:
                return
            seen.add(module)
            path = module.replace(".", "/")+".lean"
            frozen = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)
            assert (ROOT/path).read_bytes() == frozen, f"Frozen source differs: {path}"
            for imports in re.findall(r"^import (.+)$", frozen.decode(), re.M):
                for dep in imports.split():
                    if dep.startswith("Solidity."):
                        visit(dep)
            ordered.append(path)
        visit("Solidity.Frontend.Static.Certificates")
        visit("Solidity.Frontend.Static.UnitsExamples")
        (EVIDENCE/"frontend-units-build-plan.json").write_text(json.dumps(ordered, indent=2)+"\n")
        env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(EVIDENCE/"olean"))
        prior_path = EVIDENCE/"typing-values-build-results.json"
        prior = {r["command"][-1]: r for r in json.loads(prior_path.read_text())}
        results = []
        for path in ordered:
            cap = int(Path("/sys/fs/cgroup/memory.max").read_text())
            current = int(Path("/sys/fs/cgroup/memory.current").read_text())
            assert cap-current >= 4*1024**3, "Insufficient reserve"
            output = EVIDENCE/"olean"/Path(path).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            log = EVIDENCE/(path.replace("/", "_")+".build.log")
            cmd = [str(LEAN), "-j1", "--memory=11000", "--tstack=131072", "-o", str(output), path]
            old = prior.get(path)
            if old and old["exit"] == 0 and old["stopped"] is None and old["command"][0] == str(LEAN) and output.exists():
                if (hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == old["source_sha256"]
                    and hashlib.sha256(output.read_bytes()).hexdigest() == old["olean_sha256"]):
                    results.append(dict(old, reused=True, seconds=0.0))
                    (EVIDENCE/"frontend-units-build-results.json").write_text(json.dumps(results, indent=2)+"\n")
                    print(path, "hash-validated reuse", flush=True)
                    continue
            start = time.monotonic()
            stopped = None
            with log.open("w") as stream:
                process = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
                while process.poll() is None:
                    current = int(Path("/sys/fs/cgroup/memory.current").read_text())
                    if cap-current < 4*1024**3:
                        stopped = "4 GiB reserve guard"
                    if time.monotonic()-start > 300:
                        stopped = "300 second external process limit"
                    if stopped:
                        process.terminate()
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            process.kill()
                            process.wait()
                        break
                    time.sleep(0.1)
            result = dict(command=cmd, exit=process.returncode, seconds=time.monotonic()-start,
                stopped=stopped, log=str(log),
                source_sha256=hashlib.sha256((ROOT/path).read_bytes()).hexdigest(),
                olean_sha256=hashlib.sha256(output.read_bytes()).hexdigest() if process.returncode == 0 and not stopped else None)
            results.append(result)
            (EVIDENCE/"frontend-units-build-results.json").write_text(json.dumps(results, indent=2)+"\n")
            print(path, process.returncode, stopped, flush=True)
            if stopped or process.returncode:
                raise SystemExit(process.returncode or 1)
        print("Static frontend frozen dependency build passed; controls pending")

if __name__ == "__main__":
    main()
