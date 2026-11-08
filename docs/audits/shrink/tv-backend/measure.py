#!/usr/bin/env python3
"""Serial kernel recheck of the affected library root, with cached imports.
Run after `lake build Solidity` and `restore-lake-artifacts.py`, under the
repository writer lock. Output must be outside the code checkout.
No systemd scope on the cloud VM (H232). Lean heap cap 12 GiB; VM has no swap.
The timing includes importing, kernel rechecking (-t0), and root elaboration;
it is not an isolated kernel CPU profiler or a clean-build timing.
"""
import json, os, pathlib, subprocess, sys, time
out = pathlib.Path(sys.argv[1]).resolve(); out.mkdir(parents=True, exist_ok=True)
root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
assert not out.is_relative_to(root), "evidence must be outside the checkout"
env = dict(os.environ, LEAN_NUM_THREADS="1")
cmd = ["lake", "env", "lean", "-j1", "-M12288", "-t0", "--tstack=131072", "Solidity.lean"]
start = time.monotonic()
with (out / "root.log").open("w") as log:
    result = subprocess.run(["/usr/bin/time", "-v", "-o", str(out / "resources.txt"), *cmd], env=env, stdout=log, stderr=subprocess.STDOUT)
record = {"command": cmd, "elapsed_seconds": time.monotonic() - start, "exit_code": result.returncode,
          "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
          "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
          "lake": subprocess.check_output(["lake", "--version"], text=True).strip()}
(out / "measurement.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record)); sys.exit(result.returncode)
