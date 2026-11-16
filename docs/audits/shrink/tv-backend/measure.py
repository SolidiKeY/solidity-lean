#!/usr/bin/env python3
"""Serial root import/elaboration measurement of the affected library root, with cached imports.
Run after `lake build Solidity` and `restore-lake-artifacts.py`, under the
repository writer lock. Output must be outside the code checkout.
No systemd scope on the cloud VM (H232). Lean heap cap 12 GiB; VM has no swap.
The timing includes importing, trust-zero import loading (-t0), and root elaboration;
it is not an isolated kernel CPU profiler or a clean-build timing.
"""
import json, os, pathlib, resource, subprocess, sys, time
out = pathlib.Path(sys.argv[1]).resolve(); out.mkdir(parents=True, exist_ok=True)
root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
assert not out.is_relative_to(root), "evidence must be outside the checkout"
env = dict(os.environ, LEAN_NUM_THREADS="1")
cmd = ["lake", "env", "lean", "-j1", "-M12288", "-t0", "--tstack=131072", "Solidity.lean"]
start = time.monotonic()
with (out / "root.log").open("w") as log:
    result = subprocess.run(cmd, env=env, stdout=log, stderr=subprocess.STDOUT)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
record = {"command": cmd, "max_rss_kib": usage.ru_maxrss, "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime, "elapsed_seconds": time.monotonic() - start, "exit_code": result.returncode,
          "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
          "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
          "lake": subprocess.check_output(["lake", "--version"], text=True).strip()}
(out / "measurement.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record)); sys.exit(result.returncode)
