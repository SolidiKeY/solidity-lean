#!/usr/bin/env python3
"""Bounded serial kernel replay. Arguments: VIEW IMPORTS SELECTED COUNT OUTDIR.
VIEW is a complete matched artifact view. Expected counts prevent vacuous success.
Imports and scan overhead are outside the measured individual kernel calls.
"""
import json, os, pathlib, resource, subprocess, sys, time
view, imports, selected, count, output = sys.argv[1:]
out = pathlib.Path(output).resolve(); out.mkdir(parents=True, exist_ok=True)
root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
assert not out.is_relative_to(root)
cmd = ["lean", "-j1", "-M12288", "--run", str(pathlib.Path(__file__).with_name("Replay.lean")), imports, selected, str(out / "replay.json"), count]
env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(pathlib.Path(view).resolve()))
started = time.monotonic()
with (out / "replay.log").open("w") as log:
    result = subprocess.run(cmd, env=env, stdout=log, stderr=subprocess.STDOUT)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
record = {"command": cmd, "elapsed_seconds": time.monotonic() - started, "exit_code": result.returncode, "max_rss_kib": usage.ru_maxrss}
(out / "process.json").write_text(json.dumps(record, indent=2) + "\n")
if result.returncode: sys.exit(result.returncode)
record = json.loads((out / "replay.json").read_text())
assert record["checked_theorems"] == int(count) and record["negative_control_rejected"]
print("KERNEL_REPLAY_COUNT_PASS", count, record["kernel_call_nanoseconds"])
