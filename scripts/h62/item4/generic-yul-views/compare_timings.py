#!/usr/bin/env python3
"""Validate recorded matched serial timings. Does not run Lean or prove closure."""
import argparse
from decimal import Decimal
import json
from pathlib import Path
import re
from statistics import median

PIN = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
HASHES = ("toolchain_archive_sha256", "cache_state_sha256", "resource_policy_sha256",
          "original_case_inventory_sha256", "frozen_statement_inventory_sha256")

def positive(value):
    n = Decimal(str(value))
    if not n.is_finite() or n <= 0: raise ValueError("timing must be positive and finite")
    return n

def validate(record):
    if record.get("schema_version") != 1: raise ValueError("unsupported schema")
    conditions = record["conditions"]
    for key in HASHES:
        if not re.fullmatch("[0-9a-f]{64}", conditions.get(key, "")):
            raise ValueError("missing or invalid condition hash: " + key)
    if conditions["toolchain_archive_sha256"] != PIN:
        raise ValueError("toolchain differs from coordinator pin")
    counts = [conditions.get(key) for key in ("lean_threads", "heavy_jobs")]
    args = conditions.get("lean_args")
    if any(type(count) is not int or count != 1 for count in counts):
        raise ValueError("serial Lean conditions require integer counts of one")
    if not isinstance(args, list) or any(not isinstance(arg, str) for arg in args):
        raise ValueError("Lean arguments must be a string list")
    if args.count("-j1") != 1 or any(
            (arg.startswith("-j") and arg != "-j1") or
            arg.startswith("--threads") for arg in args):
        raise ValueError("one unambiguous -j1 thread option required")
    modules = record["modules"]
    if not modules or len(modules) != len(set(modules)): raise ValueError("empty/duplicate module inventory")
    trials = record["trials"]
    if len(trials) < 3: raise ValueError("three matched trials required")
    for trial in trials:
        if trial["exit"] != 0 or trial.get("resource_stop") is not None:
            raise ValueError("failed/resource-stopped run cannot pass")
        if set(trial["module_seconds"]) != set(modules): raise ValueError("module coverage mismatch")
        elapsed = positive(trial["wall_seconds"])
        durations = [positive(x) for x in trial["module_seconds"].values()]
        if elapsed < sum(durations): raise ValueError("serial wall time omits recorded module work")
    return conditions

def compare(before, after):
    if validate(before) != validate(after): raise ValueError("conditions differ")
    if len(before["trials"]) != len(after["trials"]): raise ValueError("trial counts differ")
    if not set(before["modules"]).issubset(after["modules"]): raise ValueError("original module removed")
    rows = {}
    for module in [None] + before["modules"]:
        def duration(record):
            return median(positive(t["wall_seconds"] if module is None else t["module_seconds"][module]) for t in record["trials"])
        old, new = duration(before), duration(after)
        rows["aggregate" if module is None else "module:" + module] = dict(before=str(old),after=str(new),delta_percent=str((new-old)*100/old),stop=new > old*Decimal("1.10"))
    return dict(schema_version=1,status="TIMING_STOP" if any(r["stop"] for r in rows.values()) else "RECORDED_TIMING_ACCEPTANCE_PASS",
        boundary="Recorded timings only; caller must establish full affected closure, source/case/statement identities and actual cache/resource equivalence. Not proof acceptance.",
        rows=rows,added_modules=sorted(set(after["modules"])-set(before["modules"])))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("before",type=Path);ap.add_argument("after",type=Path)
    args=ap.parse_args()
    result=compare(json.loads(args.before.read_text()),json.loads(args.after.read_text()))
    print(json.dumps(result,indent=2))
    raise SystemExit(1 if result["status"]=="TIMING_STOP" else 0)

if __name__ == "__main__": main()
