#!/usr/bin/env python3
"""Offline analysis of saved timing evidence; never executes Lean or clears a hold."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics

THRESHOLD_PERCENT = 10
IDENTITY_FIELDS = ("lean_binary_sha256", "lake_binary_sha256", "toolchain_file_sha256",
                   "lean_version", "lake_version", "resource_flags")


def load_run(samples_path, receipt_path):
    samples = json.loads(samples_path.read_text())
    receipt = json.loads(receipt_path.read_text())
    log = Path(receipt["log"]).read_bytes()
    if hashlib.sha256(log).hexdigest() != receipt["log_sha256"]:
        raise ValueError("timing log hash mismatch")
    records = []
    for line in log.decode().splitlines():
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(record, dict) and "samples_seconds" in record:
            records.append(record)
    if records != [samples]:
        raise ValueError("samples differ from the unique hash-bound log record")
    times = samples["samples_seconds"]
    if len(times) != 5 or any(type(v) not in (int, float) or not math.isfinite(v) or v <= 0 for v in times):
        raise ValueError("expected five positive finite samples")
    median = statistics.median(times)
    if not math.isclose(median, samples["median_seconds"], rel_tol=1e-12):
        raise ValueError("recorded median disagrees with samples")
    if receipt["command"][receipt["command"].index("--output")+1] != str(samples_path):
        raise ValueError("receipt output path does not bind samples")
    for field in IDENTITY_FIELDS:
        if not receipt.get(field):
            raise ValueError("missing identity field: "+field)
    if receipt.get("stop_reason") is not None:
        raise ValueError("resource guard stop invalidates timing comparison")
    return samples, receipt


def analyze(before_path, after_path, before_receipt, after_receipt):
    before, br = load_run(before_path, before_receipt)
    after, ar = load_run(after_path, after_receipt)
    canonical = ["python3", "scripts/h62/item2/audit-readonly-calls/measure.py", "--output"]
    if br["command"] != canonical+[str(before_path)] or ar["command"] != canonical+[str(after_path), "--compare", str(before_path)]:
        raise ValueError("noncanonical measurement command or baseline binding")
    for field in ("command", "file_sha256"):
        if before[field] != after[field]:
            raise ValueError("comparison input mismatch: "+field)
    for field in IDENTITY_FIELDS:
        if br[field] != ar[field]:
            raise ValueError("comparison identity mismatch: "+field)
    if (br["child_exit"], br["gate_exit"], br["status"]) != (0, 0, "pass"):
        raise ValueError("baseline receipt is not successful")
    delta = 100*(after["median_seconds"]/before["median_seconds"]-1)
    if not math.isclose(delta, after["delta_percent"], rel_tol=1e-12, abs_tol=1e-12):
        raise ValueError("recorded delta disagrees with samples")
    stopped = delta > THRESHOLD_PERCENT
    expected = (1, 1, "fail") if stopped else (0, 0, "pass")
    if (ar["child_exit"], ar["gate_exit"], ar["status"]) != expected:
        raise ValueError("receipt outcome disagrees with timing threshold")
    if stopped and "SLOWDOWN_STOP" not in Path(ar["log"]).read_text():
        raise ValueError("failed timing log lacks stop marker")
    def describe(row):
        values = row["samples_seconds"]
        return {"samples_seconds": values, "median_seconds": row["median_seconds"],
                "first_two_median_seconds": statistics.median(values[:2]),
                "last_three_median_seconds": statistics.median(values[2:]),
                "range_seconds": [min(values), max(values)]}
    return {"schema": 1, "recorded_timing_outcome": "stop" if stopped else "within-threshold",
            "threshold_percent": THRESHOLD_PERCENT, "delta_percent": delta,
            "before": describe(before), "after": describe(after),
            "identities_match": True, "cause": "unestablished",
            "missing_comparability_evidence": ["per-sample CPU and throttling deltas",
                "per-sample cache state", "per-sample concurrent workload"],
            "boundary": "External offline evidence analysis only. Does not run Lean, establish code causality, clear any hold, authorize a rerun or prove a theorem.",
            "inputs_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in (before_path, after_path, before_receipt, after_receipt)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("before", "after", "before-receipt", "after-receipt", "output"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    result = analyze(args.before, args.after, args.before_receipt, args.after_receipt)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print("OFFLINE_TIMING_EVIDENCE_VALIDATED recorded_outcome="+result["recorded_timing_outcome"]+" cause=unestablished; no hold cleared")


if __name__ == "__main__":
    main()
