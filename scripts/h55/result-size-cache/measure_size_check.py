#!/usr/bin/env python3
"""Measure H44 size-gate regressions without weakening JSON/history rejection.

Uses one persistent disposable Git fixture, never the production checkout's data.
Seven warmed invocations record output identity, wall time and wait4 maximum RSS.
This is an external performance control, not a trusted-base integration gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]


def run(args):
    fixture, output = args.fixture.resolve(), args.output.resolve()
    if fixture.is_relative_to(ROOT) or output.is_relative_to(ROOT) or output.is_relative_to(fixture):
        raise ValueError("fixture and evidence must be separate and outside the checkout")
    body = b"# measured reviewable source\n" * 8000
    digest = hashlib.sha256(body).hexdigest()
    if not fixture.exists():
        fixture.mkdir(parents=True)
        def git(*cmd):
            return subprocess.check_output(["git", *cmd], cwd=fixture)
        git("init", "-q")
        git("config", "user.email", "fixture@example.invalid")
        git("config", "user.name", "H55 fixture")
        approval = fixture / "scripts/h55/result-size-cache/approved-source.json"
        approval.parent.mkdir(parents=True)
        approval.write_text(json.dumps({"large.py": digest}) + "\n")
        git("add", ".")
        git("commit", "-qm", "synthetic trusted approval")
        (fixture / "large.py").write_bytes(body)
    base = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=fixture, text=True).strip()
    if (fixture / "large.py").read_bytes() != body:
        raise ValueError("measurement fixture changed")
    command = [sys.executable, "-B", str(args.script.resolve()), base]
    records = []
    output.parent.mkdir(parents=True, exist_ok=True)
    for index in range(8):
        log = output.with_name(output.stem + f"-{index}.log")
        started = time.monotonic()
        with log.open("wb") as stream:
            process = subprocess.Popen(command, cwd=fixture, stdout=stream, stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
        seconds = time.monotonic() - started
        if process.returncode:
            raise RuntimeError(f"measurement failed: {log}")
        records.append({"seconds": seconds, "maxRssKiB": usage.ru_maxrss,
                        "outputSha256": hashlib.sha256(log.read_bytes()).hexdigest(), "log": str(log)})
    result = {"command": command, "fixture": str(fixture), "base": base,
              "scriptSha256": hashlib.sha256(args.script.read_bytes()).hexdigest(),
              "warmup": records[0], "runs": records[1:],
              "medianSeconds": statistics.median(row["seconds"] for row in records[1:]),
              "rssBoundary": "wait4 per invocation; kernel child usage can include waited Git descendants"}
    if len({row["outputSha256"] for row in records}) != 1:
        raise RuntimeError("measurement output changed")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"medianSeconds": result["medianSeconds"], "output": str(output)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--script", type=Path, default=Path(__file__).with_name("size_check.py"))
    run(parser.parse_args())
