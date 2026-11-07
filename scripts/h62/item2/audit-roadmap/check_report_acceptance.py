#!/usr/bin/env python3
"""Integration controls: real evidence passes; stale/failed proof evidence fails.
Negative fixtures are explicitly synthetic and stay off git. No Lean is run.
"""
import argparse
import copy
import json
import pathlib
import subprocess
import sys

ap = argparse.ArgumentParser()
ap.add_argument("--evidence", required=True, type=pathlib.Path)
args = ap.parse_args()
ev = args.evidence.resolve()
root = pathlib.Path(__file__).resolve().parents[4]
fixtures = ev/"report-acceptance"
fixtures.mkdir(exist_ok=True)
base = json.loads((ev/"lean-evm-h69-final/results.json").read_text())
context = ev/"lean-context-h69-final/results.json"
report_script = root/"scripts/h62/item2/audit-roadmap/audit_report.py"
results = []
for name, mutation in (
    ("valid", None),
    ("stale-dependency", ("Solidity/Keccak.lean", "source_sha256", "0"*64)),
    ("stale-helper", ("tests/h62/item2/audit-roadmap/EvmWitnesses.lean", "source_sha256", "0"*64)),
    ("failed-check", ("tests/h62/item2/audit-roadmap/EvmWitnesses.lean", "exit", 1)),
    ("changed-compiler", ("lean-version", "compiler_sha256", "0"*64)),
):
    rows = copy.deepcopy(base)
    if mutation:
        label, key, value = mutation
        next(r for r in rows if r["label"] == label)[key] = value
    fixture = fixtures/(name+".synthetic-results.json")
    fixture.write_text(json.dumps(rows,indent=2)+"\n")
    cmd = [sys.executable,str(report_script),"--census",str(ev/"census/census.json"),
        "--results",str(fixture),"--results",str(context),"--output",str(fixtures/name)]
    run = subprocess.run(cmd,cwd=root,text=True,capture_output=True)
    (fixtures/(name+".log")).write_text(run.stdout+run.stderr)
    expected = run.returncode == 0 if mutation is None else run.returncode != 0
    if mutation is None and expected:
        summary = json.loads((fixtures/name/"audit-census.json").read_text())["summary"]
        expected = summary["witnessed"] == 17 and summary["uncovered"] == 334
    results.append(dict(case=name,command=cmd,exit=run.returncode,control_pass=expected,
        boundary="Synthetic negative evidence is not a proof result"))
    if not expected:
        raise SystemExit("acceptance control failed: "+name)
(ev/"report-acceptance.json").write_text(json.dumps(results,indent=2)+"\n")
print("PASS: real evidence accepted; stale dependency/helper/compiler and failed check rejected")
