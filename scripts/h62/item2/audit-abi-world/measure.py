#!/usr/bin/env python3
"""Matched warm before/after diagnostics; fail above the authorized 10% limit."""
import argparse
import hashlib
import json
from pathlib import Path
import statistics
import subprocess
import sys

root=Path(__file__).resolve().parents[4]
parser=argparse.ArgumentParser()
parser.add_argument("phase",choices=["before","after"])
parser.add_argument("--evidence",type=Path,required=True)
args=parser.parse_args()
assert not args.evidence.resolve().is_relative_to(root)
folder=args.evidence/("timings-"+args.phase);folder.mkdir(exist_ok=True)
module="tests/h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean"
params=json.dumps(dict(file_path=module,interactive=False,timeout_s=120))
command=[".venv/bin/python","-B","scripts/h62/item2/audit-abi-world/mcp_call.py","lean_diagnostic_messages",params]
samples=[];support=None
for n in range(8):
    name="warmup" if n==0 else str(n)
    proof=folder/(name+".json");resource=folder/(name+"-resource.json")
    with proof.open("w") as stdout,(folder/(name+".stderr")).open("w") as stderr:
        subprocess.run([sys.executable,"-B","scripts/h62/item2/audit-abi-world/bounded.py","--receipt",str(resource),"--timeout","180","--output",str(proof),"--"]+command,cwd=root,stdout=stdout,stderr=stderr,check=True)
    p=json.loads(proof.read_text());r=json.loads(resource.read_text());audit=p["_audit"]
    assert p["structuredContent"]["result"]["success"] is True
    assert r["reason"] is None and r["exit_code"]==0 and r["cleanup_complete"] is True
    current=dict(source_sha256=audit["source_sha256"],support=audit["support_before"],
                 version=audit["lean_version"],guard_sha256=r["guard_sha256"],
                 reserve=r["reserve_bytes"],cap=r["task_cap_bytes"],threads=r["lean_num_threads"])
    if support is None:support=current
    assert current==support,"checking tree/config/resources changed during samples"
    if n:samples.append(audit["elapsed_seconds"])
report=dict(phase=args.phase,module=module,warmup_discarded=True,samples=samples,
            median_seconds=statistics.median(samples),identity=support)
if args.phase=="after":
    before=json.loads((args.evidence/"timings-before.json").read_text())
    assert before["identity"]==support,"before/after identities differ"
    report["before_median_seconds"]=before["median_seconds"]
    report["delta_percent"]=(report["median_seconds"]/before["median_seconds"]-1)*100
    report["within_limit"]=report["delta_percent"]<=10
output=args.evidence/("timings-"+args.phase+".json")
output.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:v for k,v in report.items() if k!="identity"}))
if report.get("within_limit") is False:raise SystemExit(2)
