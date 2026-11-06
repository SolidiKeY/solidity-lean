#!/usr/bin/env python3
"""Collect non-Lean acceptance evidence; failed gates remain failed."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import census


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--ownership", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    repo, output = a.repo.resolve(), a.output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    scripts = "scripts/h62/item2/audit-g25-scalar-lowering/"
    commands = [
      [sys.executable,scripts+"census_tests.py"],
      [sys.executable,scripts+"runner_tests.py"],
      [sys.executable,scripts+"inventory_tests.py"],
      [sys.executable,scripts+"gate_tests.py"],
      [sys.executable,scripts+"generate_success_axioms.py","--check"],
      [sys.executable,scripts+"success_evidence.py"],
      [sys.executable,scripts+"census.py","--ownership",str(a.ownership),"--output",str(output/"source-census.json")],
      [sys.executable,scripts+"inventory.py","--source",str(output/"source-census.json"),"--kernel",str(output/"kernel-census-v424.json"),"--schemas",str(output/"premise-structures-v424.json"),"--output",str(output/"statement-inventory-v424.json")],
      [sys.executable,scripts+"verify_census.py","--ownership",str(a.ownership),"--census",str(output/"source-census.json"),"--kernel",str(output/"kernel-census-v424.json"),"--verification",str(output/"witness-verification-v424.json"),"--cache",str(output.parent/"audit-v424"),"--toolchain","/workspace/.setup/tools/lean-4.24.0-linux","--output",str(output/"coverage-ledger.json")],
      ["git","diff","--check",census.BASE],
      ["git","merge-base","--is-ancestor",census.BASE,"origin/master"],
      ["node","scripts/check-layers.mjs"],
      ["bash","scripts/coord-tools/register.sh","--check"],
      ["bash","scripts/coord-tools/fragments.sh","--check"],
      ["bash","scripts/check-doc-paths.sh"],
    ]
    results=[]
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1")
    for index,cmd in enumerate(commands):
        log=output/(f"acceptance-{index:02d}.log")
        start=time.monotonic()
        with log.open("w") as stream:
            result=subprocess.run(cmd,cwd=repo,env=env,stdout=stream,stderr=subprocess.STDOUT)
        row={"command":cmd,"exit":result.returncode,"status":"pass" if result.returncode==0 else "fail",
             "seconds":round(time.monotonic()-start,3),"log":str(log),"log_sha256":census.digest(log.read_bytes())}
        results.append(row); print(json.dumps(row),flush=True)
    changed=subprocess.run(["git","diff","--name-only",census.BASE],cwd=repo,check=True,stdout=subprocess.PIPE,text=True).stdout.splitlines()
    untracked=subprocess.run(["git","ls-files","--others","--exclude-standard"],cwd=repo,check=True,stdout=subprocess.PIPE,text=True).stdout.splitlines()
    changed=sorted(set(changed+untracked))
    allowed=("tests/h62/item2/audit-g25-scalar-lowering/","scripts/h62/item2/audit-g25-scalar-lowering/")
    violations=[name for name in changed if not name.startswith(allowed) and name!="docs/feature-work/h62-2-audit-g25-scalar-lowering.md"]
    forbidden=[]
    for path in (repo/allowed[0]).rglob("*.lean"):
        for match in re.finditer(r"\b(?:sorry|axiom|native_decide|maxHeartbeats)\b",census.mask(path.read_text())):
            forbidden.append({"path":str(path.relative_to(repo)),"token":match.group()})
    report={"commands":results,"changed_paths":changed,"scope_violations":violations,
            "forbidden_lean_tokens":forbidden,"ownership_sha256":census.digest(a.ownership.read_bytes()),
            "proof_boundary":"No Lean proof or final-gate credit from these external checks."}
    (output/"acceptance-results.json").write_text(json.dumps(report,indent=2)+"\n")
    if any(r["exit"] for r in results) or violations or forbidden: raise SystemExit(1)

if __name__ == "__main__": main()
