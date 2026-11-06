#!/usr/bin/env python3
"""Join every census row to actual mapped import blockers; never certify proofs."""
import argparse
import json
from functools import cache
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--census",type=Path,required=True)
p.add_argument("--probe",type=Path,required=True)
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
c=json.loads(a.census.read_text());probe=json.loads(a.probe.read_text())
rows={r["module"]:r for r in probe["results"]}
if len(rows)!=len(probe["results"]):raise SystemExit("duplicate probe result")
def module(path):return path.removeprefix("Bridge/").removesuffix(".lean").replace("/", ".")
expected={module(f["path"]) for f in c["files"]}
if set(probe["requested"])!=expected:raise SystemExit("probe does not cover the exact frozen map")
if not expected <= rows.keys():raise SystemExit("missing requested probe results")
@cache
def blockers(name):
    r=rows[name]
    if r["status"]=="pass":return set()
    if r["status"]=="fail" or r.get("reason"):return {name}
    deps=r.get("dependencies",[])
    if not deps:raise ValueError("unexplained blocked module: "+name)
    return set().union(*(blockers(d) for d in deps))
result=dict(base=c["base"], counts=c["counts"], proof_witnesses_verified=0,
            elaborated_signature_fidelity_verified=0,
            declaration_status="all source candidates retained; semantic classification pending",
            module_source_census=[dict(path=f["path"],sha256=f["sha256"],
                                      producer_attribution=f.get("producer_attribution"),
                                      source_summary=f.get("source_summary")) for f in c["files"]],
            direct_failures=[r for r in probe["results"] if r["status"]=="fail"],
            missing_external_dependencies=[r for r in probe["results"] if r.get("reason")],
            uncovered=[dict(name=r["name"],path=r["path"],line=r["line"],
                            visibility=r["visibility"],signature_sha256=r["signature_sha256"],
                            owner_evidence=r["owner_evidence"],
                            producer_attribution=r.get("producer_attribution"),
                            source_premise_bundle=r.get("source_premise_bundle"),
                            source_review=r.get("source_review"),
                            import_blockers=sorted(blockers(module(r["path"]))),
                            simultaneous_witness="pending", premise_classification="pending-elaboration")
                       for r in c["declarations"]])
a.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(dict(mapped_modules=len(expected),
                      mapped_pass=sum(rows[n]["status"]=="pass" for n in expected),
                      direct_compile_failures=len(result["direct_failures"]),
                      source_candidates=len(result["uncovered"]),verified_witnesses=0),sort_keys=True))
raise SystemExit(1 if any(rows[n]["status"]!="pass" for n in expected) else 0)
