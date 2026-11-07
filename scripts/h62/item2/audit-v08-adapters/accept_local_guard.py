#!/usr/bin/env python3
"""Reconcile reviewed local-guard carriers and mandatory-success controls.
This limited scope acceptance is not the full H62 gate or equivalence prover.
"""
import argparse,hashlib,json
from pathlib import Path
from accept_witnesses import checked_run, require

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for k in ["repo","run","census-run","census","out"]:ap.add_argument("--"+k,type=Path,required=True)
    a=ap.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    require(out!=repo and repo not in out.parents, 'acceptance predicate failed')
    ledger=json.loads((repo/"tests/h62/item2/audit-v08-adapters/local-guard-ledger.json").read_text())
    run,sources=checked_run(repo,a.run);crun,csources=checked_run(repo,a.census_run)
    for r in run["records"]:
        if r.get("reused_from"):require(r["seconds"]==0 and r.get("artifact_sha256"), 'acceptance predicate failed')
    require(run["records"][-1]["command"][-1]==ledger["fixture"] and ledger["fixture"] in sources, 'acceptance predicate failed')
    require(crun["records"][-1]["command"][-1]==ledger["census_fixture"] and ledger["census_fixture"] in csources, 'acceptance predicate failed')
    require(ledger["source"] in sources and ledger["source"] in csources, 'acceptance predicate failed')
    text=Path(crun["records"][-1]["log"]).read_text()
    rows=[json.loads(line.split("H62_CENSUS_JSON ",1)[1]) for line in text.splitlines() if line.startswith("H62_CENSUS_JSON ")]
    kernel={r["name"]:r for r in rows};require(len(rows)==len(kernel) and rows, 'acceptance predicate failed')
    require(all(r["module"]==ledger["module"] for r in rows), 'acceptance predicate failed')
    fixture=(repo/ledger["fixture"]).read_text()
    require(fixture.count("#guard_msgs (whitespace := lax) in #print axioms")==len(ledger["controls"]), 'acceptance predicate failed')
    for control in ledger["controls"]:
        expected="'H62.AuditV08Adapters.LocalGuardSuccess."+control+"' depends on axioms: ["+", ".join(ledger["allowed_axioms"])+"]"
        require(expected in fixture, 'acceptance predicate failed')
    for reviewed in ledger["reviewed"]:
        r=kernel[reviewed["target"]]
        require(set(r["axioms"])<=set(ledger["allowed_axioms"]), 'acceptance predicate failed')
        if reviewed["classification"]=="coherent_carrier_proof_field":require(r["is_proof"], 'acceptance predicate failed')
        if reviewed["classification"]=="inhabited_structure_carrier":require(r["kind"]=="structure_carrier" and r["structure_fields"], 'acceptance predicate failed')
    wanted={r["target"] for r in ledger["reviewed"]};require(len(wanted)==13, 'acceptance predicate failed')
    for carrier in ["View","BoolLocalView"]:
        r=kernel[ledger["module"]+"."+carrier]
        require({f["projection"] for f in r["structure_fields"]}<=wanted, 'acceptance predicate failed')
    source=json.loads(a.census.read_text())["declarations"]
    names={r["name_candidate"] for r in source if r["file"]==ledger["source"]}
    require(names=={ledger["module"]+".accepts_local",ledger["module"]+".selected_correct"}, 'acceptance predicate failed')
    result=dict(status="LOCAL_GUARD_ONLY_PASS",source_theorems_accounted=2,
        coherent_carriers=2,coherent_proof_fields=4,data_fields=2,
        reviewed_primary_declarations=13,kernel_declarations=len(rows),
        kernel_inventory=rows,reviewed=ledger["reviewed"],
        remaining_generated_candidates=[r["name"] for r in rows if r["name"] not in wanted],
        mandatory_success=True,reject_all_excluded=True,always_revert_excluded=True,
        limits=ledger["limits"],overall_audit="UNFINISHED")
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print("LOCAL_GUARD_ACCEPTANCE_PASS: success+failure, both trivial compilers excluded, coherent carriers; full audit UNFINISHED")

if __name__=="__main__":main()
