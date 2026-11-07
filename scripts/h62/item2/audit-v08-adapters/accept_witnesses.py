#!/usr/bin/env python3
"""Reconcile reviewed source witnesses, H69 impossibility, and exact kernel types.
Accepts this resource family only; never passes the full H62 audit.
"""
import argparse, hashlib, json
from pathlib import Path

def require(condition, message='acceptance predicate failed'):
    if not condition:
        raise ValueError(message)

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def checked_run(repo, directory):
    run=json.loads((directory/"results.json").read_text())
    require(run["versions"][0].startswith("Lean (version 4.24.0,"), 'acceptance predicate failed')
    require("797c613eb9b6d4ec95db23e3e00af9ac6657f24b" in run["versions"][0], 'acceptance predicate failed')
    require(run["records"] and all(r["exit"]==0 and r["stop"] is None for r in run["records"]), 'acceptance predicate failed')
    require(run["no_swap"] and run["cap_bytes"]==12*1024**3 and run["reserve_bytes"]==4*1024**3, 'acceptance predicate failed')
    sources=json.loads((directory/"source-sha256.json").read_text())
    for path,expected in sources.items(): require(digest(repo/path)==expected, path)
    return run,sources

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for key in ["repo","census","run","census-run","out"]: ap.add_argument("--"+key,type=Path,required=True)
    a=ap.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    if out==repo or repo in out.parents: raise SystemExit("Output must be off Git")
    ledger=json.loads((repo/"tests/h62/item2/audit-v08-adapters/witness-ledger.json").read_text())
    census=json.loads(a.census.read_text());run,sources=checked_run(repo,a.run)
    krun,ksources=checked_run(repo,a.census_run)
    require(ledger["fixture"] in sources and run["records"][-1]["command"][-1]==ledger["fixture"], 'acceptance predicate failed')
    log=Path(krun["records"][-1]["log"]).read_text()
    krows=[json.loads(line.split("H62_CENSUS_JSON ",1)[1]) for line in log.splitlines() if line.startswith("H62_CENSUS_JSON ")]
    census_fixture="tests/h62/item2/audit-v08-adapters/ResourceStatementCensus.lean"
    require(census_fixture in ksources and krun["records"][-1]["command"][-1]==census_fixture, 'acceptance predicate failed')
    require(len({row["name"] for row in krows})==len(krows), 'acceptance predicate failed')
    kernel={row["name"]:row for row in krows if row["kind"]=="theorem"}
    require(len(kernel)==12, 'acceptance predicate failed')
    require(all(r["module"]==ledger["defining_module"] for r in krows), 'acceptance predicate failed')
    indexed={r["id"]:r for r in census["declarations"]}
    rows=ledger["rows"];require(len(rows)==11 and len({r["census_id"] for r in rows})==11, 'acceptance predicate failed')
    fixture=(repo/ledger["fixture"]).read_text()
    require(fixture.count("#guard_msgs (whitespace := lax) in #print axioms")==len(ledger["axiom_guards"]), 'acceptance predicate failed')
    for proof in ledger["axiom_guards"]: require("'"+proof+"' does not depend on any axioms" in fixture, 'acceptance predicate failed')
    counts={"joint_witness":0,"intentional_impossibility":0,"no_propositional_premises":0}
    for row in rows:
        target=indexed[row["census_id"]];exact=kernel[row["target"]]
        require(target["name_candidate"]==row["target"] and target["signature_source"]==row["signature_source"], 'acceptance predicate failed')
        require(target["signature_sha256"]==row["signature_sha256"], 'acceptance predicate failed')
        require(hashlib.sha256(exact["type_expr"].encode()).hexdigest()==row["kernel_type_sha256"], 'acceptance predicate failed')
        require(target["file"] in sources and target["file"] in ksources, 'acceptance predicate failed')
        kind=row["classification"];counts[kind]+=1
        if kind=="no_propositional_premises":require(not any(b["is_proposition"] for b in exact["binders"]), 'acceptance predicate failed')
        else:
            require(any(b["is_proposition"] for b in exact["binders"]), 'acceptance predicate failed')
            require(row["proof"] in ledger["axiom_guards"], 'acceptance predicate failed')
            if kind=="intentional_impossibility":require(row["why_intentional"], 'acceptance predicate failed')
    require(counts==dict(joint_witness=5,intentional_impossibility=1,no_propositional_premises=5), 'acceptance predicate failed')
    named={r["target"] for r in rows}
    for generated in ledger["generated_equations"]:
        require(generated["name"] not in named and generated["classification"]=="generated_equation", 'acceptance predicate failed')
        require(hashlib.sha256(kernel[generated["name"]]["type_expr"].encode()).hexdigest()==generated["type_sha256"], 'acceptance predicate failed')
        named.add(generated["name"])
    require(named==set(kernel), 'acceptance predicate failed')
    covered={r["census_id"] for r in rows}
    result=dict(status="RESOURCE_FAMILY_ONLY_PASS",census_candidates=len(indexed),classifications=counts,
        source_statements_accounted=11,non_theorem_declarations_retained=len(krows)-len(kernel),
        predicate_witness="NoFail inhabited; separate from frozen SourceSpec producer",
        kernel_generated_equations=len(ledger["generated_equations"]),
        remaining_candidates=len(indexed)-len(covered),resource_statement_fidelity="exact imported kernel types; reviewed proof correspondence",
        overall_elaborated_fidelity="PENDING",overall_audit="UNFINISHED",witnesses=rows,
        uncovered=[key for key in indexed if key not in covered])
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print("RESOURCE_FAMILY_ACCEPTANCE_PASS: 5 joint witnesses, 1 H69 impossibility, 5 premise-free; overall audit UNFINISHED")

if __name__=="__main__":main()
