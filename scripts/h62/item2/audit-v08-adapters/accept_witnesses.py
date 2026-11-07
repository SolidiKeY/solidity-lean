#!/usr/bin/env python3
"""Reconcile reviewed source witnesses, H69 impossibility, and exact kernel types.
Accepts this resource family only; never passes the full H62 audit.
"""
import argparse, hashlib, json
from pathlib import Path

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def checked_run(repo, directory):
    run=json.loads((directory/"results.json").read_text())
    assert run["versions"][0].startswith("Lean (version 4.24.0,")
    assert "797c613eb9b6d4ec95db23e3e00af9ac6657f24b" in run["versions"][0]
    assert run["records"] and all(r["exit"]==0 and r["stop"] is None for r in run["records"])
    assert run["no_swap"] and run["cap_bytes"]==12*1024**3 and run["reserve_bytes"]==4*1024**3
    sources=json.loads((directory/"source-sha256.json").read_text())
    for path,expected in sources.items(): assert digest(repo/path)==expected, path
    return run,sources

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for key in ["repo","census","run","census-run","out"]: ap.add_argument("--"+key,type=Path,required=True)
    a=ap.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    if out==repo or repo in out.parents: raise SystemExit("Output must be off Git")
    ledger=json.loads((repo/"tests/h62/item2/audit-v08-adapters/witness-ledger.json").read_text())
    census=json.loads(a.census.read_text());run,sources=checked_run(repo,a.run)
    krun,ksources=checked_run(repo,a.census_run)
    assert ledger["fixture"] in sources and run["records"][-1]["command"][-1]==ledger["fixture"]
    log=Path(krun["records"][-1]["log"]).read_text()
    krows=[json.loads(line.split("H62_CENSUS_JSON ",1)[1]) for line in log.splitlines() if line.startswith("H62_CENSUS_JSON ")]
    census_fixture="tests/h62/item2/audit-v08-adapters/ResourceStatementCensus.lean"
    assert census_fixture in ksources and krun["records"][-1]["command"][-1]==census_fixture
    assert len({row["name"] for row in krows})==len(krows)
    kernel={row["name"]:row for row in krows if row["kind"]=="theorem"}
    assert len(kernel)==12
    assert all(r["module"]==ledger["defining_module"] for r in krows)
    indexed={r["id"]:r for r in census["declarations"]}
    rows=ledger["rows"];assert len(rows)==11 and len({r["census_id"] for r in rows})==11
    fixture=(repo/ledger["fixture"]).read_text()
    assert fixture.count("#guard_msgs (whitespace := lax) in #print axioms")==len(ledger["axiom_guards"])
    for proof in ledger["axiom_guards"]: assert "'"+proof+"' does not depend on any axioms" in fixture
    counts={"joint_witness":0,"intentional_impossibility":0,"no_propositional_premises":0}
    for row in rows:
        target=indexed[row["census_id"]];exact=kernel[row["target"]]
        assert target["name_candidate"]==row["target"] and target["signature_source"]==row["signature_source"]
        assert target["signature_sha256"]==row["signature_sha256"]
        assert hashlib.sha256(exact["type_expr"].encode()).hexdigest()==row["kernel_type_sha256"]
        assert target["file"] in sources and target["file"] in ksources
        kind=row["classification"];counts[kind]+=1
        if kind=="no_propositional_premises":assert not any(b["is_proposition"] for b in exact["binders"])
        else:
            assert any(b["is_proposition"] for b in exact["binders"])
            assert row["proof"] in ledger["axiom_guards"]
            if kind=="intentional_impossibility":assert row["why_intentional"]
    assert counts==dict(joint_witness=5,intentional_impossibility=1,no_propositional_premises=5)
    named={r["target"] for r in rows}
    for generated in ledger["generated_equations"]:
        assert generated["name"] not in named and generated["classification"]=="generated_equation"
        assert hashlib.sha256(kernel[generated["name"]]["type_expr"].encode()).hexdigest()==generated["type_sha256"]
        named.add(generated["name"])
    assert named==set(kernel)
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
