#!/usr/bin/env python3
"""Check saved kernel-run provenance and reconcile the five reviewed witnesses.
This accepts only this small backfill. It cannot pass the overall H62 audit.
"""
import argparse, hashlib, json
from pathlib import Path

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for key in ["repo","census","run","out"]: ap.add_argument("--"+key,type=Path,required=True)
    a=ap.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    if out==repo or repo in out.parents: raise SystemExit("Output must be off Git")
    ledger=json.loads((repo/"tests/h62/item2/audit-v08-adapters/witness-ledger.json").read_text())
    census=json.loads(a.census.read_text());run=json.loads((a.run/"results.json").read_text())
    sources=json.loads((a.run/"source-sha256.json").read_text())
    assert run["versions"][0].startswith("Lean (version 4.35.0,")
    assert "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" in run["versions"][0]
    assert all(r["exit"]==0 and r["stop"] is None for r in run["records"])
    assert run["no_swap"] and run["cap_bytes"]==12*1024**3 and run["reserve_bytes"]==4*1024**3
    for path,expected in sources.items(): assert digest(repo/path)==expected, path
    assert ledger["fixture"] in sources
    assert run["records"][-1]["command"][-1]==ledger["fixture"]
    assert "error:" not in Path(run["records"][-1]["log"]).read_text()
    indexed={r["id"]:r for r in census["declarations"]}
    assert len(ledger["rows"])==5 and len({r["census_id"] for r in ledger["rows"]})==5
    fixture=(repo/ledger["fixture"]).read_text()
    assert fixture.count("#guard_msgs (whitespace := lax) in #print axioms")==5
    for row in ledger["rows"]:
        target=indexed[row["census_id"]]
        assert target["name_candidate"]==row["target"]
        assert target["signature_sha256"]==row["signature_sha256"]
        assert target["signature_source"]==row["signature_source"]
        assert target["file"] in sources
        assert "'"+row["proof"]+"' does not depend on any axioms" in fixture
    witnessed={r["census_id"] for r in ledger["rows"]}
    result=dict(status="BACKFILL_ONLY_PASS",census_candidates=len(indexed),
        joint_premise_targets=5,uncovered_candidates=len(indexed)-5,
        ambiguous_source_signatures=len(census["summary"]["unterminated_signatures"]),
        owners_confirmed=False,elaborated_statement_fidelity="PENDING",
        compiler_totality_success="PENDING",failure_gas_fork_execution="PENDING",
        overall_audit="UNFINISHED",witnesses=ledger["rows"],
        uncovered=[r for r in indexed if r not in witnessed])
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print("BACKFILL_ACCEPTANCE_PASS: 5 joint-premise targets; "+str(len(indexed)-5)+" uncovered candidates; overall audit UNFINISHED")

if __name__=="__main__": main()
