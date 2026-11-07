#!/usr/bin/env python3
"""Retain all new interface declarations as PENDING; inventory is not a witness."""
import argparse,json,hashlib,collections
from pathlib import Path
from accept_witnesses import checked_run, require

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for k in ["repo","evidence","out"]:ap.add_argument("--"+k,type=Path,required=True)
    a=ap.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    require(out!=repo and repo not in out.parents, 'acceptance predicate failed')
    result=[]
    for runname,fixture,module in [
      ("h70-p8-census","P8StatementCensus","Solidity.Lowering.P8.FrozenInterface"),
      ("h70-runtime-census","RuntimeFrameStatementCensus","Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1")]:
        run,sources=checked_run(repo,a.evidence/runname)
        path="tests/h62/item2/audit-v08-adapters/"+fixture+".lean"
        require(path in sources and run["records"][-1]["command"][-1]==path, 'acceptance predicate failed')
        text=Path(run["records"][-1]["log"]).read_text()
        rows=[json.loads(line.split("H62_CENSUS_JSON ",1)[1]) for line in text.splitlines() if line.startswith("H62_CENSUS_JSON ")]
        require(rows and len({r["name"] for r in rows})==len(rows), 'acceptance predicate failed')
        require(all(r["module"]==module for r in rows), 'acceptance predicate failed')
        parents={f["projection"]:r["name"] for r in rows for f in r["structure_fields"]}
        for row in rows:
            row["audit_status"]="PENDING"
            row["type_sha256"]=hashlib.sha256(row["type_expr"].encode()).hexdigest()
            row["carrier"]=parents.get(row["name"])
            row["source_role"]=("proof_field" if row["is_proof"] else "data_field") if row["name"] in parents else row["kind"]
        result.append(dict(module=module,count=len(rows),roles=dict(collections.Counter(r["source_role"] for r in rows)),declarations=rows))
    output=dict(status="INVENTORY_ONLY_PASS",modules=result,new_witnesses=0,
      owner_wait=dict(ticket="PREMISE-P8-001",destination="solidity-v12-v17-20261031/v16-correctness-transfer",delivery_acceptance="not supplied; host journals authoritative",current_owner_delivery_pending=["claudecloud/moved2-20261105/vy5-composition","claudecloud/moved3-20261105/v07-lowering"],owner_agreement=False,producer_validation=False),
      scope="All new declarations remain pending. H70 does not change statements or establish global SourceSpec/CreationPremises/LibraryPremises joint witnesses.")
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(output,sort_keys=True,indent=2)+"\n")
    print(json.dumps(dict(status=output["status"],modules=[{k:v for k,v in m.items() if k!="declarations"} for m in result],new_witnesses=0),sort_keys=True))

if __name__=="__main__":main()
