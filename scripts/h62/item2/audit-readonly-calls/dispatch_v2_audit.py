#!/usr/bin/env python3
"""Guard versioned dispatch migration erasing frozen or unresolved obligations.

The supplemental census retains all792 original records and exports only the
nine V2 interface theorem types. Lexical mapping and checked types are not
compiler adequacy, fresh runtime attestation or source-world oracle agreement.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess

import census
import export_signatures as export

FROZEN_SHA="e07aa0fe5f1a94c292c6d9edc22eee478f45c560b1802fab5e7ac581da9a2ffb"
FILES=["Solidity/Lowering/Readonly/SourceDispatchInterfaceV2.lean","Solidity/Lowering/Readonly/SourceAllHistoriesV2.lean"]
PREFIX="Solidity.Lowering.Readonly.SourceDispatchV2."
NAMES=["selector_length","selector_ne_empty","pickFn_empty","pickGetter_empty","selected_nonempty","dispatch_succ","all_at","all_callbacks","static_call_storage"]
CLIENTS={"selected_nonempty":PREFIX+"Controls.function_jointly_satisfiable",
         "dispatch_succ":PREFIX+"Controls.function_jointly_satisfiable",
         "static_call_storage":"Solidity.H62.ReadonlyAudit.StaticCallWitness.jointly_satisfiable"}
MIGRATED=["Solidity/Backend/WorldCalls/"+name+".lean" for name in ["ClosedSourceFrame","ClosedSourceConsumers","ClosedSourceControls","SourceExpressionConsumer"]]
V1=["Solidity/Lowering/Readonly/"+name+".lean" for name in ["SourceDispatchEffects","SourceAllHistories"]]


def assemble(frozen,rows):
    """Structural census only; theorem-client references require separate gates."""
    if frozen.get("base")!=census.BASE or frozen.get("theorem_count")!=792 or len(frozen.get("declarations",[]))!=792:raise ValueError("original792 membership drift")
    if len({(r["file"],r["source_name"]) for r in frozen["declarations"]})!=792:raise ValueError("duplicate original obligation")
    wanted={PREFIX+n for n in NAMES}
    if len(rows)!=9 or {r["source_name"] for r in rows}!=wanted:raise ValueError("V2 interface declaration drift")
    result=copy.deepcopy(rows)
    for row in result:
        name=row["source_name"].removeprefix(PREFIX)
        expected=FILES[0] if name in NAMES[:6] else FILES[1]
        if row["file"]!=expected:raise ValueError("V2 declaration module drift")
        row.update(owner="H121 audit-readonly-calls",owner_source="H121 transfer; former Claude RO-v2 lane frozen",
                   witness_status="joint-client-pending-check" if name in CLIENTS else "no-named-input-proof-binder",
                   joint_client=CLIENTS.get(name),premise_assessment="Explicit source input proof binders mapped; result implications/negations and global structures do not imply compiler adequacy.")
    return {"schema":1,"base":census.BASE,"scope":"additive-versioned-dispatch-supplement","original_snapshot":copy.deepcopy(frozen),
            "original_artifact_sha256":FROZEN_SHA,"declarations":result,"modules":[{"file":p} for p in FILES],
            "theorem_count":9,"boundary":"All792 original obligations retained. Supplemental lexical mapping and exact kernel types only; no original positive witness, private/global completeness, body equivalence, compiler adequacy or timing STOP clearance inferred."}


def migration(frozen):
    records=[]
    for path in MIGRATED:
        old={r["source_name"]:r for r in frozen["declarations"] if r["file"]==path}
        new={r["source_name"]:r for r in census.declarations(path)}
        if old.keys()!=new.keys() or any(any(old[k][f]!=new[k][f] for f in ("signature_sha256","variable_context","visibility")) for k in old):raise ValueError("consumer statement drift: "+path)
        records.append({"file":path,"retained_headers":len(old),"sha256":hashlib.sha256((census.ROOT/path).read_bytes()).hexdigest()})
    for path in V1:
        raw=(census.ROOT/path).read_bytes()
        if raw!=subprocess.check_output(["git","show",census.BASE+":"+path],cwd=census.ROOT):raise ValueError("frozen V1 drift: "+path)
        records.append({"file":path,"frozen_byte_identical":True,"sha256":hashlib.sha256(raw).hexdigest()})
    return records


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--frozen",type=Path,required=True);p.add_argument("--output",type=Path,required=True)
    p.add_argument("--verify",action="store_true")
    args=p.parse_args();raw=args.frozen.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=FROZEN_SHA:p.error("wrong original artifact bytes")
    frozen=json.loads(raw);data=assemble(frozen,[r for f in FILES for r in census.declarations(f)])
    data["migration"]=migration(frozen)
    for row in data["modules"]:row["sha256"]=hashlib.sha256((census.ROOT/row["file"]).read_bytes()).hexdigest()
    if args.verify:
        if json.loads((args.output/"manifest.json").read_text())!=data:raise ValueError("supplemental source/manifest drift")
        evidence=args.output.parent/"evidence";query=args.output/"Signatures.lean"
        log=evidence/"signature-types.log";receipt_path=evidence/"signature-types.json"
        receipt=export.verify_receipt(query,log,receipt_path,data)
        result=export.collect(log.read_text(),data)
        result["provenance"]={key:receipt[key] for key in ["command","gate_exit","log_sha256","input_source_sha256","lean_version","lake_version","lean_binary_sha256","lake_binary_sha256","toolchain_file_sha256"]}
        result["provenance"].update(query=str(query.resolve()),log=str(log.resolve()),receipt=str(receipt_path.resolve()))
        export.verify_artifact(result,data)
        (args.output/"types.json").write_text(json.dumps(result,indent=2)+"\n")
        print("DISPATCH_V2_EXACT_TYPES_PASS declarations=9 original=792")
        return
    args.output.mkdir(mode=0o700,parents=True,exist_ok=False)
    (args.output/"manifest.json").write_text(json.dumps(data,indent=2)+"\n")
    (args.output/"Signatures.lean").write_text(export.generate(data))
    print("DISPATCH_V2_CENSUS_PASS original=792 supplemental=9 migrated_headers="+str(sum(r.get("retained_headers",0) for r in data["migration"])))


if __name__=="__main__":main()
