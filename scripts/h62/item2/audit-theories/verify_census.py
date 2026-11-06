#!/usr/bin/env python3
"""Reconcile all frozen source declarations with Lean's typed census, exactly once.
A coverage census PASS is NOT full-witness acceptance. Emits all uncovered rows.
Bulk output is off Git. Checks original-source identity and proof/cache provenance.
"""
import argparse
from collections import Counter
import hashlib
import json
import re
import subprocess
from pathlib import Path
from census import BASE, ROOT, MAP, mask, producer, scan

FINGERPRINTS={}
VERSION=None

def fingerprint(source):
    if source in FINGERPRINTS: return FINGERPRINTS[source]
    text=(ROOT/source).read_text()
    dependencies=[]
    for line in mask(text).splitlines():
        if line.startswith("import "):
            for module in line.split()[1:]:
                path=module.replace(".","/")+".lean"
                if (ROOT/path).is_file(): dependencies.append(fingerprint(path))
    value=sha((VERSION+text+"".join(dependencies)).encode())
    FINGERPRINTS[source]=value
    return value

ALLOW={"propext","Classical.choice","Quot.sound"}
WITNESSES={
 "Solidity.Theory.Progress.tuple_stmt_progress":("ProgressWitnesses","tuple_stmt_progress_joint_witness"),
 "Solidity.Theory.Progress.stmt_progress":("ProgressWitnesses","stmt_progress_joint_witness"),
 "Solidity.Theory.Progress.expr_progress":("ScopeControls","expr_progress_joint_witness"),
 "Solidity.Theory.Progress.items_progress":("ScopeControls","items_progress_joint_witness"),
 "Solidity.Theory.Progress.body_progress":("ScopeControls","body_progress_joint_witness"),
 "Solidity.Theory.Progress.callsOKX_none":("ScopeControls","callsOKX_none_joint_witness")}
IMPOSSIBLE={
 "Solidity.Theory.Progress.Val.not_tuple":("ProgressWitnesses","no_plain_tuple_input"),
 "Solidity.Theory.Progress.Controls.no_tuple_local":("ProgressWitnesses","no_tuple_locals_input"),
 "Solidity.Ty.Finite.not_array":("FiniteBoundary","no_finite_array_path_input")}

def sha(b): return hashlib.sha256(b).hexdigest()

def checked_module(serial, source):
    target=serial/"olean"/Path(source).with_suffix(".olean")
    meta=json.loads(target.with_suffix(".audit-result.json").read_text())
    assert meta["exit"]==0 and meta["resource_stop"] is None, source
    assert fingerprint(source)==meta["source_transitive_sha256"],source
    assert sha(target.read_bytes())==meta["olean_sha256"], source
    log=Path(meta["log"])
    assert sha(log.read_bytes())==meta["log_sha256"], source
    return meta,log.read_text()

def certificate(serial,module,name):
    source=f"tests/h62/item2/audit-theories/{module}.lean"
    meta,log=checked_module(serial,source)
    assert not re.search(r"\b(?:error|warning):",log),source
    fullname="H62.AuditTheories."+name
    m=re.search("'"+re.escape(fullname)+r"' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",log)
    assert m,fullname
    axioms=set(x.strip() for x in (m[2] or "").split(",") if x.strip())
    assert axioms<=ALLOW,(fullname,axioms)
    # Confirm the checked helper source is exactly the source named by provenance.
    assert meta["command"][-1]==source,source
    return {"theorem":fullname,"source":source,"axioms":sorted(axioms),"log":meta["log"]}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",type=Path,required=True)
    ap.add_argument("--require-full",action="store_true",help="Fail closed on pending witness/compiler obligations")
    a=ap.parse_args(); out=a.evidence.resolve()
    if out.is_relative_to(ROOT): raise SystemExit("Evidence must be off Git")
    global VERSION
    VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"]
    src=json.loads((out/"census/census.json").read_text())
    producer_meta,producer_log=checked_module(out/"serial","tests/h62/item2/audit-theories/ElaboratedCensus.lean")
    receipt=json.loads((out/"census-output-receipt.json").read_text())
    replay=json.loads((out/"census-replay.json").read_text())
    assert receipt["producer_exit"]==0
    for key in ("source_transitive_sha256","olean_sha256","log_sha256"):
        assert receipt["producer_"+key]==producer_meta[key],key
    data=(out/"elaborated.json").read_bytes()
    assert sha(data)==receipt["sha256"]==replay["sha256"]
    assert data==(out/"elaborated-replay.json").read_bytes()
    assert len(data)==receipt["bytes"]==replay["bytes"]
    assert replay["identical"] is True
    typed=json.loads(data)
    assert f"H62_ELABORATED_CENSUS: {len(typed)} theorem constants" in producer_log
    assert src["base"]==BASE
    frozen_map=subprocess.check_output(["git","show",BASE+":"+MAP],cwd=ROOT).decode()
    files=["Solidity/"+f for f in re.findall(r"^\| `(Theory/[^`]+\.lean)`",frozen_map,re.M)]
    expected_records=[]; expected_modules=[]; expected_inputs={MAP:sha(frozen_map.encode())}
    for file in files:
        text=(ROOT/file).read_text()
        records=scan(text,file)
        expected_records.extend(records)
        expected_modules.append({"file":file,"theorems":len(records)})
        expected_inputs[file]=sha(text.encode())
    assert src["declarations"]==expected_records
    assert src["modules"]==expected_modules
    assert src["source_inputs_sha256"]==expected_inputs
    for file,digest in src["source_inputs_sha256"].items():
        current=(ROOT/file).read_bytes()
        frozen=subprocess.check_output(["git","show",BASE+":"+file],cwd=ROOT)
        assert current==frozen and sha(current)==digest,file
    for module in src["modules"]:
        checked_module(out/"serial",module["file"])
    by={r["name"]:r for r in typed}
    assert len(by)==len(typed),"Duplicate elaborated names"
    rows=[]; used=set()
    for d in src["declarations"]:
        matches=[r for r in typed if r["name"]==d["source_name"] or
          (d["visibility"]=="private" and r["name"].endswith("."+d["source_name"]))]
        assert len(matches)==1,(d["source_name"],len(matches))
        t=matches[0]; name=d["source_name"]
        assert t["module"]==d["file"][:-5].replace("/","."),name
        assert t["name"] not in used,name
        used.add(t["name"])
        row=dict(d,elaborated=t,elaborated_type_sha256=sha(t["type_expr"].encode()),
          hypothesis_classification={"logical_binders":[i for i,b in enumerate(t["binders"]) if b["is_prop"]],
           "note":"Data/typeclass inputs also require joint inhabitance; global/per-input classification needs manual review."})
        if d["visibility"]=="private": row["status"]="private-witness-pending"
        elif name in WITNESSES:
            row["status"]="joint-witness-checked"
            row["certificate"]=certificate(out/"serial",*WITNESSES[name])
        elif name in IMPOSSIBLE:
            row["status"]="blocked-intentionally-empty-input"
            row["certificate"]=certificate(out/"serial",*IMPOSSIBLE[name])
        elif not t["binders"]:
            row["status"]="no-inputs"
            row["certificate"]={"empty_telescope":"True.intro; no binders in elaborated signature"}
        else: row["status"]="uncovered"
        rows.append(row)
    assert len(rows)==500 and len(used)==500
    counts=dict(Counter(r["status"] for r in rows))
    payload={"base":BASE,"counts":counts,"declarations":rows,
      "generated_candidates":[dict(r,status="interface-classification-and-witness-pending",file=r["module"].replace(".","/")+".lean",
          documented_producing_lane=producer(r["module"].replace(".","/")+".lean"),
          proving_owner="unresolved; coordinator relay required")
        for r in typed if r["name"] not in used],
      "full_assignment_acceptance":False,
      "limitations":["Current proving owners require coordinator confirmation.",
       "Logical-vs-data binders are typed; global-vs-per-input obligations still require individual review.",
       "Additional generated theorem constants are retained as pending candidates, not silently excluded.",
       "No compiler success/totality/gas/fork contract has been proved by these source controls."]}
    (out/"verified-census.json").write_text(json.dumps(payload,ensure_ascii=False,indent=2)+"\n")
    gaps=[{"theorem":r["elaborated"]["name"],"file":r["file"],"line":r["line"],
      "status":r["status"],"documented_producing_lane":r["documented_producing_lane"],
      "proving_owner":r["proving_owner"]} for r in rows if r["status"] in ("uncovered","blocked-intentionally-empty-input","private-witness-pending")]
    gaps.extend({"theorem":r["name"],"file":r["file"],"line":None,"status":r["status"],
      "documented_producing_lane":r["documented_producing_lane"],"proving_owner":r["proving_owner"]}
      for r in payload["generated_candidates"])
    assert len(gaps)==len({r["theorem"] for r in gaps}),"Duplicate gap accounting"
    (out/"uncovered.json").write_text(json.dumps(gaps,indent=2)+"\n")
    generated=sum(r["name"] not in used for r in typed)
    print("STATEMENT_CENSUS_PASS "+json.dumps(counts,sort_keys=True)+f"; generated candidates pending={generated}; full assignment acceptance=false")
    if a.require_full:
        print(f"FULL_ACCEPTANCE_BLOCKED: {len(gaps)} pending/blocked statements or candidates; compiler/gas/fork contracts remain unlinked")
        raise SystemExit(1)

if __name__=="__main__": main()
