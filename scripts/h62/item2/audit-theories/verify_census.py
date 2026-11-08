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
from census import BASE, ROOT, MAP, mask, producer, scan, module_to_path

FINGERPRINTS={}
VERSION=None

def fingerprint_text(text):
    dependencies=[]
    for line in mask(text).splitlines():
        if line.startswith("import "):
            for module in line.split()[1:]:
                path=module_to_path(module).as_posix()
                if (ROOT/path).is_file(): dependencies.append(fingerprint(path))
    return sha((VERSION+text+"".join(dependencies)).encode())

def fingerprint(source):
    if source in FINGERPRINTS: return FINGERPRINTS[source]
    text=(ROOT/source).read_text()
    value=fingerprint_text(text)
    FINGERPRINTS[source]=value
    return value

ALLOW={"propext","Classical.choice","Quot.sound"}
from witness_registry import WITNESSES,IMPOSSIBLE

INTENTIONAL_REASONS={
 "Solidity.Theory.Progress.Val.not_tuple":"Intentional representation refutation: plain Val has no tuple constructor; tuples use RVal.tuple.",
 "Solidity.Theory.Progress.Controls.no_tuple_local":"Intentional negative boundary: a locals head would require a plain tuple Val, already impossible.",
 "Solidity.Ty.Finite.not_array":"Intentional separation lemma: finite shapes have no direct path to a dynamic array."}
from audit_dispositions import ACCEPTED
assert all(IMPOSSIBLE.get(n)==(item["module"],item["helper"])for n,item in ACCEPTED.items())
INTENTIONAL_REASONS.update({n:item["reason"]for n,item in ACCEPTED.items()})
H69_POLICY="H69 human decision 2026-11-06: checked joint-impossibility is the audit result for intentional negative controls/separation/refutation theorems; ordinary interfaces require joint witnesses. Coordinator Q-STATIC-VALUE option3 explicitly includes enter_static; no operational refusal coverage."

def sha(b): return hashlib.sha256(b).hexdigest()

def checked_module(serial, source, source_text=None):
    target=serial/"olean"/Path(source).with_suffix(".olean")
    meta=json.loads(target.with_suffix(".audit-result.json").read_text())
    assert meta["exit"]==0 and meta["resource_stop"] is None, source
    expected=fingerprint(source) if source_text is None else fingerprint_text(source_text)
    assert expected==meta["source_transitive_sha256"],source
    assert sha(target.read_bytes())==meta["olean_sha256"], source
    log=Path(meta["log"])
    assert sha(log.read_bytes())==meta["log_sha256"], source
    return meta,log.read_text()

def certificate(serial,module,name):
    source=f"tests/h62/item2/audit-theories/{module}.lean"
    meta,log=checked_module(serial,source)
    assert not re.search(r"\b(?:error(?:\([^)]*\))?|warning):",log),source
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
    ap.add_argument("--require-complete-explicit-module",action="append",default=[],help="Fail unless every explicit declaration in this frozen module has an accepted input disposition; generated candidates remain separate")
    a=ap.parse_args(); out=a.evidence.resolve()
    if out.is_relative_to(ROOT): raise SystemExit("Evidence must be off Git")
    global VERSION
    VERSION=json.loads((out/"serial/baseline-results.json").read_text())["version"]
    src=json.loads((out/"census/census.json").read_text())
    producer_meta,producer_log=checked_module(out/"serial","tests/h62/item2/audit-theories/ElaboratedCensus.lean")
    receipt=json.loads((out/"census-output-receipt.json").read_text())
    assert receipt["producer_exit"]==0
    for key in ("source_transitive_sha256","olean_sha256","log_sha256"):
        assert receipt["producer_"+key]==producer_meta[key],key
    if receipt.get("kind")=="format-comparison":
        data=(out/"after.json").read_bytes();comparison=(out/"before.json").read_bytes()
        assert sha(data)==receipt["sha256"] and sha(comparison)==receipt["comparison_sha256"]
        assert len(data)==receipt["bytes"] and len(comparison)==receipt["comparison_bytes"]
        pair=json.loads((out/"matched-pair.json").read_text())
        assert pair["status"]=="pass" and pair["delta_percent"]<=10
        assert pair["same_command"] and pair["same_machine"] and receipt["independent_compact_replay"] is False
        before_text=(out/"before.lean").read_text();after_text=(out/"after.lean").read_text()
        assert after_text==(ROOT/"tests/h62/item2/audit-theories/ElaboratedCensus.lean").read_text()
        assert before_text.replace("(Json.arr rows).pretty ++","(Json.arr rows).compress ++")==after_text
        before=pair["before"];after=pair["after"]
        assert before["exit"]==after["exit"]==0 and before["resource_stop"] is None and after["resource_stop"] is None
        assert before["source_transitive_sha256"]==fingerprint_text(before_text)
        assert before["source_sha256"]==sha(before_text.encode()) and after["source_sha256"]==sha(after_text.encode())
        assert sha((out/"before.olean").read_bytes())==before["olean_sha256"]
        assert sha(Path(before["log"]).read_bytes())==before["log_sha256"]
        for key in ("source_transitive_sha256","olean_sha256","log_sha256"):
            assert after[key]==producer_meta[key],key
        typed=json.loads(data)
        assert receipt["decoded_equal"] is True and typed==json.loads(comparison)
        assert len(typed)==pair["records"]
    else:
        replay=json.loads((out/"census-replay.json").read_text())
        data=(out/"elaborated.json").read_bytes()
        assert sha(data)==receipt["sha256"]==replay["sha256"]
        assert data==(out/"elaborated-replay.json").read_bytes()
        assert len(data)==receipt["bytes"]==replay["bytes"] and replay["identical"] is True
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
            row["simultaneous_witness"]=row["certificate"]["theorem"]
        elif name in IMPOSSIBLE:
            row["status"]="intentional-impossibility-checked"
            row["certificate"]=certificate(out/"serial",*IMPOSSIBLE[name])
            row["intentional_reason"]=INTENTIONAL_REASONS[name]
            row["policy_source"]=H69_POLICY
            row["simultaneous_witness"]=None
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
       "This census verifies original theory inputs only. Separate verify_totality.py receipts cover core compiler success/control packets; target ABI/gas/fork and other compiler branches remain unproved."]}
    module_counts={file:dict(Counter(r["status"] for r in rows if r["file"]==file)) for file in files}
    payload["explicit_module_dispositions"]=module_counts
    payload["intentional_impossibility_policy"]=H69_POLICY
    (out/"verified-census.json").write_text(json.dumps(payload,ensure_ascii=False,indent=2)+"\n")
    gaps=[{"theorem":r["elaborated"]["name"],"file":r["file"],"line":r["line"],
      "status":r["status"],"documented_producing_lane":r["documented_producing_lane"],
      "proving_owner":r["proving_owner"]} for r in rows if r["status"] in ("uncovered","private-witness-pending")]
    gaps.extend({"theorem":r["name"],"file":r["file"],"line":None,"status":r["status"],
      "documented_producing_lane":r["documented_producing_lane"],"proving_owner":r["proving_owner"]}
      for r in payload["generated_candidates"])
    assert len(gaps)==len({r["theorem"] for r in gaps}),"Duplicate gap accounting"
    (out/"uncovered.json").write_text(json.dumps(gaps,indent=2)+"\n")
    generated=sum(r["name"] not in used for r in typed)
    print("STATEMENT_CENSUS_PASS "+json.dumps(counts,sort_keys=True)+f"; generated candidates pending={generated}; full assignment acceptance=false")
    accepted={"joint-witness-checked","no-inputs","intentional-impossibility-checked"}
    for file in a.require_complete_explicit_module:
        if file not in module_counts:
            print("EXPLICIT_MODULE_UNKNOWN: "+file)
            raise SystemExit(1)
        pending=sum(n for status,n in module_counts[file].items() if status not in accepted)
        if pending:
            print(f"EXPLICIT_MODULE_BLOCKED: {file}: {pending} pending explicit declarations")
            raise SystemExit(1)
        print(f"EXPLICIT_MODULE_PASS: {file}: {sum(module_counts[file].values())} explicit declarations; generated candidates remain separately pending")
    if a.require_full:
        print(f"FULL_ACCEPTANCE_BLOCKED: {len(gaps)} pending/blocked statements or candidates; separate compiler evidence and remaining target ABI/gas/fork obligations require full-assignment verification")
        raise SystemExit(1)

if __name__=="__main__": main()
