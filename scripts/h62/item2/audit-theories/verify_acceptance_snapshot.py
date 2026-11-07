#!/usr/bin/env python3
"""Cross-check original ledger, current helper receipts and reviewed-role union.
This is an external acceptance/accounting gate, never full assignment acceptance.
No Lean jobs; bulk reports remain off Git. Pending ordinary impossibilities are
preserved and cannot become H69 or joint witnesses through a report edit.
"""
import argparse,json,re,subprocess
from collections import Counter
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import digest,annotate,SPECS as BRIDGE_OUTCOME
from mutability_input_roles import SPECS as CLOSER_PAYABLE,EQ
from assignable_input_roles import SPECS as ASSIGNABLE
from pending_impossibility import PENDING
import verify_census as v

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("evidence","roles","historical-evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();proof=a.evidence.resolve();roles_path=a.roles.resolve();old=a.historical_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT)for p in(proof,roles_path,old,out)):raise SystemExit("Use off-Git evidence")
    source=old/"verified-census.json";manifest=dict((line.split("  ",1)[1],line.split("  ",1)[0])for line in(old/"SHA256SUMS").read_text().splitlines());assert digest(source)==manifest[source.name]
    historical=json.loads(source.read_text());assert historical["base"]==BASE
    originals={r["source_name"]:r for r in historical["declarations"]};assert len(originals)==500
    ledger_path=proof/"original-coverage-ledger.json";helpers_path=proof/"verified-helpers.json";gaps_path=proof/"remaining-original-records.json"
    ledger=json.loads(ledger_path.read_text());helpers=json.loads(helpers_path.read_text());roles=json.loads(roles_path.read_text());gaps=json.loads(gaps_path.read_text())
    for p in(ledger,roles):assert p["frozen_assignment_base"]==BASE and p["historical_typed_snapshot_sha256"]==digest(source)
    for p in(ledger,helpers,roles):assert p["full_assignment_acceptance"]is False
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear()
    helper_names=set();helper_sources=set()
    expected_sources={p.relative_to(ROOT).as_posix()for p in(ROOT/"tests/h62/item2/audit-theories").rglob("*.lean")if p.name!="ElaboratedCensus.lean"}
    for module in helpers["modules"]:
        src=module["source"];assert src not in helper_sources;helper_sources.add(src)
        meta,log=v.checked_module(proof/"serial",src)
        for k in("command","exit","seconds","log","source_transitive_sha256"):assert module[k]==meta[k]
        assert not re.search(r"\b(?:error(?:\([^)]*\))?|warning):",log)and "sorryAx"not in log
        declarations=scan((ROOT/src).read_text(),src);names={r["source_name"]for r in declarations}
        assert len(names)==len(module["theorems"])and names=={r["name"]for r in module["theorems"]}
        for item in module["theorems"]:
            name=item["name"];assert name not in helper_names;helper_names.add(name)
            cert=v.certificate(proof/"serial",Path(src).stem,name.removeprefix("H62.AuditTheories."));assert cert["axioms"]==item["axioms"]
    assert helper_sources==expected_sources and len(helper_names)==helpers["proved_theorems"]
    entries=ledger["original_explicit_declarations"];assert len(entries)==len(originals)and{r["source_name"]for r in entries}==set(originals)
    joint=set();intentional=set();expected_gaps=set();expected_gap_rows={};counts=Counter();changed=set()
    for row in entries:
        name=row["source_name"];orig=originals[name]
        for key in("file","line","visibility","source_header","elaborated_type_sha256","documented_producing_lane","proving_owner"):assert row[key]==orig[key]
        frozen=subprocess.check_output(["git","show",BASE+":"+row["file"]],cwd=ROOT)
        status="byte-unchanged"if(ROOT/row["file"]).read_bytes()==frozen else"changed-frozen-file-version-pending"
        assert row["frozen_file_status"]==status
        if status!="byte-unchanged":changed.add(row["file"])
        if name in v.WITNESSES:
            joint.add(name);assert row["status"]=="joint-certificate-present-version-fidelity-separate"
            assert row["current_certificate"]==v.certificate(proof/"serial",*v.WITNESSES[name])
        elif name in v.IMPOSSIBLE:
            intentional.add(name);assert row["status"]=="H69-intentional-impossibility-certificate-present"
            assert row["current_certificate"]==v.certificate(proof/"serial",*v.IMPOSSIBLE[name])
            assert row["intentional_reason"]==v.INTENTIONAL_REASONS[name]
        elif orig["status"]=="no-inputs":assert row["status"]=="historical-empty-input-telescope"
        else:
            gap_name=orig["elaborated"]["name"];expected_gaps.add(gap_name)
            expected_gap_rows[gap_name]={"theorem":gap_name,"source_name":name,"file":row["file"],"line":row["line"],"status":row["status"],"documented_producing_lane":row["documented_producing_lane"],"proving_owner":row["proving_owner"]}
            assert row["status"]==("private-witness-pending"if orig["visibility"]=="private"else"public-witness-pending")
        if name in PENDING:
            item=PENDING[name];assert name not in joint and name not in intentional
            annotation=row["pending_joint_impossibility"];assert annotation["accepted_H69"]is False
            assert annotation["question"]==item["question"]and annotation["reason"]==item["reason"],"Pending ledger routing mismatch"
            assert annotation["certificate"]==v.certificate(proof/"serial",item["module"],item["helper"])
        counts[row["status"]]+=1
    assert joint==set(v.WITNESSES)and intentional==set(v.IMPOSSIBLE)and dict(counts)==ledger["original_explicit_counts"]
    assert sorted(changed)==ledger["changed_frozen_files"]
    assert ledger["pending_impossibility_questions"]==[dict(theorem=n,question=i["question"],accepted_H69=False)for n,i in PENDING.items()]
    generated=historical["generated_candidates"];assert len(generated)==ledger["original_generated_candidates_pending"]==986
    expected_gaps.update(r["name"]for r in generated)
    for row in generated:
        expected_gap_rows[row["name"]]={"theorem":row["name"],"source_name":None,"file":row["file"],"line":None,"status":"original-generated-candidate-pending","documented_producing_lane":row["documented_producing_lane"],"proving_owner":row["proving_owner"]}
    assert len(gaps)==len({r["theorem"]for r in gaps})==len(expected_gaps)==ledger["remaining_original_records"]
    assert{r["theorem"]for r in gaps}==expected_gaps
    assert all(row==expected_gap_rows[row["theorem"]]for row in gaps),"Remaining record metadata/owner mismatch"
    records=roles["declarations"];names=[r["theorem"]for r in records]
    assert len(names)==len(set(names))==roles["reviewed_role_records"]==roles["cumulative_original_roles"],"Role declaration/count mismatch"
    assert roles["remaining_original_roles"]==500-len(names)and set(names)<=set(originals)
    role_joint=0;role_pending=0
    specs=dict(BRIDGE_OUTCOME);assert not set(specs)&set(CLOSER_PAYABLE);specs.update(CLOSER_PAYABLE)
    assert not set(specs)&set(ASSIGNABLE);specs.update(ASSIGNABLE)
    assert set(names)==set(specs)
    for row in records:
        name=row["theorem"];orig=originals[name]
        assert orig["file"]not in changed,"Reviewed role frozen file changed"
        expected=annotate(orig,specs[name])
        for binder in expected["binders"]:
            if binder["name"]==EQ:binder["role"]="global-equality-operation-instance-data"
        assert all(row[k]==value for k,value in expected.items()),"Reviewed role interpretation mismatch"
        assert row["source_header"]==orig["source_header"]and row["historical_frozen_elaborated_type_sha256"]==orig["elaborated_type_sha256"]
        raw=[{k:val for k,val in b.items()if k not in("index","role")}for b in row["binders"]]
        assert raw==orig["elaborated"]["binders"]
        if name in PENDING:
            item=PENDING[name];assert row["accepted_H69"]is False and"current_joint_certificate"not in row,"Ordinary pending interface promoted"
            assert row["status"]==item["status"],"Ordinary pending status mismatch"
            assert row["question"]==item["question"],"Ordinary pending question mismatch"
            assert row["pending_impossibility_certificate"]==v.certificate(proof/"serial",item["module"],item["helper"]);role_pending+=1
        else:
            assert row.get("status","joint-witness-checked")=="joint-witness-checked"and not row.get("accepted_H69",False),"Joint role status mismatch"
            assert"pending_impossibility_certificate"not in row
            assert name in joint and row["current_joint_certificate"]==v.certificate(proof/"serial",*v.WITNESSES[name]);role_joint+=1
    assert role_joint==roles["joint_certificates_in_role_union"]and role_pending==roles["ordinary_pending_impossibilities"]
    payload={"current_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),"frozen_assignment_base":BASE,
      "checked_helper_theorems":len(helper_names),"joint_certificates":len(joint),"accepted_H69":len(intentional),"original_explicit_declarations":len(entries),
      "original_generated_pending":len(generated),"remaining_original_records":len(expected_gaps),"reviewed_roles":len(names),"remaining_roles":500-len(names),
      "ordinary_impossibility_questions":[dict(theorem=n,question=i["question"],accepted_H69=False)for n,i in PENDING.items()],"changed_frozen_files":sorted(changed),
      "input_sha256":{str(p):digest(p)for p in(source,ledger_path,helpers_path,gaps_path,roles_path)},"full_assignment_acceptance":False,"lean_jobs":0,
      "boundary":"External coherent accounting/current kernel-receipt validation only; no original-version definition equivalence, generated exclusion, full compiler target totality or final runtime acceptance."}
    out.mkdir(parents=True,exist_ok=True);(out/"acceptance-snapshot.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("ACCEPTANCE_SNAPSHOT_PASS "+json.dumps({k:payload[k]for k in("checked_helper_theorems","joint_certificates","remaining_original_records","reviewed_roles","remaining_roles","full_assignment_acceptance")}))
if __name__=="__main__":main()
