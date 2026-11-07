#!/usr/bin/env python3
"""Generate exact owner requests and a private proof candidate without editing owners."""
import argparse, collections, difflib, fcntl, hashlib, importlib.util, json, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode=True
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def main():
    a=argparse.ArgumentParser();a.add_argument("root");a.add_argument("census");a.add_argument("output");a.add_argument("--producer-head");a.add_argument("--new-validation");a.add_argument("--old-validation");args=a.parse_args()
    root=Path(args.root).resolve(); out=Path(args.output).resolve();out.mkdir(parents=True,exist_ok=True)
    lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    spec=importlib.util.spec_from_file_location("census",Path(__file__).with_name("census.py"));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    census=json.loads(Path(args.census).read_text());imports={r["module"]:m.header_imports((root/r["path"]).read_text()) for r in census["closure_sources"]}
    impacts=[]
    for row in census["modules"]:
        queue=collections.deque([[row["module"]]]);seen=set()
        while queue:
            route=queue.popleft();node=route[-1]
            if node=="Solidity.Syntax.Raw": impacts.append(dict(module=row["module"],path=row["path"],route=route));break
            if node in seen:continue
            seen.add(node)
            for dep in imports.get(node,[]): queue.append(route+[dep])
    (out/"syntax-raw-impacts.json").write_text(json.dumps(impacts,indent=2)+"\n")
    target="Solidity/Calculus/LinearCountermodel.lean"
    frozen=subprocess.check_output(["git","show",BASE+":"+target],cwd=root,text=True)
    before="  simpa only [Bool.not_eq_true'] using hp"
    after="  simpa only [falseNode, Bool.not_eq_true'] using hp"
    if frozen.count(before)!=1:raise RuntimeError("Candidate replacement is not unique")
    candidate=frozen.replace(before,after)
    if (root/target).read_text() not in [frozen,candidate]:raise RuntimeError("Preserve unexpected owned-file changes")
    proposal="".join(difflib.unified_diff(frozen.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile="a/"+target,tofile="b/"+target))
    (out/"proposed-owner-proof.patch").write_text(proposal)
    candidate+="\n#print axioms Solidity.Linear.AFml.falseNode_spec\n#print axioms Solidity.Linear.AFml.searchCountermodel\n"
    fixture=root/"tests/h62/item6/migrate-calculus/GeneratedCountermodelCandidate.lean"
    if fixture.exists() and fixture.read_text()!=candidate:raise RuntimeError("Preserve unexpected candidate fixture")
    fixture.write_text(candidate);(out/fixture.name).write_text(candidate)
    header=next(line for line in frozen.splitlines() if line.startswith("theorem falseNode_spec"))
    requests=[dict(id="DEP-SYNTAX-RAW-V435",kind="OWNER_MIGRATION_DEPENDENCY",owner="solidity-h62-6-20261106/migrate-syntax",file="Solidity/Syntax/Raw.lean",lines=[597,650,665,682,684],blocked_assigned_count=len(impacts),impact_report=str(out/"syntax-raw-impacts.json"),action="Provide owner-approved v4.35.0 migration dependency preserving exact String semantics and frozen types; lane never edits this out-of-scope file",evidence="/workspace/migrate-calculus-evidence/new-clean-02/Solidity.Syntax.Raw.log"),
        dict(id="OWNER-LINEAR-FALSENODE",kind="OWNER_COORDINATION_REQUIRED",live_owner="solidity-automation-20261031/va1-decision",migration_owner="solidity-h62-6-20261106/migrate-calculus",file=target,theorem="Solidity.Linear.AFml.falseNode_spec",line=134,statement_sha256=hashlib.sha256(header.encode()).hexdigest(),action="Review exact one-line proof-only overlay proposal before any existing-file edit; no absent reply is permission",proposal=str(out/"proposed-owner-proof.patch"),candidate_fixture=str(fixture),candidate_status="pending bounded validation",evidence="/workspace/migrate-calculus-evidence/new-independent-03/Solidity.Calculus.LinearCountermodel.log")]
    validations=[]
    for validation in [args.old_validation,args.new_validation]:
        if not validation: continue
        path=Path(validation); result=json.loads(path.read_text())
        if result["status"]!="pass":raise RuntimeError("Validation is not a pass")
        expected_hash=hashlib.sha256(candidate.encode()).hexdigest()
        matches=[r for r in result["fixture_sources"] if Path(r["path"]).name==fixture.name]
        if len(matches)!=1 or matches[0]["sha256"]!=expected_hash:raise RuntimeError("Candidate validation source mismatch")
        validations.append(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),lean_version=result["lean_version"],fixture_sha256=expected_hash))
    if validations:
        requests[1]["candidate_status"]="isolated fixture pass; original-file edit awaits owner coordination"
        requests[1]["validations"]=validations
    requests[1]["candidate_fixture"]=str(out/fixture.name)
    requests[1]["transient_test_path"]=str(fixture)
    ownership=json.loads(Path("/workspace/h62-coordinator-inputs/ownership.json").read_text())
    migration_scopes=[(row["owner"],set(p.strip() for p in row.get("writeScope","").split(";"))) for row in ownership["items"] if row.get("id","").startswith("H62-6-MIGRATE-")]
    assigned={r["module"] for r in census["modules"]}
    dependencies=[dict(row,owners=[owner for owner,scope in migration_scopes if row["path"] in scope]) for row in census["closure_sources"] if row["module"] not in assigned]
    (out/"cross-directory-owners.json").write_text(json.dumps(dependencies,indent=2)+"\n")
    if args.producer_head:
        producer=subprocess.check_output(["git","rev-parse",args.producer_head],cwd=root,text=True).strip()
        source=subprocess.check_output(["git","show",producer+":"+target],cwd=root,text=True)
        original=subprocess.check_output(["git","show",producer+"^:"+target],cwd=root,text=True)
        files=subprocess.check_output(["git","diff","--name-only",producer+"^",producer],cwd=root,text=True).splitlines()
        if source!=frozen.replace(before,after) or original!=frozen or files!=[target]:raise RuntimeError("H70 producer does not match reviewed source-only change")
        requests[1]["kind"]="H70_PARTIAL_PRODUCER_PUBLICATION"
        requests[1]["candidate_status"]="Exact reviewed full-module fixture passed both toolchains; H70 source-only producer committed"
        requests[1]["producer_head"]=producer
        requests[1]["status"]="H70 exact-file partial producer published locally; full migration gates still blocked"
        requests[1]["action"]="Retrieve H70 producer commit/patch; preserve existing RSS STOP and live ownership"
        requests[1]["producer_manifest"]="/workspace/migrate-calculus-evidence/h70-producer/producer.json"
    record=dict(base=BASE,delivery="Saved for coordinator pickup; relay.sh unavailable; not sent",requests=requests)
    (out/"owner-requests.json").write_text(json.dumps(record,indent=2)+"\n")
    (root/"tests/h62/item6/migrate-calculus/owner-requests.json").write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps(dict(blocked=len(impacts),independent=len(census["modules"])-len(impacts),candidate=str(fixture))))
if __name__=="__main__":main()
