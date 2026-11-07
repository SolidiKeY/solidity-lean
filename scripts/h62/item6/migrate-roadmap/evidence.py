#!/usr/bin/env python3
"""Regenerate source/API/dependency handoff data off git; no Lean execution.
Usage: evidence.py OLD_RESULT MATRIX_RESULT OLD_API_RESULT NEW_FIXTURE_RESULT
"""
import collections, difflib, hashlib, importlib.util, json, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[4]
OUT=Path("/workspace/migrate-roadmap-evidence")
def canonical(value):return (json.dumps(value,sort_keys=True,indent=2)+"\n").encode()
def sha(data):return hashlib.sha256(data).hexdigest()
def write(name,value):
    (OUT/name).write_bytes(canonical(value))
def rows(path):
    result=[]
    for line in path.read_text().splitlines():
        if "ROADMAP_API {" in line:result.append(json.loads(line.split("ROADMAP_API ",1)[1]))
    assert len({r["name"] for r in result})==len(result)
    return sorted(result,key=lambda r:r["name"])
def load(path):
    p=Path(path).resolve();assert p.is_relative_to(OUT) and p.name=="result.json"
    return p,json.loads(p.read_text())
def main():
    if len(sys.argv)!=5:raise SystemExit(__doc__)
    oldp,old=load(sys.argv[1]);newp,new=load(sys.argv[2]);apip,api=load(sys.argv[3]);fixturep,fixture=load(sys.argv[4])
    assert old["exit"]==api["exit"]==fixture["exit"]==0
    assert all(r["guard"] is None and r["inputs_before"]==r["inputs_after"] for r in (old,new,api,fixture))
    assert new["exit"]==1 and set(new["module_statuses"].values())<={"pass","fail","blocked"}
    assert old["tooling_sha256"]==new["tooling_sha256"]
    assert old["resources"]==new["resources"]
    runs=(old,new,api,fixture)
    assert all(run["resources"]==old["resources"] for run in runs)
    unused_helper_captures={}
    def compiler_inputs(run):
        script=Path(run["command"][-1])
        assert sha(script.read_bytes())==run["script_sha256"], "recorded workload script changed"
        executed=script.read_text()
        used={};unused=[]
        for key,value in run["inputs_after"].items():
            if key.startswith("tests/h62/item6/migrate-roadmap/") and str(ROOT/key) not in executed:
                unused.append(key)
            else:used[key]=value
        unused_helper_captures[run["container"]]=unused
        return used
    selected=[compiler_inputs(run) for run in runs]
    for left in selected:
        for key,value in left.items():
            assert sha((ROOT/key).read_bytes())==value,("current compiler input mismatch",key)
        for right in selected:
            shared=left.keys() & right.keys()
            assert all(left[key]==right[key] for key in shared), "cross-run compiler input mismatch"
    spec=importlib.util.spec_from_file_location("census",Path(__file__).with_name("census.py"))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    c=m.census(ROOT);g=m.graph(ROOT)
    assert set(old["modules"])==set(new["module_statuses"])==set(c["closure"])
    for module,status in new["module_statuses"].items():
        deps=[d for d in g.imports(module) if d in new["module_statuses"]]
        if status in ("pass","fail"):assert all(new["module_statuses"][d]=="pass" for d in deps)
        else:assert any(new["module_statuses"][d]!="pass" for d in deps)
    oldrows=rows(apip.with_name("build.log"));newrows=rows(fixturep.with_name("build.log"))
    assert len(oldrows)==2077 and len(newrows)==391
    assert {r["module"] for r in oldrows}==set(c["targets"])
    assert all(r["module"]=="Solidity.Roadmap.Evm" for r in newrows)
    for row in oldrows+newrows:
        assert set(row["theorem_axioms"])<={"propext","Classical.choice","Quot.sound"},row["name"]
    write("old-api.json",oldrows);write("new-evm-api.json",newrows)
    fixture_source=(ROOT/"tests/h62/item6/migrate-roadmap/HashContainsFixture.lean").read_text()
    candidate=fixture_source[fixture_source.index('@[deprecated Fork.ctorIdx'):fixture_source.index('\ntheorem legacy_fork_index')]
    evm=(ROOT/"Solidity/Roadmap/Evm.lean").read_text()
    proposed=evm+'\nnamespace Solidity.Roadmap.Evm\n\n'+candidate+'\nend Solidity.Roadmap.Evm\n'
    proposal=''.join(difflib.unified_diff(evm.splitlines(keepends=True),proposed.splitlines(keepends=True),fromfile='a/Solidity/Roadmap/Evm.lean',tofile='b/Solidity/Roadmap/Evm.lean'))
    (OUT/"evm-compatibility-proposal.patch").write_text(proposal)
    before_evm={r["name"]:r for r in oldrows if r["module"]=="Solidity.Roadmap.Evm"}
    after_evm={r["name"]:r for r in newrows}
    removed=sorted(before_evm.keys()-after_evm.keys());added=sorted(after_evm.keys()-before_evm.keys())
    write("api-compatibility-deltas.json",dict(old_evm_declarations=len(before_evm),new_evm_declarations=len(after_evm),
        removed=[before_evm[n] for n in removed],added=[after_evm[n] for n in added],
        shared_debug_type_changes=[dict(name=n,old=before_evm[n]["type_debug"],new=after_evm[n]["type_debug"]) for n in sorted(before_evm.keys() & after_evm.keys()) if before_evm[n]["type_debug"]!=after_evm[n]["type_debug"]],
        status="BLOCKED: preserve all original interfaces; in-scope test candidates are not production restoration",
        owner_request=dict(id="B-OWNED-EVM-API",recipient="migrate-root-gate and live Evm producer",file="Solidity/Roadmap/Evm.lean",proposal=str(OUT/"evm-compatibility-proposal.patch"),request="Exact-file owner reply required before inserting tested compatibility definitions for missing original names. No scope exclusion or production edit inferred from absence of reply.",names=removed,shared_debug_type_changes_pending_root_review=sum(before_evm[n]["type_debug"]!=after_evm[n]["type_debug"] for n in before_evm.keys() & after_evm.keys()))))
    interfaces=[]
    for module in c["modules"]:
        name=module["module"];before=[r for r in oldrows if r["module"]==name];after=[r for r in newrows if r["module"]==name]
        assert module["unchanged"]
        interfaces.append(dict(module=name,source_sha256=module["sha256"],base_source_sha256=module["base_sha256"],
            old_declarations=len(before),old_debug_api_sha256=sha(canonical(before)),
            new_declarations=len(after) if after else None,new_debug_api_sha256=sha(canonical(after)) if after else None))
    write("frozen-interfaces.json",dict(note="Whole source unchanged; debug API hashes include generated constants and are not semantic equality proofs. Axiom arrays cover theorem constants only.",modules=interfaces))
    failures=[module for module,status in new["module_statuses"].items() if status=="fail"]
    assigned={target:dict(status=new["module_statuses"][target],blocking_failed_dependencies=[f for f in failures if f in g.closure([target])]) for target in c["targets"]}
    write("cross-directory-dependencies.json",dict(boundary_edges=c["boundary_edges"],external_local_modules=c["external_local_modules"],
        failure_owner_requests=[dict(id="B-EXTERNAL-"+f.replace(".","-"),module=f,path=f.replace(".","/")+".lean",recipient="migrate-root-gate: route to directory migration owner",scope="READ ONLY",request="Owner-reviewed official pinned v4.35.0 migration preserving exact types, semantics and budgets; no new axioms, sorry or raised maxHeartbeats.") for f in failures],assigned=assigned))
    write("census.json",c)
    write("validation-summary.json",dict(base=m.BASE,repository=str(ROOT),branch=subprocess.check_output(["git","branch","--show-current"],cwd=ROOT,text=True).strip(),
        old_build=dict(result=str(oldp),wall_seconds=old["wall_seconds"],sampled_peak_aggregate_rss_bytes=old["sampled_peak_aggregate_rss_bytes"],resources=old["resources"],compiled_head=old["head"],modules=len(old["modules"])),
        matrix=dict(result=str(newp),counts=dict(collections.Counter(new["module_statuses"].values())),assigned_counts=dict(collections.Counter(x["status"] for x in assigned.values()))),
        api=dict(result=str(apip),old_declarations=len(oldrows),new_evm_declarations=len(newrows)),fixture_result=str(fixturep),
        performance=dict(successful_after_build=None,delta_percent=None,acceptance="BLOCKED: failed matrix is not an after-build timing; >10% stop threshold remains binding"),
        historical_unused_helper_captures=unused_helper_captures,production_lean_changes=0,added_axioms=0,added_sorry=0,added_native_decide=0,
        proof_boundary="Old assigned closure elaborates; one new assigned module and six isolated/compatibility fixture theorems pass; two compatibility abbreviations are tested only in the helper. Python/status checks and API fingerprints are tooling evidence, not compiler correctness or cross-version semantic equality proofs.",
        outstanding=["Four external dependency owner repairs", "Owner-coordinated Evm legacy API restoration; see api-compatibility-deltas.json", "Validate 14 blocked new-toolchain Roadmap modules", "Full affected/final run-lean gate", "Successful matched after-build timing and regression review", "Final integration review/acceptance; root owns tracked lean-toolchain cut-over"],
        original_objective_sha256="71335b00c701811fd071a6d471ce30303066d242b9917095f67e1d7585292a83"))
    print(json.dumps(dict(old_declarations=len(oldrows),new_evm_declarations=len(newrows),matrix=dict(collections.Counter(new["module_statuses"].values())),assigned={k:v["status"] for k,v in assigned.items()})))
if __name__=="__main__":main()
