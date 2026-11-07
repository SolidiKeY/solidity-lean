#!/usr/bin/env python3
"""Deterministic off-git frozen API and latest migration handoff generator."""
import hashlib,json,pathlib,sys
from census import ROOT,imports,closure,frozen_matches
E=pathlib.Path(sys.argv[1]);assert E.is_absolute()
def read(p):return json.loads((E/p).read_text())
def put(p,x):(E/p).write_text(json.dumps(x,indent=2,sort_keys=True)+"\n")
def sha(b):return hashlib.sha256(b).hexdigest()
c=read("census-base.json");old=read("old-clean-3/result.json")
h70=(E/"h70-new-clean-1/result.json").is_file()
new_name="h70-new-clean-1" if h70 else "new-clean-2";new=read(new_name+"/result.json")
assert old["exit"]==0 and old["sources_unchanged"] and old["controls_unchanged"]
assert new["sources_unchanged"] and new["controls_unchanged"]
assert frozen_matches(ROOT,{m.replace(".","/")+".lean":h for m,h in c["closure_source_sha256"].items()})
for stem in ["api-controls-old-bound","api-controls-new-bound","frozen-api-old-bound"]:
 r=read(stem+".result.json");assert r["exit"]==0 and r["cleanup_stopped"] and r["controls_unchanged"] and r["original_sources_unchanged"]
rows=[json.loads(l.split("\t",1)[1]) for l in (E/"frozen-api-old-bound.log").read_text().splitlines() if l.startswith("STORAGE_API\t")]
assert len({r["name"] for r in rows})==len(rows)
mods={f["path"][:-5].replace("/",".") for f in c["files"]};assert {r["module"] for r in rows}==mods
api=[{"module":r["module"],"name":r["name"],"type_and_levels_repr_sha256":sha(json.dumps({k:r[k] for k in ["levels","type"]},sort_keys=True,separators=(",",":")).encode())} for r in sorted(rows,key=lambda r:(r["module"],r["name"]))]
put("frozen-interface-old.json",{"toolchain":old["lean_version"],"kind":"SHA256 of metadata-stripped kernel type/level structural repr; generated constants included; new-version equality pending","module_count":len(mods),"constant_count":len(api),"constants":api})
owners=json.loads(pathlib.Path("/workspace/h62-coordinator-inputs/ownership.json").read_text())["items"]
def owner(p):return [r["owner"] for r in owners if r.get("id","").startswith("H62-6-MIGRATE-") and p in r.get("writeScope","").split("; ")]
graph={m:imports((ROOT/(m.replace(".","/")+".lean")).read_text()) for m in c["build_order"]}
failed=[m["module"] for m in new["modules"] if m["exit"]!=0];assert len(failed)==1
blocked=failed[0];blocked_mods=sorted(m for m in mods if blocked in closure(graph,[m]));assert len(blocked_mods)==21
source=blocked.replace(".","/")+".lean"
if h70:
 from prepare_owner_overlay import validate_postimage,EXPECTED_PATCH
 manifest=read("h70-source-manifest.json");assert new["fixture_sources_unchanged"]
 assert new["source_manifest_sha256"]==sha((E/"h70-source-manifest.json").read_bytes())
 assert frozen_matches(pathlib.Path(manifest["source_root"]),manifest["tree_sha256"])
 validate_postimage(pathlib.Path(manifest["source_root"])/manifest["changed_file"])
 assert blocked=="Solidity.Storage.HashedLayout"
 assert next(r for r in new["modules"] if r["module"]=="Solidity.Hash.CollisionBound")["exit"]==0
 for stem in ["h70-locate-old-bound","h70-locate-new-bound"]:
  r=read(stem+".result.json");assert r["exit"]==0 and r["controls_unchanged"] and r["original_sources_unchanged"] and r["compiled_sources_unchanged"] and r["cleanup_stopped"]
 proposal=ROOT/"tests/h62/item6/migrate-storage/hashed-layout-proposal.patch"
 request={"id":"O-STORAGE-001","type":"OWNER_COORDINATION","owner":"solidity-v07-v11-20261030/v10-storage-operations (live producer), via coordinator","migration_lane":"solidity-h62-6-20261106/migrate-storage","file":source,"line":376,"theorem":"Solidity.Storage.STy.locate_bounded","diagnostic":"dependent elimination cannot solve some(...) = STy.word.locate l (head :: tail); recovery guards417/420 fail","source_sha256":c["closure_source_sha256"][blocked],"proposal":str(proposal),"proposal_sha256":sha(proposal.read_bytes()),"proposal_status":"UNAPPLIED; local rejection proof tested, full module not repaired or validated","action":"Coordinate exact-file permission with live producer before any original edit, or obtain owner-supplied equivalent migration. Preserve frozen statements/definitions/budgets. H70 routing granted no original-file permission.","fixture":"tests/h62/item6/migrate-storage/LocateRejectControls.lean","blocked_owned_modules":blocked_mods}
 hash_state={"id":"D-HASH-001","status":"component_cleared_in_private_fixture_only","owner":"solidity-h62-6-20261106/migrate-hash","reported_head":"a3f49ee0ec1829e63022c90194048d5a1ffe0d22","patch_sha256":EXPECTED_PATCH,"postimage_git_blob":manifest["new_git_blob"],"full_affected_gate":"pending","original_Hash_source_edited":False}
else:
 request={"id":"D-HASH-001","type":"DEPENDENCY_MIGRATION","owner":owner(source),"file":source,"errors":[407,660,680],"action":"Owner supplies statement/budget-preserving overlay","blocked_owned_modules":blocked_mods}
 hash_state={"id":"D-HASH-001","status":"blocked"}
request["evidence"]=str(E/new_name/"logs"/(blocked+".log"))
keyold=next(m for m in old["modules"] if m["module"]=="Solidity.KeySort");keynew=next(m for m in new["modules"] if m["module"]=="Solidity.KeySort")
report={"base":c["base"],"repository":str(ROOT),"status":"blocked","candidate_run":new_name,"hash_owner_ticket":hash_state,"requests":[request,{"id":"G-ROOT-001","type":"FINAL_INTEGRATED_GATE_AND_RESOURCE_DISPOSITION","owner":"solidity-h62-6-20261106/migrate-root-gate","action":"After source coordination and dependency overlays, obtain complete matched comparison/resource disposition, then full affected and run-lean.sh gates; root alone edits final lean-toolchain. No passing/full comparison follows from partial owner overlay.","downstream_modules":len(c["downstream_affected"])}],"old":{"modules":len(old["modules"]),"wall_seconds":old["build_wall_seconds"],"peak_sampled_rss_bytes":old["peak_sampled_aggregate_rss_bytes"]},"new":{"attempted":len(new["modules"]),"passing":sum(m["exit"]==0 for m in new["modules"]),"assigned_passing":sum(m["exit"]==0 and m["module"] in mods for m in new["modules"]),"failed":blocked},"timing_delta_percent":None,"comparison":"No complete new build; whole-build matched comparison unavailable. Failed partial runs cannot supply a whole-build delta.","partial_resource_escalation":{"owner":"migrate-root-gate","module":"Solidity.KeySort","old_sampled_rss_bytes":keyold["peak_sampled_aggregate_rss_bytes"],"new_sampled_rss_bytes":keynew["peak_sampled_aggregate_rss_bytes"],"old_wall_seconds":keyold["wall_seconds"],"new_wall_seconds":keynew["wall_seconds"],"sampled_rss_increase_percent":100*(keynew["peak_sampled_aggregate_rss_bytes"]/keyold["peak_sampled_aggregate_rss_bytes"]-1),"partial_wall_increase_percent":100*(keynew["wall_seconds"]/keyold["wall_seconds"]-1),"disposition":"Escalate partial observations; heavy migration stopped after failed prerequisite. Matched whole-build comparison and >10% STOP decision remain root-gate obligations."},"external_dependencies":[{"module":m,"owner":owner(m.replace(".","/")+".lean"),"base_sha256":c["closure_source_sha256"][m],"compiled_sha256":new["closure_source_sha256"][m]} for m in c["external_dependencies"]],"cross_directory_edges":c["cross_directory_edges"],"declarations":{"original_named":c["declaration_count"],"exported_old_kernel_constants":len(api),"original_source_files_edited":0,"new_production_helpers":0,"introduced_sorry_axiom_native_decide":[0,0,0]},"backfill":{"scanner_controls":"pass","old_type_hash_export":"pass","new_type_hash_comparison":"blocked","h70_owner_postimage_controls":"pass" if h70 else "pending","h70_rejection_controls_both_versions":"pass" if h70 else "pending","h70_rejection_axioms":"old:none; new:propext" if h70 else None}}
# H82 retirement is authoritative over historical H70 permission requests.
retirement=ROOT/"tests/h62/item6/migrate-storage/h82-handoff/retirement-status.json"
if retirement.exists():
 state=json.loads(retirement.read_text())
 report.update(status="partial",execution_status=state["execution_status"],handoff_to=state["handoff_to"],retirement_status_file=str(retirement.relative_to(ROOT)))
 report["current_waits"]=json.loads((retirement.parent/"waits-v1.json").read_text())["waits"]
 for request in report["requests"]:
  if request["id"]=="O-STORAGE-001":
   request.update(status="withdrawn_under_H82",type="WITHDRAWN_EXACT_FILE_AGREEMENT",action="No exact-file owner agreement required for statement-preserving proof-only repair underH82. Technical line376 failure remains; successor handles repair/validation after this retired lane stops.")
  elif request["id"]=="G-ROOT-001":
   request["action"]="Successor completes technical source repairs, meaning/axiom/budget checks, matched resources undercurrentH81 and fullaffected/run-lean gates. H82 removes proof-only exact-file agreements; retirement forbids thisworker fromcontinuing. Root owns finaltoolchain edit."
put("dependency-report.json",report)
if h70:put("h70-dependency-report.json",report)
print(json.dumps({"status":report["status"],"candidate":new_name,"failed":blocked,"passed":report["new"]["passing"],"old_wall":old["build_wall_seconds"],"exported_constants":len(api),"blocked_modules":len(blocked_mods),"timing_delta_percent":None}))
