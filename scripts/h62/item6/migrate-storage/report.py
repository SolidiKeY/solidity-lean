#!/usr/bin/env python3
"""Deterministic off-git census/API/dependency handoff generator."""
import hashlib,json,pathlib,sys
from census import ROOT,imports,closure,frozen_matches
E=pathlib.Path(sys.argv[1]);assert E.is_absolute()
def read(p):return json.loads((E/p).read_text())
def put(p,x):(E/p).write_text(json.dumps(x,indent=2,sort_keys=True)+"\n")
def sha(b):return hashlib.sha256(b).hexdigest()
c=read("census-base.json");old=read("old-clean-3/result.json");new=read("new-clean-2/result.json")
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
blocked="Solidity.Hash.CollisionBound"
blocked_mods=sorted(m for m in mods if blocked in closure(graph,[m]))
assert len(blocked_mods)==21
source=blocked.replace(".","/")+".lean"
request={"id":"D-HASH-001","type":"DEPENDENCY_MIGRATION","owner":owner(source),"file":source,"base":c["base"],"source_sha256":c["closure_source_sha256"][blocked],"toolchain_pin_sha256":"7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d","errors":[{"line":407,"theorem":"Solidity.Hash.countP_contains_le","diagnostic":"function equality from List.contains not discharged by congr 1"},{"line":660,"theorem":"Solidity.Hash.countP_near_le","diagnostic":"omega failure after decide/Prop simplification"},{"line":680,"theorem":"Solidity.Hash.countP_covers_le","diagnostic":"omega failure after decide/Prop simplification"}],"recovery_failures":"six #guard_msgs axiom checks include sorryAx only because of rejected proof elaboration; no failing artifact accepted; never repin sorryAx","evidence":str(E/"new-clean-2/logs/Solidity.Hash.CollisionBound.log"),"fixture":"tests/h62/item6/migrate-storage/ApiControls.lean","action":"Owner supplies migration preserving exact original types, premises, semantics and proof budgets; relay overlay to storage and migrate-root-gate. No outside-scope edits by Storage.","blocked_owned_modules":blocked_mods}
keyold=next(m for m in old["modules"] if m["module"]=="Solidity.KeySort");keynew=next(m for m in new["modules"] if m["module"]=="Solidity.KeySort")
report={"base":c["base"],"repository":str(ROOT),"status":"blocked","requests":[request,{"id":"G-ROOT-001","type":"FINAL_INTEGRATED_GATE","owner":"solidity-h62-6-20261106/migrate-root-gate","action":"After dependency overlays, run full affected and run-lean.sh gates using identical official pin; root alone edits final lean-toolchain.","downstream_modules":len(c["downstream_affected"])}],"old":{"modules":len(old["modules"]),"wall_seconds":old["build_wall_seconds"],"peak_sampled_rss_bytes":old["peak_sampled_aggregate_rss_bytes"]},"new":{"attempted":len(new["modules"]),"passing":sum(m["exit"]==0 for m in new["modules"]),"assigned_passing":0,"failed":blocked},"timing_delta_percent":None,"comparison":"pending complete successful new build; incomplete failed runs cannot be compared","partial_resource_escalation":{"owner":"migrate-root-gate","module":"Solidity.KeySort","old_sampled_rss_bytes":keyold["peak_sampled_aggregate_rss_bytes"],"new_sampled_rss_bytes":keynew["peak_sampled_aggregate_rss_bytes"],"increase_percent":100*(keynew["peak_sampled_aggregate_rss_bytes"]/keyold["peak_sampled_aggregate_rss_bytes"]-1),"qualification":"partial per-module sampled RSS increase; whole-build time and peak regression unknown"},"external_dependencies":[{"module":m,"owner":owner(m.replace(".","/")+".lean"),"sha256":c["closure_source_sha256"][m]} for m in c["external_dependencies"]],"cross_directory_edges":c["cross_directory_edges"],"declarations":{"original_named":c["declaration_count"],"exported_kernel_constants":len(api),"original_source_files_edited":0,"new_production_helpers":0,"owned_original_sorry_axiom_native_decide":[0,0,0],"introduced_sorry_axiom_native_decide":[0,0,0]},"backfill":{"scanner_controls":"pass","api_controls_old":"pass","api_controls_new":"pass","old_type_hash_export":"pass","new_type_hash_comparison":"blocked"}}
put("dependency-report.json",report)
print(json.dumps({"status":report["status"],"old_wall":old["build_wall_seconds"],"old_rss":old["peak_sampled_aggregate_rss_bytes"],"exported_constants":len(api),"blocked_modules":len(blocked_mods),"partial_keysort_rss_increase_percent":report["partial_resource_escalation"]["increase_percent"]}))
