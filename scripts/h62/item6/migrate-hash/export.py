#!/usr/bin/env python3
"""Export this committed partial checkpoint; never pushes or modifies originals."""
import hashlib, json, pathlib, shutil, subprocess, tarfile
root = pathlib.Path.cwd()
base = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
branch = "codex/solidity-h62-6-20261106/migrate-hash"
out = pathlib.Path("/workspace/migrate-hash-evidence")
def git(*args): return subprocess.check_output(["git",*args])
assert git("branch","--show-current").decode().strip() == branch
subprocess.run(["git","merge-base","--is-ancestor",base,"HEAD"],check=True)
assert not git("status","--porcelain"), "commit scoped changes before export"
head = git("rev-parse","HEAD").decode().strip()
for path in ("lean-toolchain","lakefile.toml"):
    assert (root/path).read_bytes() == git("show",base+":"+path)
for name in ("CollisionBound","Adaptive"):
    expected=(root/f"tests/h62/item6/migrate-hash/{name}.lean").read_text().replace("import tests.h62.item6.«migrate-hash».CollisionBound", "import Solidity.Hash.CollisionBound")
    assert (root/f"Solidity/Hash/{name}.lean").read_text()==expected
(out/"hash-owner-overlay.patch").write_bytes(git("diff","--binary",base,"HEAD","--","Solidity/Hash/CollisionBound.lean","Solidity/Hash/Adaptive.lean"))
(out/"collision-bound-overlay.patch").write_bytes(git("diff","--binary",base,"HEAD","--","Solidity/Hash/CollisionBound.lean"))
(out/"original.patch").write_bytes(git("diff","--binary",base,"HEAD"))
temporary=out/"migration.bundle.tmp"
temporary.unlink(missing_ok=True)
subprocess.run(["git","bundle","create",str(temporary),base+"..HEAD"],check=True)
temporary.replace(out/"migration.bundle")
subprocess.run(["git","bundle","verify",str(out/"migration.bundle")],check=True)
subprocess.run(["git","apply","--reverse","--check",str(out/"migration-candidate.patch")],check=True)
(out/"HANDOFF.md").write_text(f"Committed head: {head}\nBase: {base}\nRepository: {root}\nBranch: {branch}\n\n"+(root/"docs/feature-work/h62-6-migrate-hash.md").read_text())
generated = out/"generated"
generated.mkdir(exist_ok=True)
for name in ("CollisionBound.lean","Adaptive.lean","Inventory.lean","ProductionInventory.lean","ProductionControls.lean","census.json"):
    shutil.copyfile(root/"tests/h62/item6/migrate-hash"/name,generated/name)
consumers=["solidity-h62-1-20261106/infer-helpers","solidity-h62-2-20261106/audit-label-execution","solidity-h62-2-20261106/audit-language","solidity-h62-2-20261106/audit-memory-operations","solidity-h62-2-20261106/audit-v07-lowering","solidity-h62-2-20261106/audit-v10-storage","solidity-h62-4-20261106/generic-primitive-packets","solidity-h62-4-20261106/generic-v08","solidity-h62-4-20261106/generic-yul-views","solidity-h62-6-20261106/migrate-optimizer","solidity-h62-6-20261106/migrate-storage","solidity-h62-6-20261106/migrate-theory"]
consumers += ["solidity-h62-2-20261106/audit-roadmap","solidity-h62-5-20261106/statement-graph","solidity-h62-6-20261106/migrate-roadmap","solidity-inline-assembly5-20261031/vy2-physical"]
consumers += ["solidity-h55-sol-20261106/g49-final-theorem","solidity-h62-1-20261106/p16-generator","solidity-h62-6-20261106/migrate-language","solidity-h62-6-20261106/migrate-lowering","solidity-h62-6-20261106/migrate-semantics","solidity-h62-6-20261106/migrate-solcvalidation","solidity-h62-6-20261106/migrate-root-gate"]
assert len(consumers)==len(set(consumers))
producer={"producer":"solidity-h62-6-20261106/migrate-hash","base":base,"head":head,"migration_source_head":"2a18afcdba00a85645b0b3079704f78ffcd78860","status":"reviewed owner overlay ready for coordinator retrieval; full migration goal blocked outside Hash","toolchain":"leanprover/lean4:v4.35.0","official_archive_sha256":"7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d","consumers":consumers,"files":[],"patches":{},"evidence":str(out/"new-production-acceptance-1/results.json"),"reviews":str(out/"reviews.md"),"interface_proof_budget_changes":[],"new_axioms":0,"sorry":0,"live_owner_changes":json.loads((root/"tests/h62/item6/migrate-hash/coordination.json").read_text())["live_owner_changes"],"proof_declarations_touched":json.loads((root/"tests/h62/item6/migrate-hash/coordination.json").read_text())["proof_declarations_touched"],"full_runtime_gate":"pending; Syntax.Raw owner migration required; not a cut-over approval"}
for name in ("CollisionBound","Adaptive"):
    path=f"Solidity/Hash/{name}.lean"
    producer["files"].append({"path":path,"base_sha256":hashlib.sha256(git("show",base+":"+path)).hexdigest(),"head_sha256":hashlib.sha256((root/path).read_bytes()).hexdigest()})
for name in ("hash-owner-overlay.patch","collision-bound-overlay.patch"):
    producer["patches"][name]={"path":str(out/name),"sha256":hashlib.sha256((out/name).read_bytes()).hexdigest()}
producer["routed_requester_heads"]=json.loads((root/"tests/h62/item6/migrate-hash/coordination.json").read_text()).get("routed_requester_heads",{})
producer["coordinator_disposition"]="Reviewed Hash overlay staged/routed; wait for Syntax.Raw and root full-build gates; no new ownership or budget authority."
provenance=out/"source-provenance-2a18afcdb/manifest.json"
assert provenance.exists(),"generate source_provenance.py first"
producer["source_provenance"]={"path":str(provenance),"sha256":hashlib.sha256(provenance.read_bytes()).hexdigest(),"head":"2a18afcdba00a85645b0b3079704f78ffcd78860","bundle":str(provenance.parent/"source.bundle")}
(out/"producer-overlay.json").write_text(json.dumps(producer,indent=2)+"\n")
archive = out/"evidence.tar.gz"
def included(p):
    rel = p.relative_to(out)
    return p.is_file() and not any(x in rel.parts for x in (".lake","lib","cache")) and rel.name not in ("evidence.tar.gz","SHA256SUMS","result.json")
with tarfile.open(archive,"w:gz") as tar:
    for p in sorted(out.rglob("*")):
        if included(p): tar.add(p,arcname=str(p.relative_to(out)),recursive=False)
performance = json.loads((out/"performance.json").read_text())
acceptance = json.loads((out/"acceptance.json").read_text())
coordination = json.loads((root/"tests/h62/item6/migrate-hash/coordination.json").read_text())
result = {"batch":"solidity-h62-6-20261106","slug":"migrate-hash","status":"blocked","branch":branch,"base":base,"head":head,"repository":str(root),
"checkpoints":[{"name":"1 census and clean old native build","status":"done"},{"name":"2 official pin and adaptation","status":"done"},{"name":"3 new native comparison and affected validation","status":"blocked"},{"name":"4 migration patch and root-gate handoff","status":"partial"}],
"gates":[
{"command":"git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master","status":"pass","evidence":"remote fetched; isolated branch starts at exact published base"},
{"command":"python3 scripts/h62/item6/migrate-hash/measure.py /workspace/.setup/tools/lean-4.24.0-linux /workspace/migrate-hash-evidence/old-lake-clean-3 --lake-overlay","status":"pass","evidence":str(out/"old-lake-clean-3/results.json")},
{"command":"python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /workspace/migrate-hash-evidence/new-lake-clean-2 --lake-overlay --fixture","status":"pass","evidence":str(out/"new-lake-clean-2/results.json")},
{"command":"python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /workspace/migrate-hash-evidence/new-production-acceptance-1 --production-extra","status":"pass","evidence":str(out/"new-production-acceptance-1/results.json")},
{"command":"python3 scripts/h62/item6/migrate-hash/acceptance.py /workspace/migrate-hash-evidence","status":"pass","evidence":str(out/"acceptance-after-application.log")},
{"command":"node scripts/check-layers.mjs","status":"pass","evidence":str(out/"layers.log")+": 857 core modules; zero frontend reach"},
{"command":"bash scripts/coord-tools/register.sh --check; bash scripts/coord-tools/fragments.sh --check","status":"pass","evidence":str(out/"roots.log")+"; "+str(out/"fragments.log")},
{"command":"bash scripts/check-doc-paths.sh","status":"fail","evidence":str(out/"doc-paths.log")+": pre-existing absent Bridge Mathlib SplitIfs.lean citation; scoped Markdown links pass"},
{"command":"git apply --reverse --check /workspace/migrate-hash-evidence/migration-candidate.patch; git diff --check","status":"pass","evidence":"applied patch reverses cleanly; frozen types and definitions preserved; no whitespace errors"},
{"command":"python3 scripts/h62/item6/migrate-hash/full_measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /workspace/migrate-hash-full/new-full-4 --migrated","status":"fail","evidence":str(out/"full-new-probe/summary.json")+": Syntax.Raw five String API errors,4/6389 modules; not a performance result"},
{"command":"python3 scripts/h62/item6/migrate-hash/full_measure.py /workspace/.setup/tools/lean-4.24.0-linux /workspace/migrate-hash-full/old-full-2","status":"fail","evidence":str(out/"full-old-baseline/summary.json")+":18/6389 passed; existing300s combined native command cap; no complete baseline"},
{"command":"full affected importer validation and ./run-lean.sh on root migration overlay","status":"pending","evidence":"Syntax.Raw owner overlay, completed old baseline, matched full comparison and migration root integration pending"}],
"reviews":str(out/"reviews.md")+": independent finder and skeptic approve partial evidence; no Lean/server use; all material tooling findings fixed",
"limitations":"Production Hash overlay applied and passes direct validation. Per-module growth is nonblocking per coordinator. Syntax.Raw owner migration, root disposition of the old native-command timeout, completed matched clean full comparison, affected/runtime gates and root-gate receipt remain pending. Global doc-path failure predates this patch. No full runtime pass or completion.",
"questions":[],
"typed_blockers":["OUT_OF_SCOPE_DEPENDENCY_MIGRATION_REQUIRED","BASELINE_NATIVE_COMPILE_TIMEOUT","MATCHED_FULL_BUILD_COMPARISON_PENDING","ROOT_AFFECTED_RUNTIME_GATE_PENDING"],"owner_requests":coordination["requests"],"live_owner_changes":coordination["live_owner_changes"],"proof_declarations_touched":coordination["proof_declarations_touched"],"baseline_controller":json.loads((out/"baseline-controller.json").read_text()) if (out/"baseline-controller.json").exists() else {"status":"planned","directory":"/workspace/migrate-hash-full/old-full-2"},
"declarations_helpers":acceptance,"frozen_statements_touched":[],"performance":performance,
"artifacts":{"original_patch":str(out/"original.patch"),"candidate_patch":str(out/"migration-candidate.patch"),"owner_overlay":str(out/"hash-owner-overlay.patch"),"collision_bound_overlay":str(out/"collision-bound-overlay.patch"),"producer_handoff":str(out/"producer-overlay.json"),"source_provenance":str(provenance),"source_bundle":str(provenance.parent/"source.bundle"),"bundle":str(out/"migration.bundle"),"handoff":str(out/"HANDOFF.md"),"evidence":str(out),"archive":str(archive),"checksums":str(out/"SHA256SUMS")}}
result["artifact_sha256"] = {p.name:hashlib.file_digest(p.open("rb"),"sha256").hexdigest() for p in [out/"original.patch",provenance,provenance.parent/"source.bundle",out/"hash-owner-overlay.patch",out/"collision-bound-overlay.patch",out/"producer-overlay.json",out/"migration-candidate.patch",out/"migration.bundle",out/"HANDOFF.md",archive]}
(out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
paths = [p for p in sorted(out.rglob("*")) if included(p)] + [archive,out/"result.json"]
(out/"SHA256SUMS").write_text("".join(hashlib.file_digest(p.open("rb"),"sha256").hexdigest()+"  "+str(p.relative_to(out))+"\n" for p in paths))
print(json.dumps({"head":head,"status":"blocked","artifacts":result["artifacts"],"artifact_sha256":result["artifact_sha256"]},indent=2))
