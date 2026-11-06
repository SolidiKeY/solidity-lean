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
for path in ("Solidity/Hash/CollisionBound.lean","Solidity/Hash/Adaptive.lean","lean-toolchain","lakefile.toml"):
    assert (root/path).read_bytes() == git("show",base+":"+path)
(out/"original.patch").write_bytes(git("diff","--binary",base,"HEAD"))
if not (out/"migration.bundle").exists():
    subprocess.run(["git","bundle","create",str(out/"migration.bundle"),base+"..HEAD"],check=True)
subprocess.run(["git","bundle","verify",str(out/"migration.bundle")],check=True)
subprocess.run(["git","apply","--check",str(out/"migration-candidate.patch")],check=True)
(out/"HANDOFF.md").write_text(f"Committed head: {head}\nBase: {base}\nRepository: {root}\nBranch: {branch}\n\n"+(root/"docs/feature-work/h62-6-migrate-hash.md").read_text())
generated = out/"generated"
generated.mkdir(exist_ok=True)
for name in ("CollisionBound.lean","Adaptive.lean","Inventory.lean","census.json"):
    shutil.copyfile(root/"tests/h62/item6/migrate-hash"/name,generated/name)
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
"checkpoints":[{"name":"1 census and clean old native build","status":"done"},{"name":"2 official pin and adaptation","status":"blocked"},{"name":"3 new native comparison and affected validation","status":"blocked"},{"name":"4 migration patch and root-gate handoff","status":"partial"}],
"gates":[
{"command":"git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master","status":"pass","evidence":"remote fetched; isolated branch starts at exact published base"},
{"command":"python3 scripts/h62/item6/migrate-hash/measure.py /workspace/.setup/tools/lean-4.24.0-linux /workspace/migrate-hash-evidence/old-lake-clean-3 --lake-overlay","status":"pass","evidence":str(out/"old-lake-clean-3/results.json")},
{"command":"python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /workspace/migrate-hash-evidence/new-lake-clean-2 --lake-overlay --fixture","status":"pass","evidence":str(out/"new-lake-clean-2/results.json")},
{"command":"python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /workspace/migrate-hash-evidence/new-acceptance-3 --fixture --extra","status":"pass","evidence":str(out/"new-acceptance-3/results.json")},
{"command":"python3 scripts/h62/item6/migrate-hash/acceptance.py /workspace/migrate-hash-evidence","status":"pass","evidence":str(out/"acceptance-audit.log")},
{"command":"node scripts/check-layers.mjs","status":"pass","evidence":str(out/"layers.log")+": 857 core modules; zero frontend reach"},
{"command":"bash scripts/coord-tools/register.sh --check; bash scripts/coord-tools/fragments.sh --check","status":"pass","evidence":str(out/"roots.log")+"; "+str(out/"fragments.log")},
{"command":"bash scripts/check-doc-paths.sh","status":"fail","evidence":str(out/"doc-paths.log")+": pre-existing absent Bridge Mathlib SplitIfs.lean citation; scoped Markdown links pass"},
{"command":"git apply --check /workspace/migrate-hash-evidence/migration-candidate.patch; git diff --check","status":"pass","evidence":"candidate applies cleanly; originals unchanged; no whitespace errors"},
{"command":"full affected importer validation and ./run-lean.sh on root migration overlay","status":"pending","evidence":"owner coordination, production overlay and migration root integration pending"}],
"reviews":str(out/"reviews.md")+": independent finder and skeptic approve partial evidence; no Lean/server use; all material tooling findings fixed",
"limitations":"Production files unchanged. Exact-file owner coordination, RSS regression disposition, full affected/runtime gates and root-gate receipt remain pending. Global doc-path check has a pre-existing absent Mathlib reference. No final runtime pass or whole-assignment completion.",
"questions":[{"id":r["id"],"sources":r["sources"],"question":"ESCALATE: "+r["action"],"options":r["options"]} for r in coordination["requests"]],
"typed_blockers":["OWNER_COORDINATION_REQUIRED","PERFORMANCE_RSS_REGRESSION","ROOT_AFFECTED_RUNTIME_GATE_PENDING","PREEXISTING_DOC_PATH_MATHLIB_REFERENCE"],
"declarations_helpers":acceptance,"frozen_statements_touched":[],"performance":performance,
"artifacts":{"original_patch":str(out/"original.patch"),"candidate_patch":str(out/"migration-candidate.patch"),"bundle":str(out/"migration.bundle"),"handoff":str(out/"HANDOFF.md"),"evidence":str(out),"archive":str(archive),"checksums":str(out/"SHA256SUMS")}}
result["artifact_sha256"] = {p.name:hashlib.file_digest(p.open("rb"),"sha256").hexdigest() for p in [out/"original.patch",out/"migration-candidate.patch",out/"migration.bundle",out/"HANDOFF.md",archive]}
(out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
paths = [p for p in sorted(out.rglob("*")) if included(p)] + [archive,out/"result.json"]
(out/"SHA256SUMS").write_text("".join(hashlib.file_digest(p.open("rb"),"sha256").hexdigest()+"  "+str(p.relative_to(out))+"\n" for p in paths))
print(json.dumps({"head":head,"status":"blocked","artifacts":result["artifacts"],"artifact_sha256":result["artifact_sha256"]},indent=2))
