#!/usr/bin/env python3
"""Static exact-commit provenance for H70 root-gate; never invokes Lean/applies source."""
import hashlib, json, pathlib, shutil, subprocess
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
HEAD="2a18afcdba00a85645b0b3079704f78ffcd78860"
ROOT=pathlib.Path.cwd()
EVIDENCE=pathlib.Path("/workspace/migrate-hash-evidence")
OUT=EVIDENCE/"source-provenance-2a18afcdb"
PATHS=("Solidity/Hash/CollisionBound.lean","Solidity/Hash/Adaptive.lean")
def git(*args): return subprocess.check_output(["git",*args])
def sha(data): return hashlib.sha256(data).hexdigest()
subprocess.run(["git","merge-base","--is-ancestor",BASE,HEAD],check=True)
subprocess.run(["git","merge-base","--is-ancestor",HEAD,"HEAD"],check=True)
commit=git("cat-file","commit",HEAD)
assert hashlib.sha1(b"commit "+str(len(commit)).encode()+b"\0"+commit).hexdigest()==HEAD
bundle=EVIDENCE/"checkpoint-2a18afcdb/migration.bundle"
subprocess.run(["git","bundle","verify",str(bundle)],check=True,stdout=subprocess.DEVNULL)
refs=git("bundle","list-heads",str(bundle)).decode().splitlines()
assert refs==[HEAD+" HEAD"],refs
files=[]
for path in PATHS:
    before=git("show",BASE+":"+path); after=git("show",HEAD+":"+path)
    assert (ROOT/path).read_bytes()==after,"current source differs from reviewed source head"
    files.append({"path":path,"base_blob":git("rev-parse",BASE+":"+path).decode().strip(),"head_blob":git("rev-parse",HEAD+":"+path).decode().strip(),"base_sha256":sha(before),"head_sha256":sha(after)})
# Bind retained passing claims to the exact reviewed sources, without rerunning Lean.
run=EVIDENCE/"new-production-acceptance-1"
results=json.loads((run/"results.json").read_text())
assert [r["module"] for r in results]==["Solidity.KeySort","Solidity.Hash.CollisionBound","Solidity.Hash.Adaptive","tests.h62.item6.migrate-hash.ProductionInventory","tests.h62.item6.migrate-hash.ProductionControls"]
assert all(r["exit"]==0 and r["input_unchanged"] and not r["resource_stop"] for r in results)
settings=json.loads((run/"settings.json").read_text())
for path,digest in settings["source_sha256"].items():
    assert sha((run/"inputs"/path).read_bytes())==digest
for path in PATHS:
    assert settings["source_sha256"][path]==sha(git("show",HEAD+":"+path))
versions=json.loads((run/"versions.json").read_text())
assert "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" in versions[0]["output"]
patch=git("diff","--binary",BASE,HEAD,"--",*PATHS)
assert sha(patch)=="b07f36b08faf0244fd350a54c9d72e3f5c333a566726b1e7f420aa21b727ffec"
if OUT.exists():
    manifest=json.loads((OUT/"manifest.json").read_text())
    assert manifest["base"]==BASE and manifest["head"]==HEAD and manifest["files"]==files
    for artifact in manifest["artifacts"].values():
        assert sha(pathlib.Path(artifact["path"]).read_bytes())==artifact["sha256"]
    print(json.dumps({"status":"existing immutable provenance verified","path":str(OUT/"manifest.json"),"sha256":sha((OUT/"manifest.json").read_bytes())},indent=2))
    raise SystemExit(0)
OUT.mkdir()
(OUT/"source.commit").write_bytes(commit)
(OUT/"hash-owner-overlay.patch").write_bytes(patch)
(OUT/"source-full.patch").write_bytes(git("diff","--binary",BASE,HEAD))
shutil.copyfile(bundle,OUT/"source.bundle")
run=EVIDENCE/"new-production-acceptance-1"
for name in ("results.json","settings.json","versions.json","Solidity.Hash.CollisionBound.log","Solidity.Hash.Adaptive.log","tests.h62.item6.migrate-hash.ProductionInventory.log","tests.h62.item6.migrate-hash.ProductionControls.log"):
    shutil.copyfile(run/name,OUT/name)
shutil.copyfile(EVIDENCE/"reviews.md",OUT/"reviews.md")
artifacts={p.name:{"path":str(p),"sha256":sha(p.read_bytes())} for p in sorted(OUT.iterdir()) if p.is_file()}
manifest={"schema":1,"request":"H70 OVERLAY_PROVENANCE_ONLY from migrate-root-gate ac7d4535b16c9a393a2b86ec91dd44fae2f418f2","producer":"solidity-h62-6-20261106/migrate-hash","base":BASE,"head":HEAD,"base_tree":git("rev-parse",BASE+"^{tree}").decode().strip(),"head_tree":git("rev-parse",HEAD+"^{tree}").decode().strip(),"parent":git("rev-parse",HEAD+"^").decode().strip(),"commit_object_sha256":sha(commit),"files":files,"artifacts":artifacts,"toolchain":"leanprover/lean4:v4.35.0","official_archive_sha256":"7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d","gate_boundary":"Retained source-bound production checks pass: KeySort, both Hash modules,121 named APIs,97 theorem axiom audits,4 instances,19 finite kernel controls. Frozen embedded axiom guards pass. This is not full affected/runtime validation, a transitive axiom review of unrelated modules, or cut-over approval.","static_checks":["base ancestry","source-head ancestry in current branch","commit object SHA1","bundle verify and exact HEAD ref","base/head blob and SHA256 hashes","exact scoped patch digest","current production bytes equal reviewed source head"],"permission_boundary":"Static provenance only. No Lean rerun, source application, baseline restart, budget change, STOP disposition, root edit or ownership transfer.","peer_receipt":{"requester":"solidity-h62-4-20261106/generic-primitive-packets","head":"0a34d9c508ca24f6a914553953a0bc4abf5863dc","source":"coordinator H70 inline blockers.json","reported":"Both Hash modules checked in isolated staged source; Hash dependency cleared for isolated consumer check; Roadmap.Contracts trust guard remains separate owner blocker.","independently_replayed":False}}
(OUT/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps({"status":"exact source-commit provenance ready","path":str(OUT/"manifest.json"),"sha256":sha((OUT/"manifest.json").read_bytes()),"bundle":artifacts["source.bundle"]},indent=2))
