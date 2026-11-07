#!/usr/bin/env python3
"""Owner overlay provenance/postimage and unchanged-production negative controls."""
import hashlib,json,pathlib,subprocess,sys,tempfile
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"scripts/h62/item6/migrate-storage"))
from prepare_owner_overlay import validate_postimage,EXPECTED_PATCH,EXPECTED_POSTIMAGE,blob
from census import frozen_matches
E=pathlib.Path("/workspace/migrate-storage-evidence")
patch=ROOT/"tests/h62/item6/migrate-storage/collision-bound-owner.patch"
assert hashlib.sha256(patch.read_bytes()).hexdigest()==EXPECTED_PATCH
names=subprocess.check_output(["git","apply","--numstat",str(patch)],cwd=ROOT,text=True).splitlines()
assert len(names)==1 and names[0].split("\t")[-1]=="Solidity/Hash/CollisionBound.lean"
m=json.loads((E/"h70-source-manifest.json").read_text());source=pathlib.Path(m["source_root"])
assert frozen_matches(ROOT,m["original_tree_sha256"])
assert frozen_matches(source,m["tree_sha256"])
assert [p for p in m["tree_sha256"] if m["tree_sha256"][p]!=m["original_tree_sha256"][p]]==[m["changed_file"]]
valid=source/m["changed_file"];validate_postimage(valid);assert blob(valid.read_bytes())==EXPECTED_POSTIMAGE
try:validate_postimage(ROOT/m["changed_file"])
except AssertionError:pass
else:raise AssertionError("unpached owner source accepted")
with tempfile.TemporaryDirectory(prefix="storage-owner-negative-") as tmp:
 p=pathlib.Path(tmp)/"CollisionBound.lean";p.write_bytes(valid.read_bytes()+b"\n")
 try:validate_postimage(p)
 except AssertionError:pass
 else:raise AssertionError("edited postimage accepted")
print("OWNER_OVERLAY_NEGATIVE_CONTROLS_PASS (exact relay digest, only owner path, exact postimage, original and fixture hashes, unpatched/tampered rejection)")
