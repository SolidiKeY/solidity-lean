#!/usr/bin/env python3
"""Materialize the exact H70 Hash-owner overlay in a private test tree only."""
import fcntl,hashlib,json,pathlib,re,subprocess,sys
from census import ROOT,census,digest,frozen_matches
EXPECTED_PATCH="3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff"
OWNER_FILE="Solidity/Hash/CollisionBound.lean"
def blob(b):return hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
EXPECTED_POSTIMAGE="092971eda8c7d6997276a92ba19b25b7ce05844e"
def validate_postimage(path):
 assert blob(path.read_bytes())==EXPECTED_POSTIMAGE,"owner Hash postimage mismatch"
def prepare(source,manifest):
 assert source.is_absolute() and manifest.is_absolute() and not source.exists() and not manifest.exists()
 assert not source.is_relative_to(ROOT),"fixture must stay outside checkout"
 lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","r+");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 subprocess.run(["git","-C",str(ROOT),"status","--short","--branch"],check=True)
 patch=ROOT/"tests/h62/item6/migrate-storage/collision-bound-owner.patch"
 assert digest(patch.read_bytes())==EXPECTED_PATCH
 c=census();assert c["closure_matches_checkout"] and all(f["unchanged"] for f in c["files"])
 source.mkdir()
 paths=[m.replace(".","/")+".lean" for m in c["build_order"]]
 paths += ["tests/h62/item6/migrate-storage/ApiControls.lean","tests/h62/item6/migrate-storage/InterfaceHashes.lean"]
 original={}
 for name in paths:
  b=(ROOT/name).read_bytes();original[name]=digest(b);p=source/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 assert blob((source/OWNER_FILE).read_bytes()).startswith("b54c93a5b")
 subprocess.run(["git","apply","--check",str(patch)],cwd=source,check=True)
 subprocess.run(["git","apply",str(patch)],cwd=source,check=True)
 patched=(source/OWNER_FILE).read_bytes();validate_postimage(source/OWNER_FILE)
 assert re.findall(rb"set_option\s+(?:maxHeartbeats|maxRecDepth)\s+\S+",patched)==re.findall(rb"set_option\s+(?:maxHeartbeats|maxRecDepth)\s+\S+",(ROOT/OWNER_FILE).read_bytes())
 actual={p:digest((source/p).read_bytes()) for p in paths}
 assert [p for p in paths if actual[p]!=original[p]]==[OWNER_FILE]
 assert frozen_matches(ROOT,original)
 for name in paths:(source/name).chmod(0o444)
 record={"kind":"H70 exact owner patch in private fixture only","source_root":str(source),"owner":"solidity-h62-6-20261106/migrate-hash","reported_owner_head":"a3f49ee0ec1829e63022c90194048d5a1ffe0d22","owner_source_commit":"2a18afcd","patch_path":str(patch),"patch_sha256":EXPECTED_PATCH,"changed_file":OWNER_FILE,"old_git_blob":blob((ROOT/OWNER_FILE).read_bytes()),"new_git_blob":blob(patched),"base_closure_source_sha256":c["closure_source_sha256"],"original_tree_sha256":original,"tree_sha256":actual,"production_sources_edited":False,"full_affected_gates":"pending"}
 manifest.write_text(json.dumps(record,indent=2,sort_keys=True)+"\n")
 print("OWNER_OVERLAY_VERIFIED",manifest,record["new_git_blob"])
if __name__=="__main__":prepare(pathlib.Path(sys.argv[1]),pathlib.Path(sys.argv[2]))
