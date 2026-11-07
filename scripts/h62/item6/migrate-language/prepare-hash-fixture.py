#!/usr/bin/env python3
"""Validate a relayed owner patch in an off-Git fixture, never the owned original.
Usage: prepare-hash-fixture.py PATCH FIXTURE_DIRECTORY
Compile the resulting absolute file with the existing bounded measure.py driver.
"""
import hashlib,json,pathlib,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
patch=pathlib.Path(sys.argv[1]).resolve();dest=pathlib.Path(sys.argv[2]).resolve()
expected='3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff'
assert hashlib.sha256(patch.read_bytes()).hexdigest()==expected,'Unverified receipt: STOP'
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4';rel='Solidity/Hash/CollisionBound.lean'
def git(*args):return subprocess.check_output(['git',*args],cwd=repo)
original=git('show',base+':'+rel)
assert (repo/rel).read_bytes()==original,'Unexpected owned-original change: STOP'
assert git('hash-object',str(repo/rel)).decode().strip()=='b54c93a5b24340a19160c1fb378d057ccee60f84'
assert not dest.exists(),'Preserve existing fixture evidence'
dest.mkdir(parents=True);source=dest/rel;source.parent.mkdir(parents=True);source.write_bytes(original)
subprocess.run(['git','apply','--check',str(patch)],cwd=dest,check=True)
subprocess.run(['git','apply',str(patch)],cwd=dest,check=True)
blob=git('hash-object',str(source)).decode().strip();assert blob=='092971eda8c7d6997276a92ba19b25b7ce05844e','Owner result blob mismatch: STOP'
assert (repo/rel).read_bytes()==original
receipt=dict(base=base,owner='solidity-h62-6-20261106/migrate-hash',owner_source_head='2a18afcdba00a85645b0b3079704f78ffcd78860',owner_delivery_head='a3f49ee0ec1829e63022c90194048d5a1ffe0d22',patch=str(patch),patch_sha256=expected,fixture=str(source),fixture_git_blob=blob,fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),original_git_blob='b54c93a5b24340a19160c1fb378d057ccee60f84',original_unchanged=True,git_apply_check_exit=0,boundary='Fixture preparation only; no Lean success, full Hash migration, cross-directory owner agreement, consumer acceptance or STOP waiver implied.')
(dest/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
