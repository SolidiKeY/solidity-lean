#!/usr/bin/env python3
"""Reproduce supplied Hash-owner blob in an off-Git fixture; no branch overlay."""
import argparse, fcntl, hashlib, json, os, resource, subprocess
from pathlib import Path
from bounded import run, settings, passed
ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--verify-only',action='store_true'); a=ap.parse_args()
root=Path.cwd(); out=a.out.resolve(); out.mkdir(parents=True,exist_ok=False)
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','w'); fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('SwapTotal:'))): raise SystemExit('SWAP_BLOCK')
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'; rel=Path('Solidity/Hash/CollisionBound.lean')
old=subprocess.check_output(['git','show',base+':'+str(rel)]); text=old.decode()
base_blob=subprocess.check_output(['git','rev-parse',base+':'+str(rel)],text=True).strip()
if subprocess.check_output(['git','hash-object','--stdin'],input=old).decode().strip()!=base_blob: raise SystemExit('OWNER_BASE_MISMATCH')
text=text.replace('      if_true] <;> omega','      ite_true] <;> omega')
text=text.replace('      congr 1\n    rw [hsplit','      simp only [List.contains_cons]\n    rw [hsplit')
text=text.replace('simp only [List.map_cons, oracleOf, if_pos]','simp only [List.map_cons, oracleOf, ite_eq_left]')
text=text.replace('simp only [if_neg this]','simp only [ite_eq_right this]')
text=text.replace('if_pos hx','ite_eq_left hx').replace('if_neg hx','ite_eq_right hx')
text=text.replace("    simp only [decide_eq_true_eq, Near] at hn", "    have hn' : Near N L a b := of_decide_eq_true hn\n    unfold Near at hn'")
text=text.replace("    simp only [decide_eq_true_eq, Covers] at hn", "    have hn' : Covers N L a r := of_decide_eq_true hn\n    unfold Covers at hn'")
new=text.encode(); blob=subprocess.check_output(['git','hash-object','--stdin'],input=new).decode().strip()
expected_blob='092971eda8c7d6997276a92ba19b25b7ce05844e'
if blob!=expected_blob:
    (out/'verification.json').write_text(json.dumps({'status':'OWNER_RESULT_BLOB_MISMATCH','actual':blob,'expected':expected_blob}))
    raise SystemExit('OWNER_RESULT_BLOB_MISMATCH: '+blob)
original=out/'original.lean'; original.write_bytes(old); target=out/rel; target.parent.mkdir(parents=True); target.write_bytes(new)
r=subprocess.run(['git','diff','--no-index','--abbrev=9','--',str(original),str(target)],capture_output=True,text=True)
if r.returncode!=1: raise SystemExit('DIFF_FAILED')
patch=r.stdout.replace('a/'+str(original).lstrip('/'),'a/'+str(rel)).replace('b/'+str(target).lstrip('/'),'b/'+str(rel))
(out/'owner-overlay.patch').write_text(patch)
patch_hash=hashlib.sha256(patch.encode()).hexdigest()
# Exact blob match is mandatory. The supplied transport SHA is checked separately.
expected='3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff'
(out/'verification.json').write_text(json.dumps({'status':'verified' if patch_hash==expected else 'OWNER_PATCH_SHA256_MISMATCH','base_git_blob':base_blob,'result_git_blob':blob,'actual_patch_sha256':patch_hash,'expected_patch_sha256':expected},indent=2)+'\n')
if patch_hash!=expected: raise SystemExit('OWNER_PATCH_SHA256_MISMATCH')
if a.verify_only:
    print('PASS: exact owner blob and transport SHA256; verification only, no Lean check')
    raise SystemExit(0)
cmd=['/workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux/bin/lean','-j1','--tstack=131072','-o',str(out/'CollisionBound.olean'),str(rel)]
result=run(cmd,log=out/'compile.log',cwd=out,env=dict(os.environ,LEAN_NUM_THREADS='1'))
report={'owner':'migrate-hash','owner_ticket_head':'a3f49ee0ec1829e63022c90194048d5a1ffe0d22','owner_source_head':'2a18afcdba00a85645b0b3079704f78ffcd78860','base':base,'file':str(rel),'result_git_blob':blob,'supplied_patch_sha256':expected,'reconstructed_patch_sha256':patch_hash,'patch_transport_hash_equal':patch_hash==expected,'fixture_sha256':hashlib.sha256(new).hexdigest(),'command':cmd,'settings':settings(),**result,'cumulative_peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'boundary':'Owner overlay tested only in an off-Git fixture; branch Hash source unchanged; full gates pending.'}
(out/'result.json').write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report)); raise SystemExit(0 if passed(result) else 1)
