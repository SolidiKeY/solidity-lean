#!/usr/bin/env python3
"""Stage only the exact H70 owner-reviewed Hash overlay, never checkout writes."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
from census import ROOT, BASE

OWNER_HEAD='2a18afcdba00a85645b0b3079704f78ffcd78860'
BLOBS={
 'Solidity/Hash/CollisionBound.lean':('b54c93a5b24340a19160c1fb378d057ccee60f84','092971eda8c7d6997276a92ba19b25b7ce05844e'),
 'Solidity/Hash/Adaptive.lean':('cb5d5a1c61f7350aa01d9d0c81c8f4403b19fab3','20087c3f9525d6773c008708678eb67876ab9e14')}


def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def replace_once(text,old,new):
    if text.count(old)!=1:
        raise ValueError('owner hunk does not match exactly once: '+old)
    return text.replace(old,new)


def stage(destination):
    if destination.exists() or destination.is_symlink():
        raise ValueError('owner staging requires a fresh nonexisting destination')
    destination=destination.resolve()
    if destination==ROOT or ROOT in destination.parents:
        raise ValueError('source overlay must remain outside the checkout')
    destination.mkdir(parents=True,exist_ok=False)
    rows=[]; patch=[]
    for relative,(before,expected_after) in BLOBS.items():
        raw=(ROOT/relative).read_bytes()
        published=subprocess.check_output(['git','show',f'{BASE}:{relative}'],cwd=ROOT)
        if raw!=published or blob(raw)!=before:
            raise ValueError('exact published base mismatch: '+relative)
        old=raw.decode()
        new=old.replace('if_pos','ite_eq_left').replace('if_neg','ite_eq_right')
        if relative.endswith('CollisionBound.lean'):
            new=new.replace('if_true','ite_true')
            new=replace_once(new,'A.countP (fun a => (a == x) || t.contains a) := by\n      congr 1','A.countP (fun a => (a == x) || t.contains a) := by\n      simp only [List.contains_cons]')
            for name in ('Near','Covers'):
                new=replace_once(new,f'    simp only [decide_eq_true_eq, {name}] at hn',f"    have hn' : {name} N L a {'b' if name=='Near' else 'r'} := of_decide_eq_true hn\n    unfold {name} at hn'")
        else:
            for function,empty in [('eagerCollides','CollisionFree'),('eagerRegionsFail','RegionsDisjoint')]:
                new=replace_once(new,f'      simp only [{function}, eagerQueries, decide_eq_true_eq, Classical.not_not]\n      exact {empty}.nil',f'      simp only [{function}, eagerQueries]\n      exact fun h => (of_decide_eq_true h) {empty}.nil')
        encoded=new.encode(); after=blob(encoded)
        if after != expected_after:
            raise ValueError(f'owner postimage mismatch: {relative}: {after}')
        output=destination/relative
        if not output.resolve().is_relative_to(destination) or output.is_symlink():
            raise ValueError('owner staging output escapes fresh source root')
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_bytes(encoded)
        rows.append(dict(path=relative,base_blob=before,owner_post_blob=after,sha256=hashlib.sha256(encoded).hexdigest()))
        patch.append(f'diff --git a/{relative} b/{relative}\nindex {before}..{after} 100644\n')
        patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+relative,tofile='b/'+relative))
    manifest=dict(base=BASE,owner='solidity-h62-6-20261106/migrate-hash',owner_head=OWNER_HEAD,authorization='H70 isolated migration use only; no checkout-original edit permission',files=rows)
    (destination/'owner-overlay.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (destination/'owner-overlay.patch').write_text(''.join(patch))
    print(json.dumps(manifest,indent=2))
    print('EXACT_OWNER_OVERLAY_STAGE_PASS; checkout originals unchanged')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination',type=Path)
    stage(parser.parse_args().destination)
