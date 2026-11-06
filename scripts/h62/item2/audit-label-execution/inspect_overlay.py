#!/usr/bin/env python3
"""Inspect the routed single-file Hash overlay entirely in memory.

No original write or Lean execution. Equal source signatures do not prove the
replacement proofs, their axioms, migration completion, or permission to apply.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import census

PATH = 'Solidity/Hash/CollisionBound.lean'

def apply_in_memory(original, patch):
    lines = patch.splitlines(keepends=True)
    expected = f'diff --git a/{PATH} b/{PATH}\n'
    if not lines or lines[0] != expected or sum(l.startswith('diff --git ') for l in lines) != 1:
        raise ValueError('only the exact routed Hash path is supported')
    if len(lines)<5 or not re.fullmatch(r'index [0-9a-f]{7,40}\.\.[0-9a-f]{7,40} 100644\n',lines[1]) or lines[2] != f'--- a/{PATH}\n' or lines[3] != f'+++ b/{PATH}\n' or not lines[4].startswith('@@ '):
        raise ValueError('unsupported or duplicate pre-hunk metadata')
    source = original.splitlines(keepends=True)
    result = []
    cursor = 0
    i = 4
    hunks = 0
    while i < len(lines):
        if not lines[i].startswith('@@ '):
            if hunks: raise ValueError('unexpected text after hunk')
            i += 1; continue
        m = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
        if not m: raise ValueError('invalid hunk header')
        old_start, old_count, new_start, new_count = [int(m[1]),int(m[2] or 1),int(m[3]),int(m[4] or 1)]
        if old_count < 1 or new_count < 1: raise ValueError('zero-count hunks unsupported by routed overlay inspector')
        if old_start < 1 or old_start-1 < cursor or old_start-1+old_count>len(source): raise ValueError('overlapping/out-of-range hunk')
        result.extend(source[cursor:old_start-1]); cursor = old_start-1
        if len(result) != new_start-1: raise ValueError('new hunk offset mismatch')
        consumed = produced = 0
        i += 1
        while i < len(lines) and not lines[i].startswith('@@ '):
            line = lines[i]
            if not line or line[0] not in ' +-': raise ValueError('unsupported hunk content')
            if line[0] in ' -':
                if cursor >= len(source) or source[cursor] != line[1:]: raise ValueError('frozen hunk context mismatch')
                consumed += 1; cursor += 1
            if line[0] in ' +': result.append(line[1:]); produced += 1
            i += 1
        if (consumed,produced) != (old_count,new_count): raise ValueError('hunk line-count mismatch')
        hunks += 1
    if not hunks: raise ValueError('empty overlay')
    result.extend(source[cursor:])
    return ''.join(result)

def inspect(root, receipt_path, artifact_override=None):
    receipt = json.loads(receipt_path.read_text())
    if Path(receipt['artifact']).name != receipt['artifact']: raise ValueError('artifact name must be a basename')
    patch_path = artifact_override or Path(receipt.get('artifact_path',str(receipt_path.parent / receipt['artifact'])))
    data = patch_path.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != receipt['reported_sha256']: raise ValueError('routed patch checksum mismatch')
    if receipt['source_path'] != PATH: raise ValueError('receipt path mismatch')
    before = census.frozen_bytes(root, PATH)
    after = apply_in_memory(before.decode(), data.decode()).encode()
    def signatures(source):
        return [(r['name'],r['signature_sha256']) for r in census.declarations(source.decode(),PATH)]
    old_sigs,new_sigs = signatures(before),signatures(after)
    if old_sigs != new_sigs: raise ValueError('overlay changes named source signatures')
    def blob(data): return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    m = re.search(r'(?m)^index ([0-9a-f]+)\.\.([0-9a-f]+) ',data.decode())
    if not m or not blob(before).startswith(m[1]) or not blob(after).startswith(m[2]):
        raise ValueError('Git preimage/postimage index mismatch')
    return dict(base=census.BASE,path=PATH,patch_sha256=actual,reported_owner_head=receipt['reported_head'],
                reported_source_head=receipt['reported_source_head'],reported_heads_independently_verified=False,
                preimage_sha256=census.digest(before),postimage_sha256=census.digest(after),
                source_signatures_unchanged=len(old_sigs),frozen_hunks_match=True,
                original_files_written=0,overlay_applied=False,lean_executed=False,
                proof_validation='pending; source text inspection only',
                migration_gate='pending; partial owner overlay does not discharge other blockers',
                routing='delivery acceptance is not owner agreement or validation')

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[4])
    p.add_argument('--receipt',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--artifact',type=Path,help='explicit relocated routed artifact; checksum remains mandatory')
    args=p.parse_args()
    result=inspect(args.root,args.receipt,args.artifact)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True))
