#!/usr/bin/env python3
"""Reproduce static review of the H70 routed partial Hash overlay.
Never applies an overlay to files or invokes Lean. Header equality is lexical,
not proof/axiom fidelity, successful migration, or authorization to release holds.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import census

EXPECTED='3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff'
TARGET='Solidity/Hash/CollisionBound.lean'

def apply_in_memory(old, patch):
    lines=old.splitlines(keepends=True); diff=patch.splitlines(keepends=True)
    result=[]; cursor=0; i=0; hunks=0
    while i<len(diff):
        m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',diff[i])
        if not m: i+=1; continue
        start=int(m.group(1))-1
        if start<cursor: raise ValueError('overlapping hunks')
        result.extend(lines[cursor:start]); cursor=start; i+=1; hunks+=1
        while i<len(diff) and not diff[i].startswith('@@ '):
            line=diff[i]
            if line.startswith((' ','-')):
                if cursor>=len(lines) or lines[cursor]!=line[1:]: raise ValueError('context mismatch')
                cursor+=1
            if line.startswith((' ','+')): result.append(line[1:])
            i+=1
    if not hunks: raise ValueError('no hunks')
    result.extend(lines[cursor:]);return ''.join(result)

def signatures(source):
    code=census.mask(source)
    return [(m.group(2),source[m.start():census.signature_end(code,m.end())].strip()) for m in census.COMMAND.finditer(code)]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--patch',required=True,type=pathlib.Path)
    ap.add_argument('--output',required=True,type=pathlib.Path);a=ap.parse_args()
    root=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
    output=a.output.resolve()
    if output==root or root in output.parents: ap.error('bulk output must be outside checkout')
    patch=a.patch.resolve();data=patch.read_bytes()
    if hashlib.sha256(data).hexdigest()!=EXPECTED: raise ValueError('routed artifact checksum mismatch')
    text=data.decode()
    if text.count('diff --git ')!=1 or not text.startswith('diff --git a/'+TARGET+' b/'+TARGET+'\n'): raise ValueError('unexpected patch target')
    old=census.frozen(root,TARGET).decode()
    check=subprocess.run(['git','apply','--check',str(patch)],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if check.returncode: raise ValueError(check.stdout)
    new=apply_in_memory(old,text)
    if signatures(old)!=signatures(new): raise ValueError('theorem signature changed')
    new_blob=subprocess.check_output(['git','hash-object','--stdin'],input=new.encode(),cwd=root).decode().strip()
    if not new_blob.startswith('092971eda'): raise ValueError('advertised new blob differs')
    if (root/TARGET).read_text()!=old: raise ValueError('original unexpectedly changed')
    result=dict(owner_head='78c110f83dc1a30700acd1b5bd34b19f61da6ccd',source_head='2a18afcdba00a85645b0b3079704f78ffcd78860',sha256=EXPECTED,hash_matches=True,apply_check_exit=0,applied=False,lean_runs=0,new_blob=new_blob,theorem_signature_pairs_unchanged=len(signatures(old)),boundary='Static context/header review only; no checked proof/axiom or migration gate; Syntax.Raw/full migration holds remain.')
    output.mkdir(parents=True,exist_ok=True)
    (output/'overlay-static-review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
