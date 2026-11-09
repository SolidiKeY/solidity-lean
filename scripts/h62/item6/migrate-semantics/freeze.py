#!/usr/bin/env python3
"""Freeze source and changed public theorem headers; not elaborated API equivalence."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
ap=argparse.ArgumentParser(); ap.add_argument('--base',required=True); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
rows=[]
for p in sorted(Path.cwd().glob('Solidity/Semantics/**/*.lean')):
    rel=str(p.relative_to(Path.cwd())); old=subprocess.check_output(['git','show',a.base+':'+rel]); new=p.read_bytes()
    row={'path':rel,'base_sha256':hashlib.sha256(old).hexdigest(),'current_sha256':hashlib.sha256(new).hexdigest(),'whole_source_equal':old==new}
    if old!=new:
        def signatures(data):
            text=data.decode(); result={}
            for m in re.finditer(r'^theorem\s+(\S+)\s',text,re.M):
                end=text.find(':=',m.end())
                if end<0: raise ValueError('unsupported theorem header '+m[1])
                sig=' '.join(text[m.start():end].split()); result[m[1]]=hashlib.sha256(sig.encode()).hexdigest()
            return result
        before=signatures(old); after=signatures(new)
        if before!=after: raise SystemExit('PUBLIC_HEADER_CHANGE: '+rel)
        row['public_theorem_signature_sha256']=before
    rows.append(row)
a.out.write_text(json.dumps({'base':a.base,'boundary':'Original source hashes and changed-file lexical public theorem headers. Not elaborated API equivalence; private helpers reviewed separately.','rows':rows},indent=2)+'\n')
print('PASS: source hashes and unchanged lexical public theorem headers for',len(rows),'files')
