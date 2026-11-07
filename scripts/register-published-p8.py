#!/usr/bin/env python3
"""Deduplicate only the exact published P8 interface registrations after rebase."""
import re,json
from pathlib import Path
root=Path(__file__).resolve().parents[1];path=root/'Solidity.lean'
modules={'Solidity.Lowering.P8.FrozenInterface','Solidity.Lowering.P8b.Frozen','Solidity.Lowering.P8b.P8aInterface','Solidity.Source.FailureResources'}
# Import-only root: preserve comments and all unrelated registrations. Reject
# ambiguous comment-bearing imports rather than silently rewrite their text.
text=path.read_text();code=[];i=0;depth=0
while i<len(text):
 if text.startswith('/-',i):depth+=1;code.extend('  ');i+=2
 elif depth and text.startswith('-/',i):depth-=1;code.extend('  ');i+=2
 elif depth:code.append('\n' if text[i]=='\n' else ' ');i+=1
 elif text.startswith('--',i):
  end=text.find('\n',i);end=len(text) if end<0 else end;code.extend(' '*(end-i));i=end
 else:code.append(text[i]);i+=1
assert depth==0
seen=set();removed=[];out=[]
for raw,line in zip(text.splitlines(),''.join(code).splitlines(),strict=True):
 m=re.fullmatch(r'\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*',line)
 assert not line.strip() or m,'unsupported root code'
 if m and m[1] in modules:
  assert re.fullmatch(r'\s*import\s+'+re.escape(m[1])+r'\s*(?:--.*)?',raw),'ambiguous published import'
  if m[1] in seen:removed.append(m[1]);continue
  seen.add(m[1])
 out.append(raw)
assert seen==modules,'missing published interface root'
path.write_text('\n'.join(out)+'\n');print(json.dumps({'removed_duplicate_imports':removed}))
