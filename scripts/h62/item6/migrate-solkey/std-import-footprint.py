#!/usr/bin/env python3
"""Static SDK source-import footprint; not a memory profiler or Lean gate."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--toolchain',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise SystemExit('Refusing overwrite')
root=a.toolchain.resolve()/'src/lean'
seeds=['Init.Data.String.Basic','Init.Data.String.Lemmas']
rows={}
def header_imports(text):
 depth=0;result=[]
 for line in text.splitlines():
  clean=[];i=0
  while i<len(line):
   pair=line[i:i+2]
   if pair=='/-':depth+=1;i+=2;continue
   if depth and pair=='-/':depth-=1;i+=2;continue
   if not depth and pair=='--':break
   if not depth:clean.append(line[i])
   i+=1
  value=''.join(clean).strip()
  if not value or value in {'module','prelude'}:continue
  match=re.fullmatch(r'(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.+)',value)
  if not match:break
  result.extend(n for n in match[1].split() if n!='all')
 if depth:raise ValueError('unclosed header comment')
 return result
def visit(name):
 if name in rows:return
 path=root/(name.replace('.','/')+'.lean')
 if not path.exists():rows[name]={'missing_source':True};return
 raw=path.read_bytes();deps=header_imports(raw.decode())
 rows[name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'imports':deps}
 for dep in deps:visit(dep)
for name in seeds:visit(name)
def closure(name):
 seen=set();todo=[name]
 while todo:
  n=todo.pop()
  if n not in seen:seen.add(n);todo.extend(rows[n].get('imports',[]))
 return seen
counts={n:{'modules':len(closure(n)),'source_bytes':sum(rows[k].get('bytes',0) for k in closure(n))} for n in seeds}
data={'schema_version':1,'toolchain_source_root':str(root),'boundary':'Static source footprint only; not measured live memory or causal attribution; does not lift STOP','seeds':counts,'records':dict(sorted(rows.items()))}
a.out.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(counts,indent=2))
