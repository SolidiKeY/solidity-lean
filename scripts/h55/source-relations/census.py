#!/usr/bin/env python3
"""Read-only import and textual-consumer census; no owner inference."""
import hashlib,json,pathlib,re,subprocess
from lean_imports import header_imports
root=pathlib.Path(__file__).resolve().parents[3]
paths=['Solidity/Backend/Scalar/Typed.lean','Solidity/Frontend/Static/Infer.lean','Solidity/Lowering/V07/ContextMap.lean','Solidity/Lowering/V07/Scalar.lean','Solidity/Source/Agreement/Locals.lean','Solidity/Source/Agreement/PrimitiveTypes.lean','Solidity/Source/Infer.lean']
files=subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard'],cwd=root).decode().split('\0')
def module(path):
    for prefix in ['vendor/LeanTeX/','Bridge/']:
        if path.startswith(prefix):path=path[len(prefix):];break
    return path[:-5].replace('/','.')
lean_files=sorted(set(p for p in files if p.endswith('.lean') and not p.startswith('tests/') and (root/p).is_file()))
graph={module(p):header_imports((root/p).read_text()) for p in lean_files}
reverse={}
for mod,deps in graph.items():
    for dep in deps:reverse.setdefault(dep,set()).add(mod)
rows=[]
for path in paths:
    mod=path[:-5].replace('/','.');seen=set();stack=list(reverse.get(mod,()))
    while stack:
        c=stack.pop()
        if c in seen:continue
        seen.add(c);stack.extend(reverse.get(c,()))
    rows.append({'input':path,'sha256':hashlib.sha256((root/path).read_bytes()).hexdigest(),'owner':'pending coordinator notice','lease':'migration input only','direct_importers':sorted(reverse.get(mod,())),'transitive_consumers':sorted(seen)})
pattern=re.compile(r'\b(?:PrimitiveRel|IntValueRel|LocalsRel|ValueRelation|ValueRel|inferN|isMappingTy|isPayableArg|payableArg|convLoc)\b')
references=[]
for name in lean_files:
    path=root/name
    for line,text in enumerate(path.read_text().splitlines(),1):
        if pattern.search(text):references.append({'path':str(path.relative_to(root)),'line':line,'text':text})
print(json.dumps({'base':'4d3790eadb8a5212233bc7d5e345817476b2f590','inventory_boundary':'repository Lean files including generated roots, Bridge, executables, vendor and scripts; tests excluded; textual names require owner resolution','inputs':rows,'textual_candidates_not_resolved_identifiers':references},indent=2))
