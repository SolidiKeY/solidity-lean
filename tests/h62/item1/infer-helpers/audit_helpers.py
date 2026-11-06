#!/usr/bin/env python3
"""Render an external axiom probe from exact additive source declaration text."""
import argparse, hashlib, json, pathlib, re
p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4]
assert not a.output.resolve().is_relative_to(root.resolve()), 'external output required'
folder=root/'tests/h62/item1/infer-helpers';imports=set();bodies=[];names=[];sources={}
for name in ['Shared.lean','CaseSpecifications.lean','CompletenessCompatibility.lean']:
 path=folder/name;text=path.read_text();sources[str(path.relative_to(root))]=hashlib.sha256(path.read_bytes()).hexdigest()
 namespace=re.findall(r'^namespace (\S+)$',text,re.M);assert len(namespace)==1
 for line in text.splitlines():
  if line.startswith('import '):imports.add(line)
 body='\n'.join(line for line in text.splitlines() if not line.startswith('import '))+'\n'
 bodies.append(body)
 names.extend(namespace[0]+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)\b',text,re.M))
assert len(names)==31 and len(set(names))==31
probe='\n'.join(sorted(imports))+'\n\n'+ '\n'.join(bodies)+'\n'+''.join('#print axioms '+name+'\n' for name in names)
a.output.mkdir(exist_ok=False);(a.output/'Probe.lean').write_text(probe)
(a.output/'manifest.json').write_text(json.dumps(dict(sources=sources,declarations=names,probe_sha256=hashlib.sha256(probe.encode()).hexdigest(),boundary='Declaration text preserved; imports unioned for probe. Original modules require their individual checks. Not a full migration or inferencer-equivalence gate.'),indent=2)+'\n')
print('Rendered',len(names),'declaration axiom queries')
