#!/usr/bin/env python3
"""Guard regression: preserve and query each of the31 named helper declarations once. Anonymous examples remain source-preserved but outside named-query coverage."""
import argparse, hashlib, json, pathlib, re
p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4]
assert not a.output.resolve().is_relative_to(root.resolve()), 'external output required'
folder=root/'tests/h62/item1/infer-helpers';imports={'import Solidity.Source.InferHelpers'};bodies=[];names=[];sources={}
canonical=root/'Solidity/Source/InferHelpers.lean'
canonical_text=canonical.read_text()
canonical_namespace=re.findall(r'^namespace (\S+)$',canonical_text,re.M)
assert len(canonical_namespace)==1
names.extend(canonical_namespace[0]+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)\b',canonical_text,re.M))
sources[str(canonical.relative_to(root))]=hashlib.sha256(canonical.read_bytes()).hexdigest()
shim=folder/'Shared.lean'
assert shim.read_text().splitlines()[0]=='import Solidity.Source.InferHelpers'
assert not re.search(r'^(?:def|theorem|example)\b',shim.read_text(),re.M)
sources[str(shim.relative_to(root))]=hashlib.sha256(shim.read_bytes()).hexdigest()
for name in ['CaseSpecifications.lean','CompletenessCompatibility.lean']:
 path=folder/name;text=path.read_text();sources[str(path.relative_to(root))]=hashlib.sha256(path.read_bytes()).hexdigest()
 namespace=re.findall(r'^namespace (\S+)$',text,re.M);assert len(namespace)==1
 for line in text.splitlines():
  if line.startswith('import '):imports.add(line)
 body='\n'.join(line for line in text.splitlines() if not line.startswith('import '))+'\n'
 bodies.append(body)
 names.extend(namespace[0]+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)\b',text,re.M))
assert len(names)==31 and len(set(names))==31
existing=re.findall(r'^#print axioms (\S+)$','\n'.join(bodies),re.M)
assert len(existing)==len(set(existing)) and set(existing)<=set(names)
probe='\n'.join(sorted(imports))+'\n\n'+ '\n'.join(bodies)+'\n'+''.join('#print axioms '+name+'\n' for name in names if name not in existing)
a.output.mkdir(exist_ok=False);(a.output/'Probe.lean').write_text(probe)
(a.output/'manifest.json').write_text(json.dumps(dict(sources=sources,declarations=names,probe_sha256=hashlib.sha256(probe.encode()).hexdigest(),boundary='Canonical shared declarations imported through production module; remaining declaration text preserved and imports unioned for probe. Original modules require their individual checks. Not a full migration or inferencer-equivalence gate.'),indent=2)+'\n')
print('Rendered',len(names),'declaration axiom queries')
