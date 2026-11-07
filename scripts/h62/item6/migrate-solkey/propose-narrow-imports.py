#!/usr/bin/env python3
"""Emit a new-toolchain-only import proposal; never apply or run Lean."""
import argparse,difflib,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--graph',type=Path,required=True);p.add_argument('--old-report',type=Path,required=True);p.add_argument('--new-report',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
root=Path(__file__).resolve().parents[4];relative='tests/h62/item6/migrate-solkey/StringApiControls.lean';fixture=root/relative
original=fixture.read_bytes();source_hash=hashlib.sha256(original).hexdigest()
pins={}
for line in (root/'tests/h62/item6/migrate-solkey/evidence-SHA256SUMS').read_text().splitlines():
 if line and not line.startswith('#'):
  value,name=line.split(None,1);pins[name.strip()]=value
for report,label,version in [(a.old_report,'old-api-final/gate.json','4.24.0'),(a.new_report,'new-api-final/gate.json','4.35.0')]:
 if hashlib.sha256(report.read_bytes()).hexdigest()!=pins.get(label):raise SystemExit('Capture differs from committed evidence pin: '+label)
 data=json.loads(report.read_text())
 if not data['versions']['lean'].startswith('Lean (version '+version+',') or ('Lean version '+version) not in data['versions']['lake']:
  raise SystemExit('Wrong capture toolchain: '+label)
 if data.get('exit')!=0 or data.get('axiom_exit')!=0 or data.get('stop') is not None or data.get('source_sha256')!=source_hash:
  raise SystemExit('Fixture/capture provenance mismatch')
text=original.decode();old='import Init.Data.String.Lemmas\n';new='import Init.Data.String.Lemmas.TakeDrop\nimport Init.Data.String.Lemmas.Pattern.TakeDrop.String\n'
if text.count(old)!=1:raise SystemExit('Expected one original umbrella import')
candidate=text.replace(old,new,1)
if candidate.replace(new,old,1)!=text:raise SystemExit('Non-import change detected')
catalog=json.loads((root/'tests/h62/item6/migrate-solkey/portable-evidence/catalog.json').read_text())
pins=[member['sha256'] for archive in catalog['bulk_archives'] for member in archive['required_members'] if member['path']=='new-sdk-imports.json']
graph_hash=hashlib.sha256(a.graph.read_bytes()).hexdigest()
if len(pins)!=1 or graph_hash!=pins[0]:raise SystemExit('SDK graph differs from committed portable evidence pin')
graph=json.loads(a.graph.read_text())['records']
def closure(seeds):
 seen=set();todo=list(seeds)
 while todo:
  name=todo.pop()
  if name in seen:continue
  if name not in graph or graph[name].get('missing_source'):raise SystemExit('Missing SDK graph source: '+name)
  seen.add(name);todo.extend(graph[name]['imports'])
 return seen
before=closure(['Init.Data.String.Basic','Init.Data.String.Lemmas'])
after=closure(['Init.Data.String.Basic','Init.Data.String.Lemmas.TakeDrop','Init.Data.String.Lemmas.Pattern.TakeDrop.String'])
required={'String.toList_injective':'Init.Data.String.Basic','String.toList_copy_drop':'Init.Data.String.Lemmas.TakeDrop','String.endsWith_eq_endsWith_toSlice':'Init.Data.String.Lemmas.Pattern.TakeDrop.Basic','String.Slice.endsWith_string_iff':'Init.Data.String.Lemmas.Pattern.TakeDrop.String','String.Slice.endsWith_string_eq_false_iff':'Init.Data.String.Lemmas.Pattern.TakeDrop.String','String.copy_toSlice':'Init.Data.String.Basic','String.Slice.toStringToString_eq':'Init.Data.String.Slice'}
if not set(required.values())<=after:raise SystemExit('A defining source module is not reachable')
if a.out.exists():raise SystemExit('Refusing existing proposal directory')
a.out.mkdir(parents=True)
(a.out/'narrow-imports.patch').write_text(''.join(difflib.unified_diff(text.splitlines(True),candidate.splitlines(True),fromfile='a/'+relative,tofile='b/'+relative)))
(a.out/'StringApiControls.candidate.lean').write_text(candidate)
plan={'schema_version':1,'fixture':relative,'target_toolchain':'leanprover/lean4:v4.35.0 only','source_sha256':source_hash,'candidate_sha256':hashlib.sha256(candidate.encode()).hexdigest(),'sdk_graph_sha256':hashlib.sha256(a.graph.read_bytes()).hexdigest(),'original_new_version_header_modules':len(before),'candidate_explicit_header_modules':len(after),'removed_source_modules':sorted(before-after),'required_defining_source_modules':required,'statement_and_proof_text_preserved':True,'applied':False,'lean_run':False,'measured_rss_delta':None,'public_signatures_checked':False,'axiom_sets_checked':False,'performance_accepted':False,'STOP_lifted':False,'boundary':'Static source reachability is not import visibility, elaboration, axiom equivalence or measured memory. Candidate is new-version-only; old4.24 fixture and eight public statements/proof text stay unchanged. Gate.sh per-file and meaning/axiom checks require current policy/disposition before any future run.'}
(a.out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n');print(json.dumps({k:v for k,v in plan.items() if k not in ['removed_source_modules','required_defining_source_modules']},indent=2))
