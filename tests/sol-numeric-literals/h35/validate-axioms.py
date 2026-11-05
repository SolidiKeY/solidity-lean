#!/usr/bin/env python3
"""Check complete H35 print output against exact expected source and kernel pins."""
import hashlib,json,pathlib,runpy
root=pathlib.Path(__file__).resolve().parents[3]
f=root/'tests/sol-numeric-literals';here=f/'h35'
expected=json.loads((here/'expected.json').read_text())
manifest=json.loads((f/'acceptance.json').read_text())
authored=sorted(d['name'] for m in manifest['modules'] for d in m['authored'] if d['kind']=='theorem')
assert expected['authored_theorems']==authored
source=(here/'PrintAxioms.lean').read_bytes()
exact_source='import Solidity.Frontend.NumericLiteralProofs.Audit\n\n/-! H35: print every authored theorem axiom set. No proof declarations added. -/\n\n'+''.join('#print axioms '+n+'\n' for n in authored)
assert source.decode()==exact_source
assert hashlib.sha256(source).hexdigest()==expected['print_file_sha256']
assert hashlib.sha256((f/'kernel-inventory.json').read_bytes()).hexdigest()==expected['kernel_inventory_sha256']
lines={i:s[len('#print axioms '):] for i,s in enumerate(source.decode().splitlines(),1) if s.startswith('#print axioms ')}
assert sorted(lines.values())==expected['authored_theorems'] and len(lines)==627
raw=json.loads((f/'evidence/h35-print-axioms.log').read_text())
assert raw['success'] and not raw['partial'] and not raw['timed_out'] and not raw.get('failed_dependencies')
assert len(raw['items'])==627
actual={}
for item in raw['items']:
 assert item['severity']=='info'
 name=lines[item['line']];prefix="'"+name+"' "
 assert item['message'].startswith(prefix) and name not in actual
 text=item['message'][len(prefix):]
 if text=='does not depend on any axioms':axioms=[]
 else:
  assert text.startswith('depends on axioms: [') and text.endswith(']')
  axioms=sorted(x.strip() for x in text[len('depends on axioms: ['):-1].split(',') if x.strip())
 assert set(axioms)<={'propext','Quot.sound','Classical.choice'}
 actual[name]=axioms
pinned=json.loads((f/'kernel-inventory.json').read_text());byname={r['name']:r for r in pinned}
assert set(actual)==set(expected['authored_theorems'])
for name,axioms in actual.items():assert axioms==sorted(byname[name]['axioms']),name
assert hashlib.sha256((here/'PrintAllAxioms.lean').read_bytes()).hexdigest()==expected['print_all_file_sha256']
for label in ('h35-print-all-axioms','adopted-print-axioms'):
 all_raw=json.loads((f/'evidence'/(label+'.log')).read_text())
 assert all_raw['success'] and not all_raw['partial'] and not all_raw['timed_out'] and not all_raw.get('failed_dependencies')
 all_actual={}
 for item in all_raw['items']:
  assert item['severity']=='info'
  text=item['message'];assert text.startswith("'")
  name,text=text[1:].rsplit("' ",1)
  assert name not in all_actual
  if text=='does not depend on any axioms':axioms=[]
  else:
   assert text.startswith('depends on axioms: [') and text.endswith(']')
   axioms=sorted(x.strip() for x in text[len('depends on axioms: ['):-1].split(',') if x.strip())
  all_actual[name]=axioms
 assert len(all_actual)==808 and set(all_actual)=={r['name'] for r in pinned if r['kind']=='theorem'}
 for name,axioms in all_actual.items():assert axioms==sorted(byname[name]['axioms']),name

ns=runpy.run_path(str(root/'scripts/check-sol-numeric-literals.py'))
modules=ns['source_snapshot']()
ns['validate_inventory'](json.loads((f/'evidence/kernel-inventory.actual.json').read_text()),pinned,modules)
build=json.loads((f/'evidence/h35-owned-build.json').read_text())
assert build['exit']==0 and not build['resource_stop']
assert build['proof_sources']=={m['path']:m['sha256'] for m in modules}
assert build['minimum_parent_headroom_bytes']>=4*1024**3
for label in ('adopted-owned-build','adopted-audit','adopted-print-axioms'):
 gate=json.loads((f/'evidence'/(label+'.json')).read_text())
 assert gate['exit']==0 and not gate['resource_stop']
 assert gate['proof_sources']==build['proof_sources']
 assert gate['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1)
 assert gate['minimum_parent_headroom_bytes']>=4*1024**3
result=dict(authored_prints=627,all_theorem_prints=808,all_printed_theorem_axioms=all_actual,kernel_theorem_constants=sum(r['kind']=='theorem' for r in pinned),all_owned_constants=len(pinned),new_axioms=[],axioms_by_authored_theorem=actual,proof_sources=build['proof_sources'],print_diagnostics_complete=True,generated_helpers_checked_by_full_inventory=True)
(f/'evidence/h35-axiom-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print('H35 axioms: 627 authored prints and all808 theorem-constant prints match pins; full991 inventory checked; no new axioms or unsafe declarations')
