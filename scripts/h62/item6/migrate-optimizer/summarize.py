#!/usr/bin/env python3
"""Derive reviewable hashes and blocked-gate summary from private bulk evidence."""
from pathlib import Path
import hashlib,json,re,subprocess
from bulk import load_bulk_json, derived_directory
root=Path(__file__).resolve().parents[4];d=root/'tests/h62/item6/migrate-optimizer';E=Path('/workspace/migrate-optimizer-evidence')
census=load_bulk_json('census.json')
output_directory=derived_directory()
def records(run):
 text=(E/run/'build.log').read_text();out={}
 for m in re.finditer(r"^INTERFACE (Solidity\.Optimizer\.\S+) universes=.*?(?=^INTERFACE |^'Solidity|^FIXTURE=|\Z)",text,re.M|re.S):
  out[m.group(1)]=re.sub(r'\s+',' ',m.group(0)).strip()
 assert out,run
 (output_directory/(run+'-interface-records.json')).write_text(json.dumps(out,indent=2)+'\n')
 return out
runs=['old-audit','isolated-old','generic-old','generic-new']
allrecords={r:records(r) for r in runs}
explicit=[]
for module in census['targets']:
 path=root/census['files'][module]['path'];stack=[]
 for line in path.read_text().splitlines():
  m=re.match(r'namespace (\S+)',line)
  if m:stack.append(m.group(1));continue
  if re.match(r'end(?: |$)',line):
   if stack:stack.pop()
   continue
  m=re.match(r'(?:abbrev|def|structure|theorem) (\S+)',line)
  if m:explicit.append('.'.join(stack+[m.group(1)]))
assert len(explicit)==35
full=allrecords['old-audit'];a=allrecords['generic-old'];b=allrecords['generic-new']
assert set(explicit)<=full.keys()
subset=[n for n in explicit if n in a and n in b]
assert len(subset)==27
assert all(a[n]==b[n] for n in subset),'explicit fixture interface changed'
hashes={r:{k:hashlib.sha256(v.encode()).hexdigest() for k,v in sorted(x.items())} for r,x in allrecords.items()}
(output_directory/'interface-hashes.json').write_text(json.dumps({'encoding':'SHA256 of whitespace-normalized Lean Expr repr, with name and ordered universe parameters; binder hygiene names retained','full_original_old_explicit_declarations':explicit,'generic_explicit_unchanged_across_versions':subset,'generic_pending_explicit_declarations':sorted(set(explicit)-set(subset)),'hashes':hashes,'generated_api_changes':sorted(k for k in a.keys()&b.keys() if a[k]!=b[k]),'generated_api_added':sorted(b.keys()-a.keys()),'limitations':'Full original new-toolchain interface unavailable. Fixture relocation changes hygienic binder labels versus original modules; no alpha-equivalence claim from unequal repr hashes.'},indent=2)+'\n')
labels=['clean-4.24.0','reviewed-old','reviewed-new','old-audit','isolated-old','isolated-new','generic-old','generic-new']
results={r:json.loads((E/r/'result.json').read_text()) for r in labels}
old=results['generic-old'];new=results['generic-new']
delta={k:100*(new[k]/old[k]-1) for k in ['wall_seconds','peak_sampled_aggregate_rss_bytes']}
delta['maximum_child_rss_kib']=100*(new['kernel_usage']['maximum_child_rss_kib']/old['kernel_usage']['maximum_child_rss_kib']-1)
delta['kernel_wall_seconds']=100*(new['kernel_usage']['wall_seconds']/old['kernel_usage']['wall_seconds']-1)
summary={'base':'c6f550e281a7e5affa9a99bc2cdaed556dec00e4','results':results,'full_migration_timing_delta':None,'full_migration_timing_reason':'New closure failed before any assigned module; incomplete work cannot be compared','generic_fixture_percent_delta':delta,'performance_status':'STOP_GT_10_PERCENT','full_gate_status':'BLOCKED_OWNER_DEPENDENCIES_AND_PERFORMANCE','source_changed':False,'new_axioms':0,'new_sorry':0,'resource_profile':{'cpu':1,'memory_bytes':12*1024**3,'swap_disabled':True,'reserve_bytes':4*1024**3,'Lean_threads':1,'artifact_cache':False},'proof_boundary':'Generic fixture proves unchanged 27 declarations and scalar controls only. Full old originals pass; full new originals and intrinsic/Roadmap adapters remain unverified on new toolchain. External tests are not semantic completeness proofs.'}
(output_directory/'measurements.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'interfaces_full_old':len(full),'explicit_total':len(explicit),'generic_explicit_identical':len(subset),'generic_percent_delta':delta,'status':summary['performance_status']},indent=2))
