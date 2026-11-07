#!/usr/bin/env python3
"""Recheck exact original48 under the baseline cache/flags/resource policy.
Baseline is the immutable C1/C2 checkpoint. No failed/differently bounded run
is comparable. A >10% aggregate wall slowdown fails and stops this command.
"""
import argparse,json,subprocess,sys
from pathlib import Path
import bounded_lean

def main():
 repo=Path.cwd(); root=Path('/workspace/h62-audit-g25-artifacts');cache=root/'audit-v424'
 baseline=root/'checkpoints/b25616bd6c24a8ef5d905cd33c5cd552c33c2c12'
 census=json.loads((root/'evidence/source-census.json').read_text())
 modules=[x['path'][:-5].replace('/','.') for x in census['modules']]
 manifest=baseline/'SHA256SUMS'
 manifest_sha=bounded_lean.digest_file(manifest)
 if manifest_sha!='830102ff123fbd03a961ad40115edb117e93af915bc3f4b1d96bfafa872cb2c7': raise ValueError('baseline manifest differs from saved C1/C2 export')
 for line in manifest.read_text().splitlines():
  sha,name=line.split('  ',1); path=baseline/name
  if not path.resolve().is_relative_to(baseline.resolve()) or bounded_lean.digest_file(path)!=sha: raise ValueError('baseline checksum mismatch: '+name)
 baseline_index=json.loads((baseline/'cache-index.json').read_text());old={}
 for path in (baseline/'receipts').glob('*.json'):
  row=json.loads(path.read_text());module=row['module']
  if module in old: raise ValueError('duplicate baseline module receipt: '+module)
  entry=baseline_index[module]
  if path.name!=Path(entry['receipt']).name or bounded_lean.digest_file(path)!=entry['receipt_sha256']: raise ValueError('baseline index receipt mismatch: '+module)
  old[module]=row
 if set(old)!=set(baseline_index): raise ValueError('baseline receipt index census differs')
 expected={m for m in old if m.startswith(('Solidity.Backend.Scalar.','Solidity.Backend.Environment.'))}
 if len(modules)!=48 or len(set(modules))!=48 or set(modules)!=expected: raise ValueError('original48 module census differs from frozen baseline')
 p=argparse.ArgumentParser();p.add_argument('--compare-existing',action='store_true');a=p.parse_args()
 command=[sys.executable,str(Path(__file__).with_name('bounded_lean.py')),'--reuse','--recheck-targets',
  '--toolchain','/workspace/.setup/tools/lean-4.24.0-linux','--artifacts',str(cache),*modules]
 log=root/'evidence/original48-recheck.log'
 if not a.compare_existing:
  with log.open('w') as output: result=subprocess.run(command,cwd=repo,stdout=output,stderr=subprocess.STDOUT)
  if result.returncode: raise SystemExit(result.returncode)
 measured={}
 for line in log.read_text().splitlines():
  row=json.loads(line)
  if row['module'] in modules and not row.get('cache_hit'):
   if row['module'] in measured: raise ValueError('duplicate measured module')
   measured[row['module']]=row
 if set(measured)!=set(modules): raise ValueError('measurement log does not contain all48 fresh modules')
 index=json.loads((cache/'cache-index.json').read_text());rows=[]
 for module in modules:
  before=old[module]; entry=index[module];path=Path(entry['receipt'])
  if bounded_lean.digest_file(path)!=entry['receipt_sha256']: raise ValueError('measured receipt hash differs')
  after=json.loads(path.read_text())
  if after!=measured[module]: raise ValueError('measured log/receipt differs: '+module)
  for key in ['module','command','source_sha256','fingerprint','exit','resource_stop','output_sha256']:
   if before[key]!=after[key]: raise ValueError('noncomparable original receipt: '+module+' '+key)
  if before['exit']!=0 or before['resource_stop'] or after['cache_hit']: raise ValueError('nonpassing/nonfresh sample')
  rows.append({'module':module,'fingerprint':after['fingerprint'],
   'before_wall_seconds':before['seconds'],'after_wall_seconds':after['seconds'],
   'before_cpu_seconds':before['cpu_seconds'],'after_cpu_seconds':after['cpu_seconds'],
   'before_sampled_peak_rss_kib':before['sampled_peak_rss_kib'],
   'after_sampled_peak_rss_kib':after['sampled_peak_rss_kib']})
 before=sum(x['before_wall_seconds'] for x in rows);after=sum(x['after_wall_seconds'] for x in rows)
 delta=(after/before-1)*100
 report={'status':'pass' if delta<=10 else 'fail','boundary':'original48 recheck; additive audit cost is separate; no original source refactor',
  'command':command,'exit':0,'log':str(log),'log_sha256':bounded_lean.digest_file(log),
  'baseline':str(baseline),'baseline_manifest_sha256':manifest_sha,'modules':len(rows),'same_source_flags_imports_toolchain_cache_and_resource_policy':True,
  'before_wall_seconds':round(before,3),'after_wall_seconds':round(after,3),'wall_delta_percent':round(delta,3),
  'before_cpu_seconds':round(sum(x['before_cpu_seconds'] for x in rows),6),
  'after_cpu_seconds':round(sum(x['after_cpu_seconds'] for x in rows),6),'stop_threshold_percent':10,'rows':rows}
 (root/'evidence/original48-timings.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k not in ['rows','command']},sort_keys=True))
 if delta>10: raise SystemExit('STOP: original48 aggregate slowdown exceeds10%')

if __name__=='__main__': main()
