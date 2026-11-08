#!/usr/bin/env python3
"""Check pinned-source identity and reconcile all committed measurement totals.
Run: python3 -I docs/audits/direction-tools/declgraph/verify.py [--results DIR]
This validates accounting and boundaries, not deletion safety or missing roots.
"""
import argparse,csv,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser();p.add_argument('--results',type=pathlib.Path,default=HERE);a=p.parse_args();d=a.results
 api=runpy.run_path(str(HERE/'audit.py'));api['assert_sources']()
 inv=json.loads((HERE/'inventory.json').read_text());s=json.loads((d/'summary.json').read_text())
 assert inv==api['inventory'](),'Frozen inventory differs'
 assert s['base']==api['BASE'] and s['status']=='partial'
 assert s['module_universe']+s['missing_files']==inv['tracked_lean_files']
 assert s['indexed_physical_lines']+s['missing_physical_lines']==inv['physical_lines']
 assert s['deletable_now_verified_lines']==0
 keys=('facade_used','policy_check_only','unreached')
 for name in ('areas','directories'):
  rows=list(csv.DictReader((d/(name+'.csv')).open()))
  total=sum(int(r[k+'_source_span_lines']) for r in rows for k in keys)+sum(int(r['unattributed_physical_lines']) for r in rows)
  assert total==s['indexed_physical_lines'],(name,total,s['indexed_physical_lines'])
  assert sum(int(r[k+'_declarations']) for r in rows for k in keys)==s['native_declarations']
 for pre,r in s['families'].items():
  assert r['indexed_files']==inv['families'][pre]['files']
  assert r['declarations']==sum(r[k+'_declarations'] for k in keys)
  assert 0<=r['zero_incoming_declarations']<=r['unreached_declarations']
  assert r['unreached_source_spanned_native_constants']<=r['source_spanned_native_constants']<=r['declarations']
  assert r['used_only_by_own_policy_check_roots_declarations']<=r['policy_check_only_declarations']
  assert r['used_only_by_own_policy_check_roots_source_span_lines']<=r['source_span_lines']['policy_check_only']
  f=d/(pre.strip('/').replace('/','_')+'-unreached.tsv')
  rows=list(csv.DictReader(f.open(),delimiter='\t'))
  assert len(rows)==r['unreached_declarations']
  assert sum(int(x['zero_incoming']) for x in rows)==r['zero_incoming_declarations']
  assert all(x['serialized_module_owner_path'].startswith(pre) for x in rows)
 for f in d.iterdir():
  if f.suffix in ('.json','.csv','.tsv'):assert f.stat().st_size<1_000_000,f
 print('DECLGRAPH_ACCOUNTING_PASS',s['module_universe'],'indexed modules;',s['indexed_physical_lines'],'physical lines; deletion certification remains pending')
if __name__=='__main__':main()
