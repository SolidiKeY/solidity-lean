#!/usr/bin/env python3
"""Bind historical candidates by Lean definition positions; inspect native uses.
Historical lexical edges never enter this graph. Negative results remain bounded
by cached modules and cannot certify deletion, macro effects or exact roots.
"""
import argparse,collections,hashlib,json,pathlib,runpy
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));

def measure(source_root,graph,view,historical):
 src=API['assert_sources'](source_root);raw_span=runpy.run_path(str(HERE/'historical.py'))['raw_span']
 native=runpy.run_path(str(HERE/'module_graph.py'));g=native['load'](graph)
 paths=runpy.run_path(str(HERE/'native_summary.py'))['module_paths'](src,view)
 assert set(paths)=={m for m,r in g.modules.items() if r['selected']}
 historical_summary=json.loads((historical/'historical-summary.json').read_text());assert historical_summary['base']==API['BASE']
 pinned_historical=json.loads(API['git']('show',API['BASE']+':docs/audits/direction-tools/reachability/summary.json'))
 assert historical_summary['historical_base']==pinned_historical['base']
 candidates=[]
 for family in API['FAMILIES']:
  p=historical/(family.strip('/').replace('/','_')+'-historical.json');candidates.extend(json.loads(p.read_text()))
 bypath=collections.defaultdict(list)
 for i,r in enumerate(candidates):
  assert r['last_line']-r['first_line']+1==r['physical_span_lines'] and r['first_line']>=1
  assert str(pathlib.PurePosixPath(r['path']).parent)+'/' in API['FAMILIES']
  same=hashlib.sha256(src[r['path']].encode()).hexdigest()==r['old_source_sha256']
  assert r['unchanged_at_base']==same,'Stale source-drift flag'
  if same:
   assert raw_span(src[r['path']],r['source_start_char'],r['source_end_char'])==(r['first_line'],r['last_line'],r['physical_span_lines']),'Stale physical coordinates'
  r.update(native_symbols=[],external_source_edges=0,unattributed_incoming_edges=0,internal_edges=0)
  if same:bypath[r['path']].append(i)
 positions={};owner={}
 for key,node in g.nodes.items():
  selection=node['selection']
  if selection is None:continue
  path=paths[key[0]];line=selection[0]+1;positions[key]=(path,line,selection[1])
  matches=[i for i in bypath[path] if candidates[i]['first_line']<=line<=candidates[i]['last_line']]
  assert len(matches)<=1,(key,matches)
  if matches:owner[key]=matches[0];candidates[matches[0]]['native_symbols'].append(key[1])
 for a,refs in g.edges.items():
  pos=positions.get(a)
  for b in refs:
   if b not in owner or a==b:continue
   i=owner[b];r=candidates[i]
   if pos and pos[0]==r['path'] and r['first_line']<=pos[1]<=r['last_line']:
    r['internal_edges']+=1
   elif pos:
    r['external_source_edges']+=1
    witness=dict(from_symbol=a[1],source_module=a[0],to_symbol=b[1],target_module=b[0],source_path=pos[0],source_owner_definition_line=pos[1])
    if 'witness' not in r or (a[0],a[1],b[0],b[1])<(r['witness']['source_module'],r['witness']['from_symbol'],r['witness']['target_module'],r['witness']['to_symbol']):r['witness']=witness
   else:r['unattributed_incoming_edges']+=1
 totals=collections.defaultdict(collections.Counter);provenance=collections.defaultdict(collections.Counter)
 for r in candidates:
  r['native_symbols'].sort()
  if not r['unchanged_at_base']:status='source_file_changed'
  elif not r['native_symbols']:status='no_native_range_binding'
  elif r['external_source_edges']:status='native_compile_use_witness'
  elif r['unattributed_incoming_edges']:status='native_auxiliary_incoming'
  else:status='no_external_incoming_in_native_compile_graph'
  r['status']=status;family=str(pathlib.PurePosixPath(r['path']).parent)+'/'
  for c in (totals[family],provenance[API['provenance'](r['path'],src[r['path']])]):
   c[status+'_declarations']+=1;c[status+'_historical_reported_lines']+=r['historical_masked_span_lines'];c[status+'_physical_span_lines']+=r['physical_span_lines']
  del r['old_source_sha256']
 for family,c in totals.items():
  assert sum(v for k,v in c.items() if k.endswith('_declarations'))==historical_summary['families'][family]['declarations']
  assert sum(v for k,v in c.items() if k.endswith('_historical_reported_lines'))==historical_summary['families'][family]['historical_reported_lines']
 result=dict(base=API['BASE'],historical_base=historical_summary['historical_base'],status='partial',native_graph_sha256=native['sha'](graph),indexed_modules=len(paths),serialized_constant_records=len(g.nodes),unresolved_native_references=dict(g.unresolved),
  families={k:dict(sorted(v.items())) for k,v in sorted(totals.items())},provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},deletable_now_verified_lines=0,
  verdict='Native compile-use witnesses refute zero incoming uses for witnessed candidates. ALL candidates remain unresolved for full semantic-root liveness and deletion.',
  settling_measurement='Complete affected-root elaboration on the pinned source, recording macro/extension effects and missing-module references, followed by isolated removal builds for candidates without uses.',
  boundaries=['Bindings use per-module native declaration selection ranges in unchanged historical files; no editor-reference positions or edges are used.',
   'Native module/name identities preserve repeated theorem names. Each expression edge resolves in its defining module compilation context, not a downstream root context.',
   'Witness source_owner_definition_line is a declaration name location, not the use site. Incoming uses do not establish root reachability or deletion failure.',
   'Range-less native auxiliary owners remain conservative incoming uses.',
   'Historical reported lines are masked-text units; physical_span_lines and binding positions come from raw LF-based source offsets. Neither is a deletion budget.',
   'Compiler attributes, anonymous check proofs, missing consumers and dynamic effects remain unmeasured by this native-expression graph.'])
 return sorted(candidates,key=lambda r:(r['path'],r['first_line'])),result

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--historical',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 rows,result=measure(a.source_root,a.graph,a.view,a.historical);a.out.mkdir(parents=True,exist_ok=True)
 outputs={'candidate-summary.json':json.dumps(result,sort_keys=True,indent=2)+'\n'}
 for family in API['FAMILIES']:
  subset=[r for r in rows if str(pathlib.PurePosixPath(r['path']).parent)+'/'==family]
  outputs[family.strip('/').replace('/','_')+'-candidates.json']=json.dumps(subset,sort_keys=True,separators=(',',':'))+'\n'
 for name,body in outputs.items():
  assert len(body.encode())<1000000,name
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 print('CANDIDATE_NATIVE_USE_PASS',len(rows),sum(r['external_source_edges']>0 for r in rows))
if __name__=='__main__':main()
