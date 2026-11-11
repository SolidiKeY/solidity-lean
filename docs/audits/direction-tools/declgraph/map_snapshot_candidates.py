#!/usr/bin/env python3
"""Bind saved-check observations to historical units using native identities.
Imported pointer witnesses and stage2 range correspondences stay distinct.
No lexical edges, negative liveness verdicts or deletion budgets are inferred.
"""
import argparse,collections,csv,hashlib,io,json,os,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha']
def keyhash(key):return hashlib.sha256(json.dumps(key,separators=(',',':'),ensure_ascii=True).encode()).hexdigest()
def read_tsv(name):return list(csv.DictReader((HERE/name).open(),delimiter='\t'))

def verdict(imported,stage2):
 if imported:head='Imported saved-check dependencies witness matched historical units; stage2 correspondences remain separate.'
 elif stage2:head='Only stage2 range correspondences were found; no imported snapshot dependency witness is established.'
 else:head='No historical candidate receives an imported snapshot dependency witness or exact stage2 range correspondence in this measured corpus.'
 return head+' This does not certify unusedness or deletability; full-root liveness remains unresolved.'

def bind(candidates,nodes,imports,stage2,keys,module_paths):
 bysymbol={};rows=[]
 for i,c in enumerate(candidates):
  module=next(m for m,p in module_paths.items() if p==c['path'])
  for name in c['native_symbols']:
   assert (module,name) not in bysymbol
   node=nodes[(module,name)];assert node['selection'] is not None and c['first_line']<=node['selection'][0]+1<=c['last_line']
   bysymbol[module,name]=i
  rows.append(dict(path=c['path'],name=c['name'],first_line=c['first_line'],last_line=c['last_line'],historical_masked_span_lines=c['historical_masked_span_lines'],physical_span_lines=c['physical_span_lines'],compile_graph_status=c['status'],status='no_observed_snapshot_witness',imported_symbols=[],stage2_correspondences=[]))
 imported_bound=0;stage2_bound=0
 for r in imports:
  k=(r['module'],r['name']);assert k in keys and k in nodes
  assert keyhash(keys[k]['name_key'])==r['name_key_sha256'] and keys[k]['constant_kind']==r['constant_kind']==nodes[k]['kind']
  if k in bysymbol:rows[bysymbol[k]]['imported_symbols'].append(r['name']);imported_bound+=1
 for r in stage2:
  if r['seen_as_dependency']!='1':continue
  module=next(m for m,p in module_paths.items() if p==r['path']);k=(module,r['name'])
  if k not in keys or k not in nodes:continue
  if keyhash(keys[k]['name_key'])!=r['name_key_sha256'] or keys[k]['constant_kind']!=r['constant_kind']:continue
  rng=json.loads(r['own_range'])
  if rng is not None and rng==nodes[k]['range'] and k in bysymbol:
   rows[bysymbol[k]]['stage2_correspondences'].append(r['name']);stage2_bound+=1
 totals=collections.defaultdict(collections.Counter)
 for c,r in zip(candidates,rows):
  if not c['unchanged_at_base']:r['status']='historical_source_drift'
  elif r['imported_symbols']:r['status']='imported_snapshot_dependency_witness'
  elif r['stage2_correspondences']:r['status']='stage2_range_correspondence_only'
  family=str(pathlib.PurePosixPath(c['path']).parent)+'/'
  t=totals[family];t[r['status']+'_units']+=1;t[r['status']+'_historical_masked_span_lines']+=c['historical_masked_span_lines'];t[r['status']+'_physical_span_lines']+=c['physical_span_lines']
  r['imported_symbols']=sorted(set(r['imported_symbols']));r['stage2_correspondences']=sorted(set(r['stage2_correspondences']))
 return rows,totals,imported_bound,stage2_bound

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--capture',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 for k in ('source_root','view','graph','capture','out'):setattr(a,k,getattr(a,k).resolve())
 src=API['assert_sources'](a.source_root);candidate_files=[family.strip('/').replace('/','_')+'-candidates.json' for family in API['FAMILIES']];historical_files=[family.strip('/').replace('/','_')+'-historical.json' for family in API['FAMILIES']];names=('historical.py',*historical_files,'CachedKeys.lean','map_snapshot_candidates.py','audit.py','module_graph.py','modules.txt','snapshot-root-summary.json','snapshot-imported-bindings.tsv','snapshot-stage2-bindings.tsv','candidate-summary.json','historical-summary.json',*candidate_files);producers={n:SHA(HERE/n) for n in names}
 receipt_path=pathlib.Path(str(a.graph)+'.receipt.json');gr=json.loads(receipt_path.read_text());assert gr['index_sha256']==SHA(a.graph) and pathlib.Path(gr['reference_view']).resolve()==a.view
 assert gr['modules_sha256']==SHA(HERE/'modules.txt');assert json.loads((HERE/'candidate-summary.json').read_text())['native_graph_sha256']==gr['index_sha256']
 assert json.loads((HERE/'native-summary.json').read_text())['selected_module_system_modules']==0
 candidates=[r for n in candidate_files for r in json.loads((HERE/n).read_text())];old={(r['path'],r['source_start_char'],r['source_end_char']):r for n in historical_files for r in json.loads((HERE/n).read_text())};raw_span=runpy.run_path(str(HERE/'historical.py'))['raw_span']
 for c in candidates:
  h=old[c['path'],c['source_start_char'],c['source_end_char']];same=hashlib.sha256(src[c['path']].encode()).hexdigest()==h['old_source_sha256'];assert same==c['unchanged_at_base']
  if same:assert raw_span(src[c['path']],c['source_start_char'],c['source_end_char'])==(c['first_line'],c['last_line'],c['physical_span_lines'])
 imports=read_tsv('snapshot-imported-bindings.tsv');stage2=read_tsv('snapshot-stage2-bindings.tsv');wanted=collections.defaultdict(set);module_paths={};query=[];artifacts={}
 def register(module,path):
  assert path in src
  f=a.view/pathlib.Path(path).with_suffix('.ilean');assert json.loads(f.read_text())['module']==module
  if module in module_paths:assert module_paths[module]==path
  module_paths[module]=path
 for r in imports:register(r['module'],r['module'].replace('.','/')+'.lean');wanted[r['module']].add(r['name'])
 for c in candidates:
  path=c['path'];f=a.view/pathlib.Path(path).with_suffix('.ilean');module=json.loads(f.read_text())['module'];register(module,path);wanted[module].update(c['native_symbols'])
 for r in stage2:
  if r['seen_as_dependency']!='1':continue
  module=json.loads((a.view/pathlib.Path(r['path']).with_suffix('.ilean')).read_text())['module'];register(module,r['path']);wanted[module].add(r['name'])
 for module,requested in sorted(wanted.items()):
  if not requested:continue
  artifact=a.view/pathlib.Path(module_paths[module]).with_suffix('.olean');assert artifact.is_file();artifacts[str(artifact)]=SHA(artifact);query.append(dict(module=module,artifacts=[str(artifact)],names=sorted(requested)))
 query_body=json.dumps(query,sort_keys=True,separators=(',',':'))+'\n';version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 cmd=['lean','--tstack=131072','-j1','-M4000','--run',str(HERE/'CachedKeys.lean'),str(a.capture/'query.json'),str(a.capture/'keys.jsonl')];fixed=dict(producers=producers,artifacts=artifacts,lean=version,command=cmd,view=str(a.view),graph_receipt_sha256=SHA(receipt_path),graph_sha256=gr['index_sha256']);receipt=a.capture/'receipt.json'
 if a.check:
  meta=json.loads(receipt.read_text());assert all(meta[k]==v for k,v in fixed.items()) and meta['exit_code']==0
  for n in ('query.json','keys.jsonl','capture.log'):assert meta['outputs'][n]==SHA(a.capture/n)
  assert (a.capture/'query.json').read_text()==query_body
 else:
  assert not a.capture.exists();a.capture.mkdir(parents=True);(a.capture/'query.json').write_text(query_body)
  with (a.capture/'capture.log').open('w') as log:x=subprocess.run(cmd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT,timeout=300)
  assert x.returncode==0,'Native cache-key lookup failed'
  meta=dict(fixed,exit_code=0,outputs={n:SHA(a.capture/n) for n in ('query.json','keys.jsonl','capture.log')});receipt.write_text(json.dumps(meta,sort_keys=True,indent=2)+'\n')
 records=[json.loads(line) for line in (a.capture/'keys.jsonl').read_text().splitlines()];keys={};mods={}
 for r in records:
  if r['record']=='key':
   k=(r['module'],r['name']);assert k not in keys,'Ambiguous printed name in native cache';keys[k]=r
  else:assert r['record']=='module' and r['module'] not in mods;mods[r['module']]=r
 assert set(mods)=={q['module'] for q in query}
 for q in query:
  mod=q['module'];found={name for m,name in keys if m==mod};assert found<=set(q['names'])
  assert mods[mod]['missing_names']==[n for n in q['names'] if n not in found] and mods[mod]['requested_names']==len(q['names'])
 marker=re.findall(r'CACHED_KEYS_PASS (\d+) (\d+) (\d+) (\d+)',(a.capture/'capture.log').read_text());assert len(marker)==1 and tuple(map(int,marker[0]))==(len(query),len(keys),sum(len(m['missing_names']) for m in mods.values()),len(query))
 targets=set(keys);nodes={}
 for line in a.graph.open():
  r=json.loads(line)
  if r['record']=='constant' and (r['module'],r['name']) in targets:nodes[r['module'],r['name']]=r
 assert set(nodes)==targets,'Native key lookup and original graph disagree'
 assert all(keys[k]['constant_kind']==nodes[k]['kind'] for k in keys)
 rows,totals,imported_bound,stage2_bound=bind(candidates,nodes,imports,stage2,keys,module_paths)
 provenance=collections.defaultdict(collections.Counter)
 for c,r in zip(candidates,rows):
  label=API['provenance'](c['path'],src[c['path']]) if c['unchanged_at_base'] else 'historical_source_drift'
  provenance[label][r['status']+'_units']+=1;provenance[label][r['status']+'_physical_span_lines']+=c['physical_span_lines']
 summary=dict(base=API['BASE'],status='partial',candidate_units=len(rows),imported_binding_units=len(imports),imported_symbols_bound_to_candidates=imported_bound,stage2_dependency_name_range_units=sum(r['seen_as_dependency']=='1' for r in stage2),stage2_correspondences_bound_to_candidates=stage2_bound,queried_legacy_modules=len(query),native_cached_key_records=len(keys),missing_requested_name_strings=sum(len(m['missing_names']) for m in mods.values()),families={k:dict(sorted(v.items())) for k,v in sorted(totals.items())},provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},deletable_now_verified_lines=0,verdict=verdict(imported_bound,stage2_bound),settling_measurement='An isolated removal replay of the complete affected-root suite on an authorized valid baseline, recording native symbolic, macro and attribute dependencies.',boundaries=['Imported CIs are bound by positive object-pointer origins in actual saved check environments, then structural native keys and original per-module declaration selections.','A witness to one compiled symbol marks its historical source unit; it does not show that every line or generated member is necessary.','Stage2 structural-name and exact native-range correspondence is not creation provenance and is not promoted to an imported dependency witness.','No missing observation is classified unused; symbolic-name existence, compiler attributes, macro-only and other CI/runtime consumers remain open.','All physical_span_lines are historical raw LF spans; masked reported units remain separate. Changed historical files are never remapped.','Provenance is pinned-file path/marker classification; untraced and chain/agreement files are not certified handwritten. Historical source drift has its own bucket.', 'Cache contents are externally trusted; explicit queried artifact bytes and all producer/input/output hashes are receipt-bound.'])
 outputs={'candidate-snapshot-summary.json':json.dumps(summary,sort_keys=True,indent=2)+'\n'}
 f=io.StringIO();fields=list(rows[0]);w=csv.DictWriter(f,fieldnames=fields,delimiter='\t',lineterminator='\n');w.writeheader()
 for r in rows:w.writerow(dict(r,imported_symbols=json.dumps(r['imported_symbols'],separators=(',',':')),stage2_correspondences=json.dumps(r['stage2_correspondences'],separators=(',',':'))))
 outputs['candidate-snapshot-bindings.tsv']=f.getvalue()
 assert producers=={n:SHA(HERE/n) for n in names};assert artifacts=={p:SHA(pathlib.Path(p)) for p in artifacts};API['assert_sources'](a.source_root)
 for name,body in outputs.items():
  assert len(body.encode())<1000000,name
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 print('CANDIDATE_SNAPSHOT_BINDING_PASS',len(rows),sum(r['status']=='imported_snapshot_dependency_witness' for r in rows),sum(r['status']=='stage2_range_correspondence_only' for r in rows))
if __name__=='__main__':main()
