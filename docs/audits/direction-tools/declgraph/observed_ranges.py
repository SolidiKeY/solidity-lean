#!/usr/bin/env python3
"""Positive imported-check support footprint, never global test exclusivity.
Reuse accepted corpora and unchanged cache-only CachedKeys.lean. Native graph
body/cache provenance remains external trust; identity does not attest bodies.
"""
if not __debug__:raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import argparse,collections,csv,functools,hashlib,io,json,os,pathlib,re,resource,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
C=runpy.run_path(str(HERE/'combine_candidate_witnesses_v2.py'));R=C['R'];Q=R['Q'];API=Q['API'];SHA=Q['SHA'];NS=runpy.run_path(str(HERE/'native_summary.py'));N=runpy.run_path(str(HERE/'owned_native.py'))
@functools.lru_cache(maxsize=8192)
def lf_parts(text):return text.split('\n')
def native_lines(text,r):
 if r is None:return None
 assert len(r)==4 and all(type(x) is int for x in r)
 a,b,c,d=r;parts=lf_parts(text);count=text.count('\n')+int(bool(text) and not text.endswith('\n'))
 assert 0<=a<=c<=count and b>=0 and d>=0 and (a,b)<=(c,d)
 def column(line,col):
  if line==count:assert col==0 and (not text or text.endswith('\n'));return
  offsets={0};total=0
  for ch in parts[line]:total+=len(ch.encode('utf-16-le'))//2;offsets.add(total)
  assert col in offsets,'Native UTF16 endpoint does not match pinned source'
 column(a,b);column(c,d)
 if (a,b)==(c,d):return set()
 result=set(range(a+1,c+int(d>0)+1));assert all(1<=n<=count for n in result)
 return result

def footprint_counts(text,facade,observed):
 count=text.count('\n')+int(bool(text) and not text.endswith('\n'))
 assert all(1<=n<=count for n in facade|observed),'Footprint line outside pinned source'
 return len(facade),len(observed-facade),count-len(facade|observed)

def safe_paths(a):
 for name in ('source_root','view','graph','combined','combined_evidence','replay','replay_evidence','capture','out','evidence'):setattr(a,name,pathlib.Path(getattr(a,name)).resolve())
 assert a.prefix>0
 assert a.out==HERE/f'observed-ranges-prefix{a.prefix}','Designated checker directory required'
 for product in (a.capture,a.evidence):
  for protected in (HERE.parents[3],a.source_root,a.view,a.graph,a.combined,a.replay,a.combined_evidence,a.replay_evidence):
   assert not product.is_relative_to(protected) and not protected.is_relative_to(product),'Product overlaps protected input/code'
 for protected in (a.source_root,a.view,a.graph,a.combined,a.replay,a.combined_evidence,a.replay_evidence):
  assert not a.out.is_relative_to(protected) and not protected.is_relative_to(a.out),'Checker overlaps protected input'
 assert not a.evidence.is_relative_to(a.capture) and not a.capture.is_relative_to(a.evidence),'Capture/evidence overlap'
 if not a.check:assert not a.capture.exists() and not a.evidence.exists(),'Fresh private capture/evidence required'

def tabular(header,rows):
 out=io.StringIO();w=csv.writer(out,lineterminator='\n');w.writerow(header);w.writerows(rows);return out.getvalue()

def validate_chunk(meta,fixed,directory,body):
 assert all(meta[k]==v for k,v in fixed.items()) and type(meta['exit_code']) is int,'Native chunk recipe drift'
 expected={'query.json','capture.log'}
 if meta['exit_code']==0 or (directory/'keys.jsonl').exists():expected.add('keys.jsonl')
 assert set(meta['outputs'])==expected,'Native chunk output set incomplete or unexpected'
 assert (directory/'query.json').read_text()==body,'Native query text drift'
 for name,h in meta['outputs'].items():assert SHA(directory/name)==h,'Native chunk output digest drift'

def main():
 p=argparse.ArgumentParser()
 for n in ('source-root','view','graph','combined','combined-evidence','replay','replay-evidence','capture','out','evidence'):p.add_argument('--'+n,type=pathlib.Path,required=True)
 p.add_argument('--prefix',type=int,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 for n in ('source_root','view','graph','combined','combined_evidence','replay','replay_evidence','capture','out','evidence'):setattr(a,n,getattr(a,n).resolve())
 # Bound Python address space as well as each serial native query heap.
 limit=10*1024**3;soft,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(min(limit,soft if soft!=-1 else limit,hard if hard!=-1 else limit),hard))
 with Q['writer_lease']() as lease:
  safe_paths(a);src=API['assert_sources'](a.source_root);inputs={};producers={n:SHA(HERE/n) for n in ('observed_ranges.py','CachedKeys.lean','combine_candidate_witnesses_v2.py','replay_cached_checks_v2.py','compact_records_v2.py','native_summary.py','module_graph.py','ModuleExport.lean','audit.py','capture_cached_checks.py','owned_native.py','lease_lifecycle.py','map_snapshot_candidates.py')}
  def remember(path,expected=None):
   path=pathlib.Path(path);h=SHA(path);assert expected is None or h==expected,'Input digest drift: '+str(path)
   assert str(path) not in inputs or inputs[str(path)]==h;inputs[str(path)]=h;return h
  remember(a.combined_evidence);proof=json.loads(a.combined_evidence.read_text());assert proof['base']==API['BASE']
  for path,h in proof['inputs'].items():remember(path,h)
  for name,h in proof['outputs'].items():remember(a.combined/name,h)
  remember(a.replay_evidence);rp=json.loads(a.replay_evidence.read_text());assert rp['base']==API['BASE'] and inputs[str(a.replay_evidence)]==proof['inputs'][str(a.replay_evidence)]
  for name,h in rp['producers'].items():remember(HERE/name,h)
  for path,h in rp['inputs'].items():remember(path,h)
  for name,h in rp['outputs'].items():remember(a.replay/name,h)
  summary=json.loads((a.combined/'summary.json').read_text());replay=json.loads((a.replay/'summary.json').read_text());assert replay['selected_files']==a.prefix and summary['observed_additional_source_files']==replay['observed_files']
  imports={};stage2={};C['merge_rows'](imports,stage2,C['read_tsv'](HERE/'snapshot-imported-bindings.tsv'),C['read_tsv'](HERE/'snapshot-stage2-bindings.tsv'))
  for name in replay['tables']:
   assert name.startswith(('imported-','stage2-')),'Unexpected replay table'
   rows=C['read_tsv'](a.replay/name)
   C['merge_rows'](imports,stage2,rows if name.startswith('imported-') else [],rows if name.startswith('stage2-') else [])
  assert len(imports)==summary['combined_imported_units'] and len(stage2)==summary['combined_stage2_units']
  paths=R['source_paths'](src,a.view,inputs);assert set(paths)==set((HERE/'modules.txt').read_text().splitlines())
  gr=pathlib.Path(str(a.graph)+'.receipt.json');remember(gr);gmeta=json.loads(gr.read_text());remember(a.graph,gmeta['index_sha256']);assert pathlib.Path(gmeta['reference_view']).resolve()==a.view
  version=subprocess.check_output(['lean','--version'],text=True).strip();assert version==gmeta['lean']==rp['lean']
  wanted=collections.defaultdict(set)
  for row in imports.values():assert row['module'] in paths;wanted[row['module']].add(row['name'])
  query=[];artifacts={}
  for module,names in sorted(wanted.items()):
   artifact=a.view/pathlib.Path(paths[module].removeprefix('vendor/LeanTeX/').removeprefix('Bridge/')).with_suffix('.olean');artifacts[str(artifact)]=remember(artifact)
   query.append(dict(module=module,artifacts=[str(artifact)],names=sorted(names)))
  if not a.check:a.capture.mkdir(parents=True)
  keys={};chunk_receipts={};query_failures=[]
  for index,start in enumerate(range(0,len(query),100)):
   selected=query[start:start+100];directory=a.capture/f'{index:04d}';qfile=directory/'query.json';log=directory/'capture.log';keyfile=directory/'keys.jsonl';receipt=directory/'receipt.json';body=json.dumps(selected,sort_keys=True,separators=(',',':'))+'\n'
   command=['lean','--tstack=131072','-j1','-M4000','--run',str(HERE/'CachedKeys.lean'),str(qfile),str(keyfile)]
   fixed=dict(command=command,query_sha256=hashlib.sha256(body.encode()).hexdigest(),lean=version,artifacts={q['artifacts'][0]:artifacts[q['artifacts'][0]] for q in selected},producer_sha256=producers['CachedKeys.lean'],timeout_seconds=300)
   if a.check:
    meta=json.loads(receipt.read_text())
   else:
    directory.mkdir();Q['atomic_text'](qfile,body)
    with log.open('w') as output:code=N['run'](command,output,cwd=a.source_root,env=dict(os.environ,LEAN_NUM_THREADS='1'),lease=lease,timeout=300)
    meta=dict(fixed,exit_code=code,outputs={n:SHA(directory/n) for n in ('query.json','capture.log','keys.jsonl') if (directory/n).exists()});Q['atomic_json'](receipt,meta)
   validate_chunk(meta,fixed,directory,body)
   chunk_receipts[str(receipt)]=remember(receipt)
   for n,h in meta['outputs'].items():remember(directory/n,h)
   if meta['exit_code']:
    query_failures.append(dict(chunk=index,exit_code=meta['exit_code'],modules=[q['module'] for q in selected]));continue
   assert 'keys.jsonl' in meta['outputs'];mods={};found=[]
   for line in keyfile.open():
    row=json.loads(line)
    if row['record']=='key':found.append(row)
    else:assert row['record']=='module' and row['module'] not in mods;mods[row['module']]=row
   assert set(mods)=={q['module'] for q in selected} and all(row['module'] in mods for row in found)
   for row in found:
    k=(row['module'],row['name']);assert k not in keys,'Ambiguous native printed identity';keys[k]=row
   for q in selected:
    seen={r['name'] for r in found if r['module']==q['module']};assert seen<=set(q['names']);assert mods[q['module']]['requested_names']==len(q['names']) and mods[q['module']]['missing_names']==[n for n in q['names'] if n not in seen]
   marker=re.findall(r'CACHED_KEYS_PASS (\d+) (\d+) (\d+) (\d+)',log.read_text());assert len(marker)==1 and tuple(map(int,marker[0]))==(len(selected),len(found),sum(len(r['missing_names']) for r in mods.values()),len(selected))
   print('OBSERVED_CACHE_KEYS_PASS',index+1,len(query),len(found),flush=True)
  # No heavy Python graph is retained alongside a native query.
  graph=NS['NATIVE']['load'](a.graph);assert set(paths)=={m for m,r in graph.modules.items() if r['selected']}
  roots={name for (module,name),row in graph.nodes.items() if module=='Solidity.Theorems' and row['kind']=='theorem' and row['selection'] is not None};facade_all,boundary=graph.root_closure('Solidity.Theorems',roots);facade=facade_all&graph.nodes.keys()
  lines=collections.defaultdict(lambda:collections.defaultdict(set));areas=collections.defaultdict(collections.Counter);directories=collections.defaultdict(collections.Counter);provenance=collections.defaultdict(collections.Counter);labels={p:API['provenance'](p,t) for p,t in src.items()};units={};unresolved=collections.Counter();bound=set()
  def destinations(path):return (areas['/'.join(path.split('/')[:2])],directories[str(pathlib.PurePosixPath(path).parent)],provenance[labels[path]])
  def add_range(key,cls):
   path=paths[key[0]];r=graph.nodes[key]['range']
   try:covered=native_lines(src[path],r)
   except (AssertionError,UnicodeError):
    for target in destinations(path):target[cls+'_invalid_source_range_units']+=1
    return 'invalid_source_range'
   if covered is None:
    for target in destinations(path):target[cls+'_without_source_range_units']+=1
    return 'without_source_range'
   lines[path][cls].update(covered);return 'valid_source_range'
  for key in facade:
   for target in destinations(paths[key[0]]):target['facade_serialized_constants']+=1
   add_range(key,'facade')
  failed_modules={m for failure in query_failures for m in failure['modules']}
  for identity,row in sorted(imports.items()):
   module,name=row['module'],row['name'];key=(module,name);native=keys.get(key);status='native_query_failed' if module in failed_modules else 'missing_native_key';range_status='unbound';inside=None
   if native is not None:
    if C['M']['keyhash'](native['name_key'])!=row['name_key_sha256'] or native['constant_kind']!=row['constant_kind']:status='native_identity_mismatch'
    elif key not in graph.nodes or graph.nodes[key]['kind']!=native['constant_kind']:status='graph_identity_mismatch'
    else:
     status='native_key_bound';bound.add(key);inside=key in facade;range_status=add_range(key,'observed_imported')
   unresolved[status]+=1;path=paths[module]
   for target in destinations(path):target[status+'_imported_units']+=1
   units[identity]=[module,name,row['name_key_sha256'],row['constant_kind'],path,status,'' if inside is None else int(inside),range_status,json.dumps(graph.nodes[key]['range'],separators=(',',':')) if status=='native_key_bound' else 'null']
  for path in paths.values():
   core_count,extra_count,uncovered=footprint_counts(src[path],lines[path]['facade'],lines[path]['observed_imported'])
   for target in destinations(path):
    target['facade_native_range_lines']+=core_count;target['observed_imported_outside_facade_native_range_lines']+=extra_count;target['outside_both_observed_footprints_lines']+=uncovered
  assert unresolved['native_key_bound']==len(bound) and sum(unresolved.values())==len(imports)
  outputs=R['shards']('units',['module','name','name_key_sha256','constant_kind','path','binding_status','inside_facade_if_bound','range_status','native_range'],units)
  for name,rows in [('areas.csv',areas),('directories.csv',directories),('provenance.csv',provenance)]:
   fields=sorted(set().union(*(r.keys() for r in rows.values())));outputs[name]=tabular(['path']+fields,[[path]+[r[f] for f in fields] for path,r in sorted(rows.items())])
  totals=dict(sum((r for r in areas.values()),collections.Counter()));assert totals==dict(sum((r for r in directories.values()),collections.Counter()))==dict(sum((r for r in provenance.values()),collections.Counter()))
  result=dict(base=API['BASE'],status='partial',selected_cached_sources=a.prefix,observed_dense_sources=summary['observed_dense_source_files'],observed_additional_sources=summary['observed_additional_source_files'],imported_units=len(imports),binding_counts=dict(sorted(unresolved.items())),queried_modules=len(query),query_chunks=len(chunk_receipts),query_failures=query_failures,facade_theorem_roots=len(roots),facade_selected_constants=len(facade),facade_loaded_constants=len(facade_all),facade_boundary=dict(boundary),observed_imported_inside_facade=len(bound&facade),observed_imported_outside_facade=len(bound-facade),stage2_name_range_units_excluded=len(stage2),totals=totals,tables=sorted(outputs),deletable_now_verified_lines=0,boundaries=['Positive imported-pointer observations are matched to native structural key and kind before native graph source ranges; printed names select lookup candidates only.','Graph-body/cache provenance is externally trusted. A fresh key match does not attest proof-body equivalence or repair that provenance gap.','Observed support outside this fixed facade context is not global test exclusivity, unusedness or necessity of every charged line.','Source ranges use raw LF lines, valid UTF16 codepoint endpoints and facade-first union; missing/invalid ranges are explicit. Stage2 name/range inventory is excluded; no new correspondence is asserted.','Untraced provenance is not certified handwritten; generated and unresolved generator labels remain separate.','The accepted combined/replay receipts and all their inputs/outputs are sealed here; semantic root replay is reused, not re-executed by this footprint.','H347 exact pinned baseline retained; verification blocked, additive v2 unadopted and zero deletions certified.'])
  outputs['summary.json']=json.dumps(result,sort_keys=True,indent=2)+'\n';assert all(len(v.encode())<1000000 for v in outputs.values())
  assert all(SHA(pathlib.Path(n))==h for n,h in inputs.items()) and producers=={n:SHA(HERE/n) for n in producers};API['assert_sources'](a.source_root)
  final=dict(base=API['BASE'],producers=producers,inputs=inputs,chunk_receipts=chunk_receipts,outputs={n:hashlib.sha256(v.encode()).hexdigest() for n,v in outputs.items()})
  if a.check:assert json.loads(a.evidence.read_text())==final and {p.name for p in a.out.iterdir()}==set(outputs) and all((a.out/n).read_text()==v for n,v in outputs.items())
  else:
   a.out.mkdir(parents=True,exist_ok=True);assert not {p.name for p in a.out.iterdir()}-set(outputs),'Unexpected output files'
   for n,v in outputs.items():Q['atomic_text'](a.out/n,v)
   Q['atomic_json'](a.evidence,final);assert json.loads(a.evidence.read_text())==final and all(SHA(a.out/n)==h for n,h in final['outputs'].items())
   assert all(SHA(pathlib.Path(n))==h for n,h in inputs.items()) and producers=={n:SHA(HERE/n) for n in producers};API['assert_sources'](a.source_root)
  print('OBSERVED_RANGES_PASS',len(imports),len(bound),len(bound-facade),json.dumps(totals,sort_keys=True))
if __name__=='__main__':main()
