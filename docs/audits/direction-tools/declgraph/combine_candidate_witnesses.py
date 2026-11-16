#!/usr/bin/env python3
"""Join validated saved-check corpora to native historical source units.
No printed-name or directory match supplies a dependency. This combines positive
witnesses only; non-observation never establishes unusedness or deletability.
"""
import argparse,collections,csv,hashlib,json,pathlib,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
M=runpy.run_path(str(HERE/'map_snapshot_candidates.py'));R=runpy.run_path(str(HERE/'replay_cached_checks.py'));Q=R['Q'];API=Q['API'];SHA=Q['SHA']
def read_tsv(path):return list(csv.DictReader(path.open(),delimiter='\t'))
def merge_rows(imports,stage2,im,st):
 a={};b={}
 for r in im:
  k=(r['module'],r['name_key_sha256']);assert k not in a or a[k]==r;a[k]=r
 for r in st:
  k=(r['path'],r['name_key_sha256'],r['own_range']);assert k not in b or b[k]==r;b[k]=r
 assert all(k not in imports or imports[k]==v for k,v in a.items())
 assert all(k not in stage2 or stage2[k]==v for k,v in b.items())
 imports.update(a);stage2.update(b)

def candidate_imports(candidates,keys,paths,imports):
 bypath={p:m for m,p in paths.items()};wanted={}
 for c in candidates:
  if not c['unchanged_at_base']:continue
  for name in c['native_symbols']:
   module=bypath[c['path']];r=keys[module,name];k=(module,M['keyhash'](r['name_key']))
   assert k not in wanted or wanted[k]==(name,r['constant_kind']);wanted[k]=(name,r['constant_kind'])
 result=[]
 for k,r in imports.items():
  if k in wanted:
   assert (r['name'],r['constant_kind'])==wanted[k],'Native candidate identity mismatch'
   result.append(r)
 return result

def combined_provenance(imported,stage2,paths,src):
 im={k:tuple(r[n] for n in ('module','name','name_key_sha256','constant_kind')) for k,r in imported.items()}
 st={k:[r[n] for n in ('path','name','name_key_sha256','own_range','constant_kind','seen_as_root','seen_as_dependency')] for k,r in stage2.items()}
 return R['unit_provenance'](im,st,paths,src)

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--keys',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--queue-summary',type=pathlib.Path,required=True);p.add_argument('--replay-dir',type=pathlib.Path,required=True);p.add_argument('--replay-evidence',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--evidence',type=pathlib.Path,required=True);p.add_argument('--prior-runner-commit',action='append',default=[]);p.add_argument('--allow-prefix',action='store_true');p.add_argument('--check',action='store_true');a=p.parse_args()
 for k in ('source_root','view','graph','keys','captures','queue_summary','replay_dir','replay_evidence','out','evidence'):setattr(a,k,getattr(a,k).resolve())
 # Seal the exact prechecked worlds. The replay owns its own writer lease;
 # the legacy mapper is checked with the lease held by this process.
 with Q['writer_lease']():
  seals={str(a.replay_evidence):SHA(a.replay_evidence),str(a.keys/'receipt.json'):SHA(a.keys/'receipt.json')}
  for n in ('combine_candidate_witnesses.py','map_snapshot_candidates.py','replay_cached_checks.py','capture_cached_checks.py','native_summary.py'):seals[str(HERE/n)]=SHA(HERE/n)
 replay=['python3','-I',str(HERE/'replay_cached_checks.py'),'--source-root',str(a.source_root),'--view',str(a.view),'--captures',str(a.captures),'--queue-summary',str(a.queue_summary),'--out',str(a.replay_dir),'--evidence',str(a.replay_evidence),'--check']
 for commit in a.prior_runner_commit:replay+=['--prior-runner-commit',commit]
 if a.allow_prefix:replay+=['--allow-prefix']
 x=subprocess.run(replay,capture_output=True,text=True);assert x.returncode==0,x.stdout+x.stderr
 legacy=['python3','-I',str(HERE/'map_snapshot_candidates.py'),'--source-root',str(a.source_root),'--view',str(a.view),'--graph',str(a.graph),'--capture',str(a.keys),'--out',str(HERE),'--check']
 with Q['writer_lease']():
  y=subprocess.run(legacy,capture_output=True,text=True);assert y.returncode==0,y.stdout+y.stderr
  assert all(SHA(pathlib.Path(p))==h for p,h in seals.items()),'Prechecked world changed'
  src=API['assert_sources'](a.source_root);inputs=dict(seals)
  def remember(path,digest=None):
   h=SHA(path) if digest is None else digest;assert str(path) not in inputs or inputs[str(path)]==h;inputs[str(path)]=h
  rm=json.loads(a.replay_evidence.read_text());km=json.loads((a.keys/'receipt.json').read_text())
  for n,h in rm['producers'].items():remember(HERE/n,h)
  for n,h in km['producers'].items():remember(HERE/n,h)
  for p,h in rm['inputs'].items():remember(pathlib.Path(p),h)
  for p,h in km['artifacts'].items():remember(pathlib.Path(p),h)
  for n,h in rm['outputs'].items():remember(a.replay_dir/n,h)
  for n,h in km['outputs'].items():remember(a.keys/n,h)
  for n in ('combine_candidate_witnesses.py','native_summary.py','historical.py'):remember(HERE/n)
  remember(a.graph);remember(pathlib.Path(str(a.graph)+'.receipt.json'));assert km['graph_sha256']==inputs[str(a.graph)]
  mapping_inputs={};paths=R['source_paths'](src,a.view,mapping_inputs)
  for p,h in mapping_inputs.items():remember(pathlib.Path(p),h)
  assert set(paths)==set((HERE/'modules.txt').read_text().splitlines())
  names=[f.strip('/').replace('/','_')+'-candidates.json' for f in API['FAMILIES']]
  candidates=[c for n in names for c in json.loads((HERE/n).read_text())]
  keys={}
  for line in (a.keys/'keys.jsonl').open():
   r=json.loads(line)
   if r['record']=='key':
    k=(r['module'],r['name']);assert k not in keys;keys[k]=r
  nodes={}
  for line in a.graph.open():
   r=json.loads(line)
   if r['record']=='constant' and (r['module'],r['name']) in keys:
    k=(r['module'],r['name']);assert k not in nodes;nodes[k]=r
  assert set(nodes)==set(keys)
  imported={};stage2={};old=json.loads((HERE/'snapshot-root-summary.json').read_text());new=json.loads((a.replay_dir/'summary.json').read_text());queue=json.loads(a.queue_summary.read_text())
  selected={r['path'] for r in queue['files'] if r['status']=='observed'};dense={r['path'] for r in old['files'] if r['status']=='observed'};assert not selected&dense
  for n in ('snapshot-root-summary.json','snapshot-imported-bindings.tsv','snapshot-stage2-bindings.tsv'):remember(HERE/n)
  old_im=read_tsv(HERE/'snapshot-imported-bindings.tsv');old_st=read_tsv(HERE/'snapshot-stage2-bindings.tsv');assert {r['path'] for r in old_st}<=dense
  merge_rows(imported,stage2,old_im,old_st)
  im=[];st=[]
  for n in new['tables']:
   rows=read_tsv(a.replay_dir/n)
   if n.startswith('imported-'):im+=rows
   else:assert n.startswith('stage2-');st+=rows
  assert len(im)==new['imported_pointer_binding_units'] and len(st)==new['stage2_name_range_units']
  assert {r['path'] for r in st}<=selected
  merge_rows(imported,stage2,im,st)
  imported_provenance,stage2_provenance=combined_provenance(imported,stage2,paths,src)
  filtered=candidate_imports(candidates,keys,paths,imported)
  rows,totals,ib,sb=M['bind'](candidates,nodes,filtered,list(stage2.values()),keys,paths)
  provenance=collections.defaultdict(collections.Counter)
  for c,r in zip(candidates,rows):
   label=API['provenance'](c['path'],src[c['path']]) if c['unchanged_at_base'] else 'historical_source_drift'
   provenance[label][r['status']+'_units']+=1;provenance[label][r['status']+'_physical_span_lines']+=c['physical_span_lines']
  fields=list(rows[0]);items={}
  for c,r in zip(candidates,rows):items[c['path'],c['source_start_char'],c['source_end_char']]=[json.dumps(r[k],separators=(',',':')) if isinstance(r[k],list) else r[k] for k in fields]
  outputs=R['shards']('candidate',fields,items)
  result=dict(base=API['BASE'],status='partial',candidate_units=len(rows),observed_dense_source_files=len(dense),observed_additional_source_files=len(selected),combined_imported_units=len(imported),combined_stage2_units=len(stage2),combined_imported_provenance=imported_provenance,combined_stage2_provenance=stage2_provenance,imported_symbols_bound_to_candidates=ib,stage2_correspondences_bound_to_candidates=sb,families={k:dict(sorted(v.items())) for k,v in sorted(totals.items())},provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},tables=sorted(outputs),deletable_now_verified_lines=0,verdict=M['verdict'](ib,sb),settling_measurement='An isolated removal replay of the complete affected-root suite on an authorized valid baseline, recording native symbolic, macro and attribute dependencies.',boundaries=['This joins already validated corpora; replayed source files are disjoint and imported units deduplicate by module plus native structural-name hash.','A use elsewhere in a family does not mark a historical candidate; matching requires its original native key, kind and source binding.','A witness marks an entire historical unit, not necessity of every line. Stage2 range correspondence is not creation provenance.','Missing observations are not unusedness. Root, symbolic-name, attribute, reflective and runtime coverage remains incomplete.','Physical spans are historical raw LF units; changed historical files remain drift, never remapped. Provenance labels do not certify handwriting.','Per-file output replacement is not a batch transaction; interrupted outputs require successful --check or regeneration before use.'])
  outputs['summary.json']=json.dumps(result,sort_keys=True,indent=2)+'\n';assert all(len(b.encode())<1000000 for b in outputs.values())
  assert all(SHA(pathlib.Path(p))==h for p,h in inputs.items());API['assert_sources'](a.source_root)
  proof=dict(base=API['BASE'],inputs=inputs,prechecks=[dict(command=replay,output=x.stdout),dict(command=legacy,output=y.stdout)],outputs={n:hashlib.sha256(b.encode()).hexdigest() for n,b in outputs.items()})
  existing={p.name for pattern in ('candidate-*.tsv','summary.json') for p in a.out.glob(pattern)}
  if a.check:
   assert existing==set(outputs) and all((a.out/n).read_text()==b for n,b in outputs.items()),'Stale combined candidate output'
   assert json.loads(a.evidence.read_text())==proof,'Combined candidate evidence drift'
  else:
   a.out.mkdir(parents=True,exist_ok=True)
   for n in existing-set(outputs):(a.out/n).unlink()
   for n,b in sorted(outputs.items(),key=lambda kv:kv[0]=='summary.json'):Q['atomic_text'](a.out/n,b)
   Q['atomic_json'](a.evidence,proof)
  print('COMBINED_CANDIDATE_PASS',len(rows),len(imported),len(stage2),ib,sb)
if __name__=='__main__':main()
