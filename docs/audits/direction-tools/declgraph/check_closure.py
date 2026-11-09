#!/usr/bin/env python3
"""Project native check observations through the cached final-context model.
Run serial with writer lock. Native identity census precedes the Python graph;
--check replays a producer/input-bound native census without rerunning Lean.
No full check-proof, executed-program or deletion certification is provided.
"""
import argparse,collections,csv,hashlib,io,json,re,os,pathlib,resource,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));NG=runpy.run_path(str(HERE/'module_graph.py'));NS=runpy.run_path(str(HERE/'native_summary.py'));SHA=NG['sha']
CLASSES=('facade','observed_check_additional','outside_measured_closures')

def project(source_root,graph,view,checks,identity,native_names):
 src=API['assert_sources'](source_root);source_provenance={p:API['provenance'](p,t) for p,t in src.items()};g=NG['load'](graph);allpaths=NS['module_paths'](src,view);paths={m:allpaths[m] for m,r in g.modules.items() if r['selected']}
 observations=[n for f in checks['files'] if f['status']=='pass' for n in f['observed_constants']]
 assert identity['collisions']==[] and identity['constant_records']==len(g.records) and identity['loaded_modules']==len(g.modules)
 assert identity['observation_rows']==len(observations)
 assert identity['name_occurrences']==sum(1+len(r['refs']) for r in g.records.values())+len(observations)
 names=set(g.providers)
 for r in g.records.values():names.update(r['refs'])
 names.update(n['name'] for n in observations);assert len(names)==identity['unique_printed_names']
 assert len(native_names)==len(set(native_names)) and native_names==sorted(native_names) and names==set(native_names),'Native/graph name-universe mismatch'
 name_digest=hashlib.sha256(json.dumps(sorted(names),separators=(',',':'),ensure_ascii=True).encode()).hexdigest()
 reached=set();contexts=[]
 for f in checks['files']:
  if f['status']!='pass':continue
  context=f['path'][:-5].replace('/','.');assert paths[context]==f['path']
  used,boundary=g.root_closure(context,[n['name'] for n in f['observed_constants']]);reached.update(used)
  contexts.append(dict(path=f['path'],observed_constant_names=len(f['observed_constants']),loaded_model_records=len(used),selected_model_records=len(used&g.nodes.keys()),boundary=dict(sorted(boundary.items()))))
 roots=[n for (m,n),r in g.nodes.items() if m=='Solidity.Theorems' and r['kind']=='theorem' and r['selection'] is not None]
 facade,fb=g.root_closure('Solidity.Theorems',roots);assert not fb
 selected=reached&g.nodes.keys();sets={'facade':facade&g.nodes.keys(),'observed_check_additional':selected-facade,'outside_measured_closures':g.nodes.keys()-(facade|selected)}
 assert sum(map(len,sets.values()))==len(g.nodes)
 line_counts={p:t.count('\n')+int(bool(t) and not t.endswith('\n')) for p,t in src.items()};areas=collections.defaultdict(collections.Counter);directories=collections.defaultdict(collections.Counter);provenance=collections.defaultdict(collections.Counter);lines=collections.defaultdict(lambda:collections.defaultdict(set))
 def dest(p):return (areas['/'.join(p.split('/')[:2])],directories[str(pathlib.PurePosixPath(p).parent)],provenance[source_provenance[p]])
 for cls,keys in sets.items():
  for key in keys:
   r=g.nodes[key];p=paths[key[0]];ds=dest(p)
   for d in ds:d[cls+'_serialized_constants']+=1
   if r['range'] is None:
    for d in ds:d['without_native_source_range']+=1
    continue
   a,b,c,d=r['range'];assert 0<=a<=c<=line_counts[p]
   lines[p][cls].update(range(a+1,c+(1 if d else 0)+1))
 for p in paths.values():
  taken=set()
  for cls in CLASSES:
   charged=lines[p][cls]-taken;taken.update(charged)
   for d in dest(p):d[cls+'_native_range_lines']+=len(charged)
  assert len(taken)<=line_counts[p]
  for d in dest(p):d['unattributed_physical_lines']+=line_counts[p]-len(taken)
 summary=dict(base=API['BASE'],status='partial',native_identity=identity,matched_name_set_sha256=name_digest,source_contexts=contexts,selected_modules=len(paths),selected_serialized_constants=len(g.nodes),facade_roots=len(roots),observed_check_loaded_union=len(reached),observed_check_selected_union=len(selected),classes={k:len(v) for k,v in sets.items()},indexed_physical_lines=sum(line_counts[p] for p in paths.values()),missing_source_files=len(src)-len(paths),provenance={k:dict(sorted(v.items())) for k,v in sorted(provenance.items())},deletable_now_verified_lines=0,verdict='The final-context model projects additional compiled bindings beyond the facade from observed check names. This does not show that the checks consumed those bodies. Outside these measured closures is not unused; no deletion is certified.',boundaries=['The native identity census proves display-key injectivity only for these loaded constants/references and structurally keyed observations; module identities stay separate.','Each observed constant seeds the existing fixed FINAL compiled-module environment model. Earlier command environments, discarded anonymous proof bodies and complete check dependencies are not reconstructed.','Names absent from the compiled pool remain explicit model boundaries; counts are not executed-program liveness.','Selection covers19 syntax-census candidate-family files, not macro-only files, other consumers, all CI or runtime roots.','Line ranges are native LF spans, charged facade then additional checks then outside; unattributed physical lines remain separate.','Provenance is file-level path/marker classification; unmarked files are not certified handwritten.','Imported artifact bytes are externally trusted; native result receipts bind producers, module list, observations, graph, source and outputs.'])
 outputs={'check-closure-summary.json':json.dumps(summary,sort_keys=True,indent=2)+'\n'}
 for name,rows in [('check-closure-areas.csv',areas),('check-closure-directories.csv',directories)]:
  out=io.StringIO();fields=sorted(set().union(*(r.keys() for r in rows.values())));w=csv.writer(out,lineterminator='\n');w.writerow(['path']+fields)
  for k,r in sorted(rows.items()):w.writerow([k]+[r[f] for f in fields])
  outputs[name]=out.getvalue()
 return outputs

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--capture',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 for k in ('source_root','graph','view','capture','out'):setattr(a,k,getattr(a,k).resolve())
 API['assert_sources'](a.source_root);graph_receipt=json.loads(pathlib.Path(str(a.graph)+'.receipt.json').read_text());assert pathlib.Path(graph_receipt['reference_view']).resolve()==a.view,'Census must use the original graph artifact view';producers={n:SHA(HERE/n) for n in ('NameIdentity.lean','check_closure.py','module_graph.py','native_summary.py','audit.py','modules.txt','check-reference-summary.json')};checks=json.loads((HERE/'check-reference-summary.json').read_text());assert checks['base']==API['BASE']
 observations=[n for f in checks['files'] if f['status']=='pass' for n in f['observed_constants']];obs=json.dumps(observations,separators=(',',':'))+'\n';assert observations
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 command=['lean','--tstack=131072','-j1','-M6000','--run',str(HERE/'NameIdentity.lean'),str(HERE/'modules.txt'),str(a.capture/'observations.json'),str(a.capture/'identity.json')];fixed=dict(producers=producers,lean=version,command=command,view=str(a.view),graph_sha256=SHA(a.graph),graph_receipt_sha256=SHA(pathlib.Path(str(a.graph)+'.receipt.json')));receipt=a.capture/'receipt.json'
 if a.check:
  meta=json.loads(receipt.read_text());assert all(meta[k]==v for k,v in fixed.items()) and meta['exit_code']==0
  for n in ('observations.json','identity.json','identity.json.names.jsonl','capture.log'):assert meta['outputs'][n]==SHA(a.capture/n)
  assert (a.capture/'observations.json').read_text()==obs
 else:
  assert not a.capture.exists(),'Fresh capture directory required';a.capture.mkdir(parents=True);(a.capture/'observations.json').write_text(obs)
  def limits():resource.setrlimit(resource.RLIMIT_AS,(14*1024**3,14*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
  with (a.capture/'capture.log').open('w') as log:result=subprocess.run(command,env=dict(os.environ,LEAN_PATH=str(a.view),LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT,timeout=600,preexec_fn=limits)
  assert result.returncode==0,'Native identity census failed; no graph join published'
  meta=dict(fixed,exit_code=result.returncode,outputs={n:SHA(a.capture/n) for n in ('observations.json','identity.json','identity.json.names.jsonl','capture.log')});receipt.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
 identity=json.loads((a.capture/'identity.json').read_text());assert not identity['collisions']
 marker=re.findall(r'NAME_IDENTITY_CHECK_PASS (\d+) (\d+) (\d+)',(a.capture/'capture.log').read_text());assert len(marker)==1 and tuple(map(int,marker[0]))==(identity['constant_records'],identity['unique_printed_names'],len(identity['collisions']))
 native_names=[json.loads(line) for line in (a.capture/'identity.json.names.jsonl').read_text().splitlines()]
 outputs=project(a.source_root,a.graph,a.view,checks,identity,native_names)
 assert producers=={n:SHA(HERE/n) for n in producers};API['assert_sources'](a.source_root)
 for name,body in outputs.items():
  assert len(body.encode())<1000000
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 print('CHECK_CLOSURE_MODEL_PASS',identity['constant_records'],identity['unique_printed_names'],identity['collisions'])
if __name__=='__main__':main()
