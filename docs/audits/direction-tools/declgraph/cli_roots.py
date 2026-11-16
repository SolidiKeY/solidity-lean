#!/usr/bin/env python3
"""Compile two CLI leaves separately and measure fixed-context native roots.
No CLI main is executed. Requires writer lock, pinned Lean, validated warm
imports, serial work. --check reuses hashed artifacts and replays accounting.
"""
import argparse,collections,csv,hashlib,io,json,os,pathlib,runpy,shlex,subprocess,time,tomllib
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));NATIVE=runpy.run_path(str(HERE/'module_graph.py'));WARM=runpy.run_path(str(HERE/'warm_checks.py'))
TARGETS=['SolidityLean','SolkeyCheck']

def sha(p):return NATIVE['sha'](p)

def extend_leaf(g,module,constants):
 """Old contexts cannot see a newly appended leaf; preserve their edges."""
 m=module['module'];assert m not in g.modules and module['selected'] and not module['is_module']
 assert module['names']==[r['name'] for r in constants] and len(set(module['names']))==len(constants)
 assert all(r['module']==m for r in constants)
 assert all(dep in g.modules for dep in module['imports']),'Missing native dependency module'
 assert not any(name in g.collisions for name in module['names']),'Leaf extends an existing collision matrix; unsupported'
 order=[];seen=set()
 for dep in module['imports']:
  for ancestor in g.orders[dep]:
   if ancestor not in seen:seen.add(ancestor);order.append(ancestor)
 assert m not in seen;order.append(m);seen.add(m)
 g.modules[m]=module;g.orders[m]=tuple(order);g.visible[m]=seen
 for row in constants:
  name=row['name'];g.providers[name].append(m);g.records[m,name]=row;g.nodes[m,name]=row
 # Adding providers outside every old context's visibility does not change
 # old resolution results. Missing joint-visible relations stay boundaries.
 for row in constants:
  targets=set()
  for name in set(row['refs']):
   provider,reason=g.resolve(m,name)
   if provider is None:g.unresolved[reason]+=1;continue
   if (provider,name) in g.nodes:targets.add((provider,name))
   else:g.external[provider]+=1
  g.edges[m,row['name']]=targets

def outputs(src,g,local,view):
 paths=runpy.run_path(str(HERE/'native_summary.py'))['module_paths'](src,view)
 areas=[];directories=[];provenance=[];roots=[]
 for m in TARGETS:
  if m not in local:roots.append(dict(context=m,status='build_failed'));continue
  module,constants=local[m]
  try:extend_leaf(g,module,constants)
  except AssertionError as error:roots.append(dict(context=m,status='graph_blocked',reason=str(error)));continue
  used,boundary=g.root_closure(m,['main']);source_used=used & g.nodes.keys();groups=[collections.defaultdict(collections.Counter) for _ in range(3)];line_sets=collections.defaultdict(set)
  for key in source_used:
   path=paths[key[0]];row=g.records[key];labels=['/'.join(path.split('/')[:2]),str(pathlib.PurePosixPath(path).parent),API['provenance'](path,src[path])]
   for group,label in zip(groups,labels):group[label]['source_constants']+=1;group[label]['without_native_source_range']+=int(row['range'] is None)
   if row['range'] is not None:
    a,b,c,d=row['range'];physical=src[path].count('\n')+int(bool(src[path]) and not src[path].endswith('\n'));assert 0<=a<=c<=physical
    line_sets[path].update(range(a+1,c+(1 if d else 0)+1))
  for path,lines in line_sets.items():
   labels=['/'.join(path.split('/')[:2]),str(pathlib.PurePosixPath(path).parent),API['provenance'](path,src[path])]
   assert len(lines)<=src[path].count('\n')+int(not src[path].endswith('\n'))
   for group,label in zip(groups,labels):group[label]['native_range_lines']+=len(lines)
  for target,group in zip((areas,directories,provenance),groups):
   for label,counter in sorted(group.items()):target.append(dict(context=m,group=label,**counter))
  own_used=[r for r in constants if (m,r['name']) in used]
  roots.append(dict(context=m,status='expression_closure_partial' if boundary else 'expression_closure_measured',seed='main',all_loaded_used_bindings=len(used),selected_source_used_bindings=len(source_used),source_native_range_lines=sum(map(len,line_sets.values())),own_serialized_constants=len(constants),own_used_constants=len(own_used),own_outside_expression_closure_constants=len(constants)-len(own_used),boundary=dict(sorted(boundary.items()))))
 return dict(base=API['BASE'],status='partial',roots=roots,provenance=provenance,deletable_now_verified_lines=0,boundaries=['Each global main is resolved in its own cached legacy import context; incompatible CLIs are not imported together.', 'Only Lean module artifacts are compiled; native executable linking and CLI execution are not tested.', 'Counts are native type/value/structural expression closure, not runtime or whole-program liveness.', 'SolidityLean main launches scripts/solidity-lean.mjs via Node; cross-language/generated-check dependencies are outside this graph.', 'Compiler attributes/IR, reflective names, external files and arbitrary inputs require separate treatment.', 'Outside this expression closure does not mean unused or deletable; missing joint-visible collision relations remain explicit boundaries.', 'File provenance flags and missing native ranges are retained; missing ranges are not automatically classified as generated code.']),areas,directories

def render_csv(rows):
 f=io.StringIO();writer=csv.DictWriter(f,fieldnames=['context','group','source_constants','without_native_source_range','native_range_lines'],lineterminator='\n');writer.writeheader()
 for row in rows:writer.writerow({key:row.get(key,0) for key in writer.fieldnames})
 return f.getvalue()

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--out-view',type=pathlib.Path,required=True);p.add_argument('--logs',type=pathlib.Path,required=True);p.add_argument('--base-graph',type=pathlib.Path,required=True);p.add_argument('--graph',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 dependencies=['audit.py','cli_roots.py','LocalExport.lean','module_graph.py','native_summary.py','warm_checks.py'];producers={name:sha(HERE/name) for name in dependencies};src=API['assert_sources'](a.source_root)
 for name in ('source_root','view','out_view','logs','graph','base_graph','out'):setattr(a,name,getattr(a,name).resolve())
 assert a.view.is_dir() and not a.out_view.is_relative_to(a.view),'Output view must be outside input view'
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 config=tomllib.loads(API['git']('show',API['BASE']+':lakefile.toml'));assert set(TARGETS)<={r.get('root',r['name']) for r in config['lean_exe']}
 receipt_path=pathlib.Path(str(a.graph)+'.receipt.json')
 base_receipt=json.loads(pathlib.Path(str(a.base_graph)+'.receipt.json').read_text());base_view=pathlib.Path(base_receipt['reference_view']).resolve()
 for source in base_view.rglob('*'):
  if source.is_file():assert os.path.samefile(source,a.view/source.relative_to(base_view)),'Input view does not share the indexed base artifacts'
 if a.check:
  receipt=json.loads(receipt_path.read_text());assert receipt['producers']==producers and receipt['lean']==version
  assert receipt['input_view']==str(a.view) and receipt['output_view']==str(a.out_view)
  assert receipt['index_sha256']==sha(a.graph) and receipt['base_graph_sha256']==sha(a.base_graph)
  assert [row['module'] for row in receipt['builds']]==TARGETS
  for row in receipt['builds']:
   assert row['status'] in ('pass','fail')
   if row['status']=='pass':assert row['exit_code']==0
   assert row['source_sha256']==sha(a.source_root/(row['module']+'.lean'))
   assert row['command']==WARM['build_command'](a,row['module'])
   if row['status']=='pass':
    for suffix in ('olean','ilean'):assert sha(a.out_view/(row['module']+'.'+suffix))==row[suffix+'_sha256']
   else:assert all(not (a.out_view/(row['module']+suffix)).exists() for suffix in ('.olean','.ilean','.olean.server','.olean.private'))
 else:
  assert not a.out_view.exists() and not a.graph.exists() and not receipt_path.exists(),'Fresh output artifacts required';a.out_view.mkdir(parents=True);a.logs.mkdir(parents=True,exist_ok=True);builds=[]
  for source in sorted(a.view.rglob('*')):
   if source.is_file():target=a.out_view/source.relative_to(a.view);target.parent.mkdir(parents=True,exist_ok=True);os.link(source,target)
  env=dict(os.environ,LEAN_PATH=str(a.out_view),LEAN_NUM_THREADS='1')
  for m in TARGETS:
   assert all(not (a.out_view/(m+suffix)).exists() for suffix in ('.olean','.ilean'))
   command=WARM['build_command'](a,m);started=time.monotonic()
   try:r=subprocess.run(command,cwd=a.source_root,env=env,text=True,capture_output=True,timeout=600);code=r.returncode;log=r.stdout+r.stderr
   except subprocess.TimeoutExpired as error:code=124;log='CLI_BUILD_TIMEOUT600\n'+str(error.stdout or '')+str(error.stderr or '')
   (a.logs/(m+'.log')).write_text(log);status='pass' if code==0 and all((a.out_view/(m+'.'+suffix)).is_file() for suffix in ('olean','ilean')) else 'fail'
   if status=='fail':WARM['quarantine'](a.out_view,a.logs,m)
   assert sha(a.source_root/(m+'.lean'))==hashlib.sha256(src[m+'.lean'].encode()).hexdigest(),'CLI source changed'
   row=dict(module=m,status=status,exit_code=code,command=command,seconds=time.monotonic()-started,source_sha256=sha(a.source_root/(m+'.lean')))
   for suffix in ('olean','ilean'):row[suffix+'_sha256']=sha(a.out_view/(m+'.'+suffix)) if status=='pass' else None
   builds.append(row);print('CLI_BUILD_'+status.upper(),m,flush=True)
  modules=a.logs/'modules.txt';modules.write_text(''.join(row['module']+'\n' for row in builds if row['status']=='pass'))
  command=['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'LocalExport.lean'),str(modules),str(a.graph)]
  r=subprocess.run(command,env=env,text=True,capture_output=True,timeout=600);(a.logs/'export.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
  receipt=dict(producers=producers,lean=version,input_view=str(a.view),output_view=str(a.out_view),builds=builds,index_sha256=sha(a.graph),base_graph_sha256=sha(a.base_graph))
  # Publication waits for complete replay and producer/source checks below.
 for source in a.view.rglob('*'):
  if source.is_file():assert os.path.samefile(source,a.out_view/source.relative_to(a.view)),'Input view link changed'
 for row in receipt['builds']:
  if row['status']=='pass':assert json.loads((a.out_view/(row['module']+'.ilean')).read_text())['module']==row['module']
 local={}
 for line in a.graph.open():
  row=json.loads(line);m=row['module'];assert m in TARGETS
  if row['record']=='module':assert m not in local;local[m]=(row,[])
  else:assert row['record']=='constant';local[m][1].append(row)
 assert set(local)=={row['module'] for row in receipt['builds'] if row['status']=='pass'}
 graph=NATIVE['load'](a.base_graph);summary,areas,directories=outputs(src,graph,local,a.out_view)
 summary.update(local_graph_sha256=sha(a.graph),base_graph_sha256=sha(a.base_graph),build_status={row['module']:row['status'] for row in receipt['builds']})
 assert producers=={name:sha(HERE/name) for name in dependencies},'Producer changed';API['assert_sources'](a.source_root)
 for name,body in [('cli-root-summary.json',json.dumps(summary,indent=2,sort_keys=True)+'\n'),('cli-root-areas.csv',render_csv(areas)),('cli-root-directories.csv',render_csv(directories))]:
  assert len(body.encode())<1000000
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 if not a.check:receipt_path.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print('CLI_ROOT_EXPRESSION_PASS',[(row['context'],row.get('selected_source_used_bindings')) for row in summary['roots']])
if __name__=='__main__':main()
