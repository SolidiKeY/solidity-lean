#!/usr/bin/env python3
"""Capture actual saved-environment check CI dependencies in19selected files.
Root coverage is observational. Original cache bytes are externally trusted.
Use external writer lock and serial pinned Lean; --check validates existing data.
"""
import argparse,collections,csv,hashlib,io,json,os,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha']
FAMILIES=('Yul/Views','Backend/InternalFlow','SolcValidation','Frontend/SolcJson')
def keyhash(key):
 assert key is not None
 return hashlib.sha256(json.dumps(key,separators=(',',':'),ensure_ascii=True).encode()).hexdigest()

def merge_tables(imported,stage2,im,st):
 # Check both tables before publishing either: rejected files contribute nothing.
 assert all(k not in imported or imported[k]==v for k,v in im.items())
 assert all(k not in stage2 or stage2[k]==v for k,v in st.items())
 imported.update(im);stage2.update(st)

def measure(raw,log,path):
 counts=collections.Counter();commands=[];check_ids=set();root_ids=set();snapshots=[];imported={};stage2={};ambiguous=0;root_names=set();root_records=[];binding_records=[];all_command_ids=[]
 for line in raw.open():
  r=json.loads(line);kind=r['record'];counts[kind]+=1;all_command_ids.append(r['command'])
  assert kind in {'command','check_event','root_event','binding','snapshot_summary','missing_parent'}
  if kind=='command':commands.append(r)
  elif kind=='check_event':check_ids.add(r['command'])
  elif kind=='root_event':root_ids.add(r['command']);root_names.add((r['command'],keyhash(r['name_key'])));root_records.append((r['command'],r['snapshot'],keyhash(r['name_key']),r['constant_kind']))
  elif kind=='snapshot_summary':snapshots.append(r)
  elif kind=='binding':
   kh=keyhash(r['name_key']);binding_records.append((r['command'],r['snapshot'],kh,r['constant_kind'],r['is_root']));modules=r['imported_pointer_modules'];assert len(modules)==len(set(modules))
   for ref in r['refs']:keyhash(ref['name_key'])
   if len(modules)==1:
    value=(modules[0],r['name'],kh,r['constant_kind']);key=(modules[0],kh)
    if key in imported:assert imported[key]==value
    imported[key]=value
   elif len(modules)>1:ambiguous+=1
   if r['in_stage2']:
    rng=json.dumps(r['own_range'],separators=(',',':'));key=(path,kh,rng);v=stage2.setdefault(key,[path,r['name'],kh,rng,r['constant_kind'],0,0]);assert v[:5]==[path,r['name'],kh,rng,r['constant_kind']];v[5 if r['is_root'] else 6]=1
 assert [r['command'] for r in commands]==list(range(len(commands)))
 assert all(isinstance(cmd,int) and 0<=cmd<len(commands) for cmd in all_command_ids)
 snapshot_index={(r['command'],r['snapshot']):r for r in snapshots};assert len(snapshot_index)==len(snapshots)
 actual_bindings=collections.Counter();binding_keys=set();root_bindings=collections.defaultdict(dict);event_roots=collections.defaultdict(dict)
 for cmd,snap,kh,kind,is_root in binding_records:
  key=(cmd,snap);assert key in snapshot_index and (cmd,snap,kh) not in binding_keys
  binding_keys.add((cmd,snap,kh));actual_bindings[key]+=1
  if is_root:root_bindings[key][kh]=kind
 for cmd,snap,kh,kind in root_records:
  key=(cmd,snap);assert key in snapshot_index
  if kh in event_roots[key]:assert event_roots[key][kh]==kind
  event_roots[key][kh]=kind
 for key,snap in snapshot_index.items():
  expected={keyhash(n) for n in snap['root_names']};assert expected and len(expected)==len(snap['root_names'])
  assert actual_bindings[key]==snap['emitted_bindings']
  assert set(root_bindings[key])==expected and root_bindings[key]==event_roots[key]
  missing={keyhash(n) for n in snap['missing_names']};assert len(missing)==len(snap['missing_names'])
  assert snap['visited_names']>=snap['emitted_bindings']+len(missing)

 marker=re.findall(r'SNAPSHOT_ROOTS_PASS (\d+) (\d+) (\d+) (\d+) (\d+)',log.read_text());assert len(marker)==1
 assert tuple(map(int,marker[0]))==tuple(counts[k] for k in ('command','check_event','root_event','snapshot_summary','binding'))
 assert root_ids<=check_ids and all(r['command'] in check_ids for r in snapshots)
 assert sum(r['emitted_bindings'] for r in snapshots)==counts['binding']
 assert sum(r['missing_parent_events'] for r in commands)==counts['missing_parent']
 data=dict(path=path,counts=dict(sorted(counts.items())),observed_check_commands=len(check_ids),covered_check_commands=len(root_ids),uncovered_check_command_ids=sorted(check_ids-root_ids),root_name_command_observations=len(root_names),imported_pointer_binding_units=len(imported),stage2_name_range_units=len(stage2),ambiguous_import_binding_events=ambiguous,missing_native_constant_events=sum(len(r['missing_names']) for r in snapshots),unresolved_import_origin_events=sum(r['unresolved_import_origins'] for r in snapshots),active_nodes_without_parent=sum(r['active_nodes_without_parent'] for r in commands))
 return data,imported,stage2

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);modes=p.add_mutually_exclusive_group();modes.add_argument('--check',action='store_true');modes.add_argument('--replay',action='store_true');p.add_argument('--capture-driver-commit');a=p.parse_args()
 for key in ('source_root','view','captures','out'):setattr(a,key,getattr(a,key).resolve())
 API['assert_sources'](a.source_root);gr=HERE.parents[3]/'.lake/refactor-cache/declgraph-module-native.jsonl.receipt.json';graph_receipt=json.loads(gr.read_text());assert pathlib.Path(graph_receipt['reference_view']).resolve()==a.view;assert graph_receipt['modules_sha256']==SHA(HERE/'modules.txt')
 producers={n:SHA(HERE/n) for n in ('SnapshotRoots.lean','run_snapshot_roots.py','audit.py','modules.txt','source-check-syntax.json')};version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 paths=sorted({r['path'] for r in json.loads((HERE/'source-check-syntax.json').read_text()) if any(r['path'].startswith('Solidity/'+f+'/') for f in FAMILIES)})
 receipt_producers=dict(producers)
 if a.capture_driver_commit:
  assert a.check or a.replay,'Historical driver only applies to validated replay'
  assert re.fullmatch('[0-9a-f]{40}',a.capture_driver_commit)
  root=HERE.parents[3];subprocess.run(['git','merge-base','--is-ancestor',a.capture_driver_commit,'HEAD'],cwd=root,check=True)
  blob=subprocess.check_output(['git','show',a.capture_driver_commit+':docs/audits/direction-tools/declgraph/run_snapshot_roots.py'],cwd=root)
  receipt_producers['run_snapshot_roots.py']=hashlib.sha256(blob).hexdigest()
 if not (a.check or a.replay):assert not a.captures.exists();a.captures.mkdir(parents=True)
 files=[];imported={};stage2={}
 for path in paths:
  module=path[:-5].replace('/','.');source=a.source_root/path;raw=a.captures/(module+'.jsonl');log=a.captures/(module+'.log');receipt=a.captures/(module+'.receipt.json');cmd=['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'SnapshotRoots.lean'),str(source),module,str(HERE/'modules.txt'),str(raw)];fixed=dict(producers=receipt_producers,lean=version,view=str(a.view),graph_receipt_sha256=SHA(gr),source_sha256=SHA(source),command=cmd)
  if a.check or a.replay:
   meta=json.loads(receipt.read_text());assert all(meta[k]==v for k,v in fixed.items());assert meta['log_sha256']==SHA(log) and meta['raw_sha256']==(SHA(raw) if raw.exists() else None)
  else:
   try:
    x=subprocess.run(cmd,env=dict(os.environ,LEAN_PATH=str(a.view),LEAN_NUM_THREADS='1'),text=True,capture_output=True,timeout=600);log.write_text(x.stdout+x.stderr);code=x.returncode
   except subprocess.TimeoutExpired as exc:log.write_text('TIMEOUT600\n'+str(exc.stdout or '')+str(exc.stderr or ''));code=124
   meta=dict(fixed,exit_code=code,log_sha256=SHA(log),raw_sha256=SHA(raw) if raw.exists() else None);receipt.write_text(json.dumps(meta,sort_keys=True)+'\n')
  data=dict(path=path,status='unavailable',exit_code=meta['exit_code'])
  if meta['exit_code']==0:
   try:
    metrics,im,st=measure(raw,log,path)
    merge_tables(imported,stage2,im,st)
    data.update(metrics,status='observed')
   except (AssertionError,ValueError,KeyError,TypeError,FileNotFoundError) as exc:data.update(status='validation_failed',validation_error=type(exc).__name__+': '+str(exc))
  files.append(data);print(data['status'],path,flush=True)
 summary=dict(base=API['BASE'],status='partial',files=files,imported_pointer_binding_units=len(imported),stage2_name_range_units=len(stage2),deletable_now_verified_lines=0,verdict='Saved native check environments provide positive type/value dependency observations with imported CI origins. Root completeness and global liveness remain uncertified.',boundaries=['Actual native parent-declaration metadata under check commands selects observed root CIs; uncovered commands and missing parent bindings remain explicit.','CI type/value/structural refs are traversed in each saved environment, not the final compiled module context.','Positive object-pointer identity binds imported CIs to ModuleData versions; unresolved or multiple origins are not unique source attribution.','Stage2 membership and elaborating-module hints do not prove creation origin. Native own ranges are current-module extension metadata.','Root/snapshot repetitions are observations; no count is a unique successful root theorem census.','This covers19 syntax-selected family files, not all macro, CI, symbolic-name-existence, compiler-attribute or runtime dependencies.','Historical capture-driver replay verifies its exact Git blob and ancestry; current native producer/inputs/commands and raw/log hashes must still match.', 'The prepared original artifact view is externally trusted; receipts bind source, producers, manifest, graph receipt, raw captures and logs.'])
 outputs={'snapshot-root-summary.json':json.dumps(summary,sort_keys=True,indent=2)+'\n'}
 for name,header,rows in [('snapshot-imported-bindings.tsv',['module','name','name_key_sha256','constant_kind'],imported.values()),('snapshot-stage2-bindings.tsv',['path','name','name_key_sha256','own_range','constant_kind','seen_as_root','seen_as_dependency'],stage2.values())]:
  f=io.StringIO();w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(header);w.writerows(sorted(rows));outputs[name]=f.getvalue()
 assert producers=={n:SHA(HERE/n) for n in producers};API['assert_sources'](a.source_root)
 for name,body in outputs.items():
  assert len(body.encode())<1000000,'Split oversized result data before publishing'
  if a.check:assert (a.out/name).read_text()==body,'STALE '+name
  else:(a.out/name).write_text(body)
 print('SNAPSHOT_ROOT_BATCH_PASS',sum(f['status']=='observed' for f in files),len(files),len(imported),len(stage2))
if __name__=='__main__':main()
