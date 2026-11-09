#!/usr/bin/env python3
"""Receipt-bound replay of cached-check observations; no Lean elaboration.
Imported pointer witnesses and stage2 correspondences remain separate. A prefix
is accepted only explicitly; no absence, root completeness or deletion follows.
Run under the shared writer lease: replay and capture are never heavy together.
"""
import argparse,collections,csv,hashlib,io,json,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
Q=runpy.run_path(str(HERE/'capture_cached_checks.py'));C=runpy.run_path(str(HERE/'compact_records.py'))
L=C['LEGACY'];API=Q['API'];SHA=Q['SHA'];NS=runpy.run_path(str(HERE/'native_summary.py'))

def manifest(data,*,allow_prefix=False):
 queue,reused,uncached=Q['selection']();files=data['files'];paths=[r['path'] for r in files]
 assert data['base']==API['BASE'] and paths==queue[:len(paths)] and len(paths)==len(set(paths))
 assert data['reused_dense_files']==reused and data['uncached_syntax_files']==uncached
 assert data['processed_files']==len(files) and len(files)<=data['planned_files']<=len(queue)
 assert data['observed_files']==sum(r['status']=='observed' for r in files)
 assert allow_prefix or len(files)==data['planned_files']==len(queue),'Incomplete corpus requires --allow-prefix'
 assert data['planned_files'] in (len(queue),len(files)),'Invalid prefix plan'
 for r in files:
  assert r['status'] in ('observed','unavailable')
  assert (r['exit_code']==0)==(r['status']=='observed')
  if r['status']=='observed':assert r['metrics']['path']==r['path']
  else:assert 'metrics' not in r and 'encoding' not in r
 return files,reused,uncached

def tabular(header,rows):
 out=io.StringIO();w=csv.writer(out,delimiter='\t',lineterminator='\n');w.writerow(header);w.writerows(rows);return out.getvalue()

def shards(prefix,header,items,*,limit=999999):
 # Sharding is by the complete native-unit key, never by printed names alone.
 items=sorted(items.items());count=16
 while True:
  buckets=collections.defaultdict(list)
  for key,value in items:
   digest=hashlib.sha256(json.dumps(key,separators=(',',':')).encode()).digest()
   buckets[int.from_bytes(digest[:4],'big')%count].append(value)
  outputs={f'{prefix}-{i:04x}.tsv':tabular(header,rows) for i,rows in sorted(buckets.items())}
  if all(len(body.encode())<limit for body in outputs.values()):return outputs
  count*=2;assert count<=65536,'A result row cannot fit the configured small-file limit'

def add_file(imported,stage2,metrics,im,st,expected):
 assert metrics==expected['metrics'] and expected['status']=='observed','Decoded metric drift'
 L['merge_tables'](imported,stage2,im,st)

def source_paths(src,view,inputs):
 paths=NS['module_paths'](src,view)
 for module,path in paths.items():
  f=view/pathlib.Path(path.removeprefix('vendor/LeanTeX/').removeprefix('Bridge/')).with_suffix('.ilean')
  inputs[str(f)]=SHA(f)
 return paths

def unit_provenance(imported,stage2,paths,src):
 im=collections.Counter();st=collections.Counter()
 for module,name,key,kind in imported.values():
  path=paths[module];im[API['provenance'](path,src[path])]+=1
 for row in stage2.values():
  path=row[0];st[API['provenance'](path,src[path])]+=1
 return dict(sorted(im.items())),dict(sorted(st.items()))

def check_output_set(out,outputs):
 existing={x.name for pattern in ('imported-*.tsv','stage2-*.tsv','summary.json') for x in out.glob(pattern)}
 assert existing==set(outputs),'Stale/missing replay output set'
 assert all((out/n).read_text()==body for n,body in outputs.items()),'Stale replay tables'

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--queue-summary',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--evidence',type=pathlib.Path,required=True);p.add_argument('--prior-runner-commit',action='append',default=[]);p.add_argument('--allow-prefix',action='store_true');p.add_argument('--check',action='store_true');a=p.parse_args()
 for k in ('source_root','view','captures','queue_summary','out','evidence'):setattr(a,k,getattr(a,k).resolve())
 with Q['writer_lease']():
  src=API['assert_sources'](a.source_root);data=json.loads(a.queue_summary.read_text());files,reused,uncached=manifest(data,allow_prefix=a.allow_prefix)
  names=('replay_cached_checks.py','capture_cached_checks.py','capture_compact.py','CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','module_graph.py','native_summary.py','modules.txt','source-check-syntax.json','snapshot-root-summary.json')
  producers={n:SHA(HERE/n) for n in names};inputs={str(a.queue_summary):SHA(a.queue_summary)}
  gr=HERE.parents[3]/'.lake/refactor-cache/declgraph-module-native.jsonl.receipt.json';graph_sha=SHA(gr);inputs[str(gr)]=graph_sha;graph=json.loads(gr.read_text())
  assert pathlib.Path(graph['reference_view']).resolve()==a.view and graph['modules_sha256']==producers['modules.txt']
  paths=source_paths(src,a.view,inputs);assert set(paths)==set((HERE/'modules.txt').read_text().splitlines())
  allowed={producers['capture_cached_checks.py']}
  for commit in a.prior_runner_commit:
   assert re.fullmatch('[0-9a-f]{40}',commit)
   subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=HERE.parents[3],check=True)
   blob=subprocess.check_output(['git','show',commit+':docs/audits/direction-tools/declgraph/capture_cached_checks.py'],cwd=HERE.parents[3]);allowed.add(hashlib.sha256(blob).hexdigest())
  version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
  imported={};stage2={};counts=collections.Counter();flags=collections.Counter();uncovered=[];failed=[];per_directory=collections.defaultdict(collections.Counter)
  for row in files:
   path=row['path'];stem=hashlib.sha256(path.encode()).hexdigest()[:20];directory=a.captures/stem;status_file=a.captures/(stem+'.status.json');summary=a.captures/(stem+'.summary.json');log=a.captures/(stem+'.driver.log')
   status=json.loads(status_file.read_text());inputs[str(status_file)]=SHA(status_file);inputs[str(log)]=SHA(log)
   cmd=['python3','-I',str(HERE/'capture_compact.py'),'--source-root',str(a.source_root),'--view',str(a.view),'--capture',str(directory),'--file',path,'--out',str(summary)]
   # Queue statuses bind this nine-file producer set, not the replay producer.
   qnames=('capture_cached_checks.py','capture_compact.py','CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','source-check-syntax.json','snapshot-root-summary.json')
   fixed=dict(path=path,command=cmd,source_sha256=SHA(a.source_root/path),producers={n:producers[n] for n in qnames})
   Q['validate_status'](status,fixed,allowed);assert status['log_sha256']==inputs[str(log)] and status['exit_code']==row['exit_code']
   area=per_directory[str(pathlib.PurePosixPath(path).parent)];area['selected_files']+=1
   if row['status']=='unavailable':failed.append(dict(path=path,exit_code=row['exit_code']));area['unavailable_files']+=1;continue
   meta=Q['validate_capture'](directory,a.source_root/path,path,a.view,version,graph_sha,producers)
   inputs[str(directory/'receipt.json')]=SHA(directory/'receipt.json');assert status['receipt_sha256']==inputs[str(directory/'receipt.json')]
   inputs[str(summary)]=SHA(summary);assert status['summary_sha256']==inputs[str(summary)]
   recorded=json.loads(summary.read_text());assert recorded['base']==API['BASE'] and recorded['metrics']==row['metrics'] and recorded['encoding']==row['encoding']
   for n in ('roots.jsonl','capture.log'):inputs[str(directory/n)]=meta['outputs'][n]
   (metrics,im,st),encoding=C['measure'](directory/'roots.jsonl',directory/'capture.log',path)
   assert encoding==row['encoding'];add_file(imported,stage2,metrics,im,st,row)
   counts.update(metrics['counts']);area['observed_files']+=1
   for key in ('observed_check_commands','covered_check_commands','ambiguous_import_binding_events','missing_native_constant_events','unresolved_import_origin_events','active_nodes_without_parent'):
    flags[key]+=metrics[key];area[key]+=metrics[key]
   if metrics['uncovered_check_command_ids']:uncovered.append(dict(path=path,ids=metrics['uncovered_check_command_ids']))
  provenance,stage2_provenance=unit_provenance(imported,stage2,paths,src)
  outputs=shards('imported',['module','name','name_key_sha256','constant_kind'],imported)
  outputs.update(shards('stage2',['path','name','name_key_sha256','own_range','constant_kind','seen_as_root','seen_as_dependency'],stage2))
  result=dict(base=API['BASE'],status='partial',selected_files=len(files),observed_files=len(files)-len(failed),unavailable_files=failed,full_queue_files=len(Q['selection']()[0]),reused_dense_files_not_replayed_here=reused,uncached_explicit_check_files=uncached,event_counts=dict(sorted(counts.items())),observation_flags=dict(sorted(flags.items())),uncovered_check_commands=uncovered,imported_pointer_binding_units=len(imported),stage2_name_range_units=len(stage2),imported_unit_provenance=provenance,stage2_unit_provenance=stage2_provenance,directories={k:dict(sorted(v.items())) for k,v in sorted(per_directory.items())},tables=sorted(outputs),deletable_now_verified_lines=0,boundaries=['This combines only the selected additional cached captures; the19earlier dense files remain separate.','Native structural-name hashes identify units; root/snapshot repetitions remain observation events, not unique successful theorem counts.','Imported pointer witnesses and stage2 name/range correspondences stay separate; stage2 membership does not prove source creation origin.','Unobserved declarations are never classified unused; macro-only, uncached, reflective, symbolic-name, CI and runtime roots remain incomplete.','Provenance labels classify pinned source paths/markers; untraced and unresolved chain/agreement code is not certified handwritten.','Output files are replaced individually; interruption can leave unvalidated output. Rerun --check, or regenerate on failure, before using results.','Cached bytes are externally trusted; source, producers, commands, toolchain and input/output digests are validated under the writer lease.'])
  outputs['summary.json']=json.dumps(result,sort_keys=True,indent=2)+'\n';assert all(len(x.encode())<1000000 for x in outputs.values())
  assert producers=={n:SHA(HERE/n) for n in names};assert all(SHA(pathlib.Path(p))==h for p,h in inputs.items());API['assert_sources'](a.source_root)
  receipt=dict(base=API['BASE'],producers=producers,inputs=inputs,outputs={n:hashlib.sha256(body.encode()).hexdigest() for n,body in outputs.items()},lean=version,queue_summary=str(a.queue_summary))
  existing={x.name for pattern in ('imported-*.tsv','stage2-*.tsv','summary.json') for x in a.out.glob(pattern)}
  if a.check:
   check_output_set(a.out,outputs)
   assert json.loads(a.evidence.read_text())==receipt,'Replay evidence drift'
  else:
   a.out.mkdir(parents=True,exist_ok=True)
   for n in sorted(existing-set(outputs)):(a.out/n).unlink()
   for n,body in sorted(outputs.items(),key=lambda kv:kv[0]=='summary.json'):Q['atomic_text'](a.out/n,body)
   Q['atomic_json'](a.evidence,receipt)
  print('CACHED_REPLAY_PASS',len(files),len(files)-len(failed),len(imported),len(stage2))
if __name__=='__main__':main()
