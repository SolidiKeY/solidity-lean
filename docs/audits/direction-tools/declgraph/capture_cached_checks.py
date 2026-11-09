#!/usr/bin/env python3
"""Durable serial warm-cache root-capture queue, reusing19dense observations.
Each Lean capture holds the repository writer lock. Failed files are retained
and skipped; integrity failures are hard errors. No full library rebuild runs.
"""
import argparse,hashlib,json,os,pathlib,runpy,signal,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha']
LOCK='/tmp/solidity-lean-feature-groups-20261025/writer.lock'

def selection():
 census=json.loads((HERE/'source-check-syntax.json').read_text());dense=json.loads((HERE/'snapshot-root-summary.json').read_text())
 reused={r['path'] for r in dense['files'] if r['status']=='observed'}
 eligible={r['path'] for r in census if r['cached']}
 assert reused<=eligible
 return sorted(eligible-reused),sorted(reused),sorted({r['path'] for r in census}-eligible)

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--limit',type=int);p.add_argument('--check',action='store_true');a=p.parse_args()
 for k in ('source_root','view','captures','out'):setattr(a,k,getattr(a,k).resolve())
 API['assert_sources'](a.source_root);queue,reused,uncached=selection();assert a.limit is None or a.limit>0
 if a.limit is not None:queue=queue[:a.limit]
 names=('capture_cached_checks.py','capture_compact.py','CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','source-check-syntax.json','snapshot-root-summary.json');producers={n:SHA(HERE/n) for n in names}
 if not a.check:a.captures.mkdir(parents=True,exist_ok=True)
 files=[];resource_wait=None
 for index,path in enumerate(queue):
  stem=hashlib.sha256(path.encode()).hexdigest()[:20];directory=a.captures/stem;status_file=a.captures/(stem+'.status.json');summary=a.captures/(stem+'.summary.json');log=a.captures/(stem+'.driver.log')
  cmd=['flock',LOCK,'python3','-I',str(HERE/'capture_compact.py'),'--source-root',str(a.source_root),'--view',str(a.view),'--capture',str(directory),'--file',path,'--out',str(summary)]
  fixed=dict(path=path,command=cmd,source_sha256=SHA(a.source_root/path),producers=producers)
  if status_file.exists():
   status=json.loads(status_file.read_text());assert all(status[k]==v for k,v in fixed.items()),'Queue/input drift'
   assert status['log_sha256']==SHA(log)
  else:
   assert not a.check,'Missing queue status: '+path
   stats=os.statvfs(a.captures);free=stats.f_bavail*stats.f_frsize
   if free<5*1024**3:resource_wait='VM disk free below5GiB; no new capture started';break
   assert not directory.exists() and not summary.exists(),'Unfinished capture requires explicit recovery: '+path
   with log.open('w') as output:
    proc=subprocess.Popen(cmd,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
    try:code=proc.wait(timeout=660)
    except subprocess.TimeoutExpired:
     os.killpg(proc.pid,signal.SIGTERM)
     try:proc.wait(timeout=5)
     except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
     code=124
    finally:
     # Only descendants of this owned session can remain in this group.
     try:os.killpg(proc.pid,signal.SIGTERM)
     except ProcessLookupError:pass
   status=dict(fixed,exit_code=code,log_sha256=SHA(log),summary_sha256=SHA(summary) if summary.exists() else None)
   status_file.write_text(json.dumps(status,sort_keys=True)+'\n')
  row=dict(path=path,status='unavailable',exit_code=status['exit_code'])
  if status['exit_code']==0:
   assert status['summary_sha256']==SHA(summary)
   data=json.loads(summary.read_text());assert data['base']==API['BASE'] and data['metrics']['path']==path
   meta=json.loads((directory/'receipt.json').read_text());assert meta['exit_code']==0 and meta['source_sha256']==fixed['source_sha256']
   expected={n:producers[n] for n in ('CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','capture_compact.py')};assert meta['producers']==expected
   assert pathlib.Path(meta['view'])==a.view
   for n in ('roots.jsonl','capture.log'):assert meta['outputs'][n]==SHA(directory/n)
   row.update(status='observed',metrics=data['metrics'],encoding=data['encoding'])
  else:
   text=log.read_text(errors='replace');row['failure_class']='timeout' if status['exit_code']==124 else 'capture_failed'
  files.append(row)
  if not a.check:print(index+1,len(queue),row['status'],path,flush=True)
  # Durable progress is evidence on the VM, not a code-branch result.
  if not a.check:(a.captures/'progress.json').write_text(json.dumps(dict(processed=len(files),planned=len(queue),observed=sum(r['status']=='observed' for r in files),last=path),sort_keys=True)+'\n')
 assert producers=={n:SHA(HERE/n) for n in names};API['assert_sources'](a.source_root)
 result=dict(base=API['BASE'],status='partial',planned_files=len(queue),processed_files=len(files),observed_files=sum(r['status']=='observed' for r in files),reused_dense_files=reused,uncached_syntax_files=uncached,resource_wait=resource_wait,files=files,deletable_now_verified_lines=0,boundaries=['Selection is cached files with explicit native syntax-census checks; macro-only and uncached files remain outside this queue.','A successful source capture is observational; complete check roots, reflection, symbolic lookups and compiler/runtime dependencies are not certified.','Existing19dense files are reused rather than re-elaborated.','Failures contribute no observed metric counts; source/provenance integrity failures stop the queue.'])
 body=json.dumps(result,sort_keys=True,indent=2)+'\n';assert len(body.encode())<1000000
 if a.check:assert a.out.read_text()==body,'STALE queue summary'
 else:a.out.write_text(body)
 print('CACHED_CHECK_QUEUE_PASS',len(files),len(queue),result['observed_files'])
if __name__=='__main__':main()
