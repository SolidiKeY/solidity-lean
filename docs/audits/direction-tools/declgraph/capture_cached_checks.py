#!/usr/bin/env python3
"""Durable serial warm-cache root-capture queue, reusing19dense observations.
Each Lean capture holds the repository writer lock. Failed files are retained
and skipped; integrity failures are hard errors. No full library rebuild runs.
"""
import argparse,contextlib,fcntl,hashlib,json,os,pathlib,re,runpy,signal,subprocess,time,tempfile
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha']
LOCK='/tmp/solidity-lean-feature-groups-20261025/writer.lock'

def atomic_text(path,body):
 path.parent.mkdir(parents=True,exist_ok=True)
 with tempfile.NamedTemporaryFile(mode='w',dir=path.parent,prefix=path.name+'.tmp-',delete=False) as f:
  f.write(body);f.flush();os.fsync(f.fileno());name=f.name
 os.replace(name,path)

def atomic_json(path,data):atomic_text(path,json.dumps(data,sort_keys=True)+'\n')

@contextlib.contextmanager
def writer_lease(lock_path=LOCK):
 with open(lock_path,'a') as lease:
  fcntl.flock(lease,fcntl.LOCK_EX)
  yield lease

@contextlib.contextmanager
def capture_transaction(directory,*,lock_path=LOCK):
 # A surviving child may finish its receipt while the next owner waits.
 # Inspect recovery state only after acquiring the lease, and retain it through
 # recovery, capture, validation and status publication.
 with writer_lease(lock_path) as lease:
  yield lease,(directory/'receipt.json').exists()

def publish_summary(path,body,*,guard,check=False,lock_path=LOCK):
 with writer_lease(lock_path):
  guard()
  if check:assert path.read_text()==body,'STALE queue summary'
  else:atomic_text(path,body)

def timed_capture(cmd,output,*,lock_path=LOCK,timeout=660,lease=None):
 # Lock contention is scheduling, not capture runtime. No child or timer exists
 # until this process owns the writer lease. Cancellation leaves no status.
 with (contextlib.nullcontext(lease) if lease is not None else writer_lease(lock_path)) as lease:
  proc=subprocess.Popen(cmd,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(lease.fileno(),))
  try:
   try:return proc.wait(timeout=timeout)
   except subprocess.TimeoutExpired:
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:proc.wait(timeout=5)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    return 124
  finally:
   # Drain the owned group even if its immediate wrapper exited on TERM.
   try:os.killpg(proc.pid,signal.SIGKILL)
   except ProcessLookupError:pass
   proc.wait()

def validate_status(status,fixed,allowed_runner):
 assert all(status[k]==fixed[k] for k in ('path','source_sha256')),'Queue/input drift'
 prior=dict(status['producers']);runner=prior.pop('capture_cached_checks.py');assert runner in allowed_runner
 current=dict(fixed['producers']);current_runner=current.pop('capture_cached_checks.py');assert prior==current
 assert runner==current_runner or status['exit_code']!=124,'Legacy timeout may be an unstarted lock wait; explicit recovery required'
 # Only an explicitly supplied exact ancestor blob may have the old wrapper.
 assert status['command']==fixed['command'] or (runner!=current_runner and status['command']==['flock',LOCK]+fixed['command']),'Queue command drift'

def validate_capture(directory,source,path,view,version,graph_sha,producers):
 meta=json.loads((directory/'receipt.json').read_text())
 module=json.loads((view/pathlib.Path(path).with_suffix('.ilean')).read_text())['module']
 expected={n:producers[n] for n in ('CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','capture_compact.py')}
 native=['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'CompactRoots.lean'),str(source),module,str(HERE/'modules.txt'),str(directory/'roots.jsonl')]
 assert meta['producers']==expected and meta['command']==native and meta['lean']==version and meta['module']==module
 assert meta['source_sha256']==SHA(source) and meta['view']==str(view) and meta['graph_receipt_sha256']==graph_sha and meta['exit_code']==0
 for n in ('roots.jsonl','capture.log'):assert meta['outputs'][n]==SHA(directory/n)
 return meta

def selection():
 census=json.loads((HERE/'source-check-syntax.json').read_text());dense=json.loads((HERE/'snapshot-root-summary.json').read_text())
 reused={r['path'] for r in dense['files'] if r['status']=='observed'}
 eligible={r['path'] for r in census if r['cached']}
 assert reused<=eligible
 return sorted(eligible-reused),sorted(reused),sorted({r['path'] for r in census}-eligible)

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--limit',type=int);p.add_argument('--check',action='store_true');p.add_argument('--prior-runner-commit',action='append',default=[]);p.add_argument('--recover-interrupted',action='store_true');a=p.parse_args()
 for k in ('source_root','view','captures','out'):setattr(a,k,getattr(a,k).resolve())
 API['assert_sources'](a.source_root);queue,reused,uncached=selection();assert a.limit is None or a.limit>0
 if a.limit is not None:queue=queue[:a.limit]
 names=('capture_cached_checks.py','capture_compact.py','CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','source-check-syntax.json','snapshot-root-summary.json');producers={n:SHA(HERE/n) for n in names}
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 graph_file=HERE.parents[3]/'.lake/refactor-cache/declgraph-module-native.jsonl.receipt.json';graph_sha=SHA(graph_file)
 graph=json.loads(graph_file.read_text());assert pathlib.Path(graph['reference_view']).resolve()==a.view and graph['modules_sha256']==producers['modules.txt']
 allowed_runner={producers['capture_cached_checks.py']}
 for prior_commit in a.prior_runner_commit:
  assert re.fullmatch('[0-9a-f]{40}',prior_commit)
  subprocess.run(['git','merge-base','--is-ancestor',prior_commit,'HEAD'],cwd=HERE.parents[3],check=True)
  blob=subprocess.check_output(['git','show',prior_commit+':docs/audits/direction-tools/declgraph/capture_cached_checks.py'],cwd=HERE.parents[3]);allowed_runner.add(hashlib.sha256(blob).hexdigest())
 def integrity(path):
  assert producers=={n:SHA(HERE/n) for n in names},'Producer drift'
  assert SHA(graph_file)==graph_sha,'Graph receipt drift'
  assert SHA(a.source_root/path)==hashlib.sha256(API['sources']()[path].encode()).hexdigest(),'Source drift'
 if not a.check:
  with writer_lease():a.captures.mkdir(parents=True,exist_ok=True)
 files=[];resource_wait=None
 for index,path in enumerate(queue):
  stem=hashlib.sha256(path.encode()).hexdigest()[:20];directory=a.captures/stem;status_file=a.captures/(stem+'.status.json');summary=a.captures/(stem+'.summary.json');log=a.captures/(stem+'.driver.log')
  with capture_transaction(directory) as (lease,recovered):
   cmd=['python3','-I',str(HERE/'capture_compact.py'),'--source-root',str(a.source_root),'--view',str(a.view),'--capture',str(directory),'--file',path,'--out',str(summary)]
   fixed=dict(path=path,command=cmd,source_sha256=SHA(a.source_root/path),producers=producers)
   integrity(path)
   if status_file.exists():
    status=json.loads(status_file.read_text());validate_status(status,fixed,allowed_runner)
    assert status['log_sha256']==SHA(log)
   else:
    assert not a.check,'Missing queue status: '+path
    stats=os.statvfs(a.captures);free=stats.f_bavail*stats.f_frsize
    if free<5*1024**3:resource_wait='VM disk free below5GiB; no new capture started';break
    if recovered:
     assert a.recover_interrupted,'Complete receipt without status requires explicit recovery'
     validate_capture(directory,a.source_root/path,path,a.view,version,graph_sha,producers)
     compact=runpy.run_path(str(HERE/'compact_records.py'))
     (metrics,imports,stage2),encoding=compact['measure'](directory/'roots.jsonl',directory/'capture.log',path)
     data=dict(base=API['BASE'],status='partial',metrics=metrics,encoding=encoding,boundary='Actual saved-environment CI observations for this source only; compact pooling preserves every binding observation, not full root completeness or global liveness.')
     body=json.dumps(data,sort_keys=True,indent=2)+'\n'
     if summary.exists():assert summary.read_text()==body,'Interrupted summary drift'
     else:
      temporary=pathlib.Path(str(summary)+'.tmp');temporary.write_text(body);os.replace(temporary,summary)
     if not log.exists():log.write_text('RECOVERED_VALIDATED_NATIVE_RECEIPT\n')
     status=dict(fixed,exit_code=0,log_sha256=SHA(log),summary_sha256=SHA(summary),receipt_sha256=SHA(directory/'receipt.json'))
     atomic_json(status_file,status)
    else:
     if directory.exists() or summary.exists():
      assert a.recover_interrupted,'Unfinished capture requires explicit recovery: '+path
      suffix='.interrupted-'+str(time.time_ns())
      for item in (directory,summary,log):
       if item.exists():item.rename(pathlib.Path(str(item)+suffix))
     with log.open('w') as output:
      code=timed_capture(cmd,output,lease=lease)
     integrity(path)
     if code!=0:
      API['assert_sources'](a.source_root)
      text=log.read_text(errors='replace')
      ordinary=(code==124 or 'Compact capture failed; no measurement published' in text or 'subprocess.TimeoutExpired' in text)
      assert ordinary,'Child integrity/validation failure: '+path+'; '+str(log)
     receipt_sha=None
     if code==0:
      validate_capture(directory,a.source_root/path,path,a.view,version,graph_sha,producers);receipt_sha=SHA(directory/'receipt.json')
     status=dict(fixed,exit_code=code,log_sha256=SHA(log),summary_sha256=SHA(summary) if summary.exists() else None,receipt_sha256=receipt_sha)
     atomic_json(status_file,status)
   row=dict(path=path,status='unavailable',exit_code=status['exit_code'])
   if status['exit_code']==0:
    assert status['summary_sha256']==SHA(summary)
    data=json.loads(summary.read_text());assert data['base']==API['BASE'] and data['metrics']['path']==path
    validate_capture(directory,a.source_root/path,path,a.view,version,graph_sha,producers)
    actual_receipt_sha=SHA(directory/'receipt.json')
    if 'receipt_sha256' not in status:
     assert not a.check and a.prior_runner_commit,'Legacy status requires explicit validated migration'
     status['receipt_sha256']=actual_receipt_sha;atomic_json(status_file,status)
    assert status['receipt_sha256']==actual_receipt_sha,'Child receipt drift'
    row.update(status='observed',metrics=data['metrics'],encoding=data['encoding'])
   else:
    text=log.read_text(errors='replace');row['failure_class']='timeout' if status['exit_code']==124 else 'capture_failed'
   files.append(row)
   if not a.check:print(index+1,len(queue),row['status'],path,flush=True)
   # Durable progress is evidence on the VM, not a code-branch result.
   if not a.check:atomic_json(a.captures/'progress.json',dict(processed=len(files),planned=len(queue),observed=sum(r['status']=='observed' for r in files),last=path))
 def final_integrity():
  assert producers=={n:SHA(HERE/n) for n in names},'Producer drift before publication'
  assert SHA(graph_file)==graph_sha,'Graph receipt drift before publication'
  API['assert_sources'](a.source_root)
 result=dict(base=API['BASE'],status='partial',planned_files=len(queue),processed_files=len(files),observed_files=sum(r['status']=='observed' for r in files),reused_dense_files=reused,uncached_syntax_files=uncached,resource_wait=resource_wait,files=files,deletable_now_verified_lines=0,boundaries=['Selection is cached files with explicit native syntax-census checks; macro-only and uncached files remain outside this queue.','A successful source capture is observational; complete check roots, reflection, symbolic lookups and compiler/runtime dependencies are not certified.','Existing19dense files are reused rather than re-elaborated.','Failures contribute no observed metric counts; source/provenance integrity failures stop the queue.'])
 body=json.dumps(result,sort_keys=True,indent=2)+'\n';assert len(body.encode())<1000000
 publish_summary(a.out,body,guard=final_integrity,check=a.check)
 print('CACHED_CHECK_QUEUE_PASS',len(files),len(queue),result['observed_files'])
if __name__=='__main__':main()
