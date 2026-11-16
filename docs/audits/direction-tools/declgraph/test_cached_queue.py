#!/usr/bin/env python3
"""Queue receipt field tampering and atomic status replacement fixtures."""
import copy,fcntl,json,os,signal,subprocess,pathlib,runpy,sys,tempfile,threading,time
M=runpy.run_path(str(pathlib.Path(__file__).with_name('capture_cached_checks.py')));H=M['HERE']
def main():
 with tempfile.TemporaryDirectory() as d:
  root=pathlib.Path(d);capture=root/'capture';capture.mkdir();view=root/'view';(view/'Solidity').mkdir(parents=True);source=root/'Fixture.lean';source.write_text('example : True := True.intro\n');(view/'Solidity/Fixture.ilean').write_text('{"module":"Solidity.Fixture"}')
  for n in ('roots.jsonl','capture.log'):(capture/n).write_text('fixture\n')
  names=('CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','capture_compact.py');producers={n:M['SHA'](H/n) for n in names};version='Lean (version 4.24.0, commit797c613)';graph='graph-receipt'
  cmd=['lean','--tstack=131072','-j1','-M10000','--run',str(H/'CompactRoots.lean'),str(source),'Solidity.Fixture',str(H/'modules.txt'),str(capture/'roots.jsonl')]
  meta=dict(producers=producers,command=cmd,lean=version,module='Solidity.Fixture',source_sha256=M['SHA'](source),view=str(view),graph_receipt_sha256=graph,exit_code=0,outputs={n:M['SHA'](capture/n) for n in ('roots.jsonl','capture.log')})
  def test(data):
   M['atomic_json'](capture/'receipt.json',data);return M['validate_capture'](capture,source,'Solidity/Fixture.lean',view,version,graph,producers)
  assert test(meta)==meta
  for field,value in [('lean','wrong'),('module','wrong'),('graph_receipt_sha256','wrong'),('command',cmd[:-1]),('source_sha256','wrong')]:
   bad=copy.deepcopy(meta);bad[field]=value
   try:test(bad)
   except AssertionError:pass
   else:raise AssertionError('Tampered receipt accepted: '+field)
  state=root/'status.json';M['atomic_json'](state,{'first':1});M['atomic_json'](state,{'second':2});assert json.loads(state.read_text())=={'second':2};assert not list(root.glob('status.json.tmp-*'))
  fixed=dict(path='Fixture.lean',source_sha256='source',exit_code=0,command=['python3','capture.py'],producers={'capture_cached_checks.py':'current','native':'same'})
  status=copy.deepcopy(fixed);M['validate_status'](status,fixed,{'current','old'})
  status['command']=['flock',M['LOCK']]+fixed['command'];status['producers']['capture_cached_checks.py']='old'
  M['validate_status'](status,fixed,{'current','old'})
  for runners,changed in [({'current'},status),({'current','old'},dict(status,command=['wrong'])),({'current','old'},dict(status,producers=fixed['producers'])),({'current','old'},dict(status,exit_code=124))]:
   try:M['validate_status'](changed,fixed,runners)
   except AssertionError:pass
   else:raise AssertionError('Unverified legacy command accepted')
  lock=root/'writer.lock';marker=root/'started';result=[]
  with lock.open('a') as lease,(root/'child.log').open('w') as output:
   fcntl.flock(lease,fcntl.LOCK_EX)
   cmd=[sys.executable,'-c',"from pathlib import Path;Path("+repr(str(marker))+").write_text('started')"]
   worker=threading.Thread(target=lambda:result.append(M['timed_capture'](cmd,output,lock_path=lock,timeout=0.1)),daemon=True)
   worker.start()
   try:
    time.sleep(0.3)
    assert worker.is_alive() and not result and not marker.exists(),'Lock wait started capture or consumed its timeout'
   finally:fcntl.flock(lease,fcntl.LOCK_UN)
   worker.join(timeout=5)
   assert not worker.is_alive() and result==[0] and marker.read_text()=='started'
  with (root/'timeout.log').open('w') as output:
   assert M['timed_capture']([sys.executable,'-c','import time;time.sleep(10)'],output,lock_path=lock,timeout=0.1)==124
  descendant=root/'descendant.pid'
  resistant="import os,signal,time;from pathlib import Path;signal.signal(signal.SIGTERM,signal.SIG_IGN);Path("+repr(str(descendant))+").write_text(str(os.getpid()));time.sleep(10)"
  wrapper="import subprocess,sys,time;subprocess.Popen("+repr([sys.executable,'-c',resistant])+");time.sleep(10)"
  with (root/'descendant.log').open('w') as output:
   assert M['timed_capture']([sys.executable,'-c',wrapper],output,lock_path=lock,timeout=0.3)==124
  assert descendant.exists(),'Descendant fixture failed to start'
  stat=pathlib.Path('/proc')/descendant.read_text()/'stat';deadline=time.monotonic()+2
  while stat.exists() and stat.read_text().split()[2]!='Z':
   assert time.monotonic()<deadline,'TERM-resistant owned descendant survived timeout';time.sleep(0.01)
  # SIGTERM of the queue parent must not release a still-running child's lease.
  marker.unlink();release=root/'release';pidfile=root/'child.pid';recovering=root/'recovering';recovering.mkdir();receipt=recovering/'receipt.json'
  child="import os,time;from pathlib import Path;Path("+repr(str(pidfile))+").write_text(str(os.getpid()));Path("+repr(str(marker))+").write_text('started');exec(\"while not Path("+repr(str(release))+").exists(): time.sleep(0.01)\");Path("+repr(str(receipt))+").write_text('complete')"
  parent="import runpy,sys;M=runpy.run_path("+repr(str(H/'capture_cached_checks.py'))+");M['timed_capture']("+repr([sys.executable,'-c',child])+",sys.stdout,lock_path="+repr(str(lock))+",timeout=10)"
  with (root/'orphan.log').open('w') as output:
   owner=subprocess.Popen([sys.executable,'-c',parent],stdout=output,stderr=output)
   try:
    deadline=time.monotonic()+5
    while not marker.exists() and time.monotonic()<deadline:time.sleep(0.01)
    assert marker.exists(),'Child failed to start'
    owner.terminate();owner.wait(timeout=5)
    with lock.open('a') as lease:
     try:fcntl.flock(lease,fcntl.LOCK_EX|fcntl.LOCK_NB)
     except BlockingIOError:pass
     else:raise AssertionError('Queue termination released active child lease')
    recovery=[];errors=[]
    def restart_recovery():
     try:
      with M['capture_transaction'](recovering,lock_path=lock) as (_,complete):
       if not complete:recovering.rename(root/'quarantined');recovery.append('quarantined')
       else:recovery.append(receipt.read_text())
     except BaseException as exc:errors.append(exc)
    restart=threading.Thread(target=restart_recovery,daemon=True);restart.start()
    time.sleep(0.15)
    assert restart.is_alive() and not recovery and recovering.exists() and not receipt.exists(),'Recovery inspected or mutated active capture'
    release.write_text('finish');restart.join(timeout=5)
    assert not restart.is_alive() and not errors and recovery==['complete'] and recovering.exists(),'Recovery did not recheck completed receipt under lease'
   finally:
    if owner.poll() is None:owner.kill();owner.wait()
    if pidfile.exists():
     try:os.killpg(int(pidfile.read_text()),signal.SIGKILL)
     except ProcessLookupError:pass
  # Publication must revalidate after waiting for a concurrent writer.
  published=root/'published.json';published.write_text('old');guarded=['original'];errors=[]
  def guard():assert guarded==['original'],'Inputs changed while waiting'
  def publish():
   try:M['publish_summary'](published,'new',guard=guard,lock_path=lock)
   except BaseException as exc:errors.append(exc)
  with M['writer_lease'](lock):
   publisher=threading.Thread(target=publish,daemon=True);publisher.start();time.sleep(0.1)
   assert publisher.is_alive() and published.read_text()=='old'
   guarded[0]='changed'
  publisher.join(timeout=5)
  assert not publisher.is_alive() and len(errors)==1 and isinstance(errors[0],AssertionError) and published.read_text()=='old'
  guarded[0]='original';M['publish_summary'](published,'exact body\n',guard=guard,lock_path=lock)
  assert published.read_text()=='exact body\n' and not list(root.glob('published.json.tmp-*'))
  M['publish_summary'](published,'exact body\n',guard=guard,check=True,lock_path=lock)
 print('CACHED_QUEUE_FIXTURES_PASS native_recipe module version graph_receipt source atomic_replace lock_wait_excluded child_timeout legacy_command orphan_lease descendant_cleanup recovery_wait_recheck publication_guard')
if __name__=='__main__':main()
