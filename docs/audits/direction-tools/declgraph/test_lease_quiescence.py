#!/usr/bin/env python3
"""Real process-group lease ordering, guardian handoff and failclosed controls.
No Lean or source-inventory mocks are used by these process tests.
"""
import fcntl,json,os,pathlib,runpy,signal,subprocess,sys,tempfile,threading,time
HERE=pathlib.Path(__file__).resolve().parent;N=runpy.run_path(str(HERE/'owned_native.py'));L=N['L'];T=runpy.run_path(str(HERE/'test_owned_native.py'));alive=T['alive'];available=T['available'];until=T['until']
def main():
 with tempfile.TemporaryDirectory() as directory:
  d=pathlib.Path(directory);lock=d/'lease';log=d/'log';ids=d/'ids';procroot=d/'proc';procroot.mkdir()
  for pid,state,group in [(1,'R',77),(2,'Z',77),(3,'X',77),(4,'S',88)]:
   entry=procroot/str(pid);entry.mkdir();(entry/'stat').write_text(f'{pid} (name ) with space) {state} 1 {group} 0')
  assert L['group_members'](77,procroot)==[1]
  (procroot/'1/stat').write_text('malformed')
  try:L['group_members'](77,procroot)
  except (ValueError,IndexError):pass
  else:raise AssertionError('Malformed process observation accepted')
  states=iter([PermissionError('unknown'),[],[123],[],[]]);calls=[]
  def probe(group):
   value=next(states);calls.append(value)
   if isinstance(value,Exception):raise value
   return value
  assert L['await_quiescence'](77,1,poll=.001,probe=probe) and len(calls)==5
  assert not L['await_quiescence'](77,.01,poll=.001,probe=lambda _:(_ for _ in ()).throw(PermissionError('unknown')))
  child="import os,subprocess,sys,time,json,pathlib; p=subprocess.Popen([sys.executable,'-I','-B','-c','import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(30)'],close_fds=True);time.sleep(.1);pathlib.Path(sys.argv[1]).write_text(json.dumps([os.getpid(),p.pid]))"
  cmd=[sys.executable,'-I','-B','-c',child,str(ids)]
  realwait=L['await_quiescence'];observations=[]
  def ordered_wait(group,timeout,**kwargs):
   assert not available(lock),'Lease released before group observation'
   result=realwait(group,timeout,**kwargs);observations.append(result)
   assert not available(lock),'Lease released during group observation'
   return result
  L['await_quiescence']=ordered_wait
  try:
   with lock.open('a') as lease,log.open('w') as output:
    fcntl.flock(lease,fcntl.LOCK_EX);assert N['run'](cmd,output,cwd=d,env=dict(os.environ),lease=lease,timeout=5)==0
    pair=json.loads(ids.read_text());assert observations==[True] and all(not alive(pid) for pid in pair),'Returned before nonzombie group quiescence'
   assert available(lock)
  finally:L['await_quiescence']=realwait
  # Keep a real TERM-resistant descendant alive by suppressing only this
  # parent's final KILL. It closes inherited FDs; only the guardian can retain
  # the lease after the caller context exits.
  realkill=os.killpg
  def suppress_kill(group,sig):
   if sig!=signal.SIGKILL:return realkill(group,sig)
  out=d/'products';logs=d/'capture';logs.mkdir();module='Fixture.Module';relative=pathlib.Path('Fixture/Module.olean');artifact=out/relative;artifact.parent.mkdir(parents=True);artifact.write_bytes(b'partial');(logs/'receipt.json').write_text('partial receipt')
  spec={'view':str(out),'logs':str(logs),'module':module,'source_root':str(d/'source')};pending=None;ids.unlink()
  try:
   N['os'].killpg=suppress_kill
   with lock.open('a') as lease,log.open('w') as output:
    fcntl.flock(lease,fcntl.LOCK_EX)
    try:N['run'](cmd,output,cwd=d,env=dict(os.environ),lease=lease,timeout=5,cleanup_timeout=.1,cleanup_spec=spec)
    except N['CleanupPending'] as exc:pending=exc
    else:raise AssertionError('Unquiet group returned success')
   assert pending and alive(pending.guardian) and not available(lock),'No confirmed guardian retained lease'
   pair=json.loads(ids.read_text());assert alive(pair[1]) and artifact.exists() and (logs/'receipt.json').exists(),'Live group was quarantined early'
  finally:
   N['os'].killpg=realkill
   if ids.exists():
    try:realkill(json.loads(ids.read_text())[0],signal.SIGKILL)
    except ProcessLookupError:pass
  until(lambda:available(lock));assert not artifact.exists() and not (logs/'receipt.json').exists() and not (logs/'cleanup-pending.json').exists()
  assert any(f.read_bytes()==b'partial' for f in logs.glob('quarantine-exception-*/Fixture/Module.olean'))
  if pending:
   until(lambda:not alive(pending.guardian))
   try:os.waitpid(pending.guardian,os.WNOHANG)
   except ChildProcessError:pass
  # A failed guardian startup must retain the parent's lease until the group
  # is actually observed empty; a competing writer checks before release.
  ids.unlink();original_spawn=subprocess.Popen;errors=[]
  def no_guard(args,*a,**kw):
   if '--guardian' in args:raise OSError('fixture guardian spawn failure')
   return original_spawn(args,*a,**kw)
  def finish():
   try:
    until(ids.exists);time.sleep(.3);assert not available(lock);realkill(json.loads(ids.read_text())[0],signal.SIGKILL)
   except BaseException as exc:errors.append(exc)
  closer=threading.Thread(target=finish,daemon=True)
  try:
   N['os'].killpg=suppress_kill;N['subprocess'].Popen=no_guard
   with lock.open('a') as lease,log.open('w') as output:
    fcntl.flock(lease,fcntl.LOCK_EX);closer.start()
    try:N['run'](cmd,output,cwd=d,env=dict(os.environ),lease=lease,timeout=5,cleanup_timeout=.05)
    except RuntimeError as exc:assert 'parent retained lease' in str(exc)
    else:raise AssertionError('Failed handoff returned success')
    pair=json.loads(ids.read_text());assert all(not alive(pid) for pid in pair) and not available(lock)
   closer.join(timeout=5);assert not errors and available(lock)
  finally:
   N['os'].killpg=realkill;N['subprocess'].Popen=original_spawn
   if ids.exists():
    try:realkill(json.loads(ids.read_text())[0],signal.SIGKILL)
    except ProcessLookupError:pass
 print('LEASE_QUIESCENCE_PASS proc_states unknown_not_empty two_empty_scans lease_order real_guardian_ack deferred_quarantine failed_handoff_retains_lease')
if __name__=='__main__':main()
