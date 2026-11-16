#!/usr/bin/env python3
"""Bounded owned process groups retaining the caller's writer lease.
TERM/INT handlers only record cancellation, including during spawn and cleanup.
Polling unwinds safely. Successful return requires observed group quiescence.
Cleanup uncertainty hands the lease to an acknowledged guardian before raising.
After uncatchable wrapper death, only a still-live direct child or acknowledged
guardian retains the lease. Leader exit before guardian acknowledgement is not
covered by that conditional guarantee.
"""
if not __debug__: raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import os,signal,subprocess,time,pathlib,runpy
L=runpy.run_path(str(pathlib.Path(__file__).with_name('lease_lifecycle.py')))
class CleanupPending(RuntimeError):
 def __init__(self,pgid,guardian):
  super().__init__(f'Owned group{pgid} cleanup pending; lease guardian{guardian}');self.pgid=pgid;self.guardian=guardian

def run(command,output,*,cwd,env,lease,timeout=600,cleanup_timeout=5,cleanup_spec=None,cancel_check=None):
 assert 0 < timeout <= 600 and 0 < cleanup_timeout <= 5
 cleanup_spec=L['validate_spec'](cleanup_spec)
 proc=None;pending=None;previous={};code=None
 def interrupted(signum,frame):
  nonlocal pending
  # Never raise between OS child creation and recording its Popen handle,
  # or while cleanup/handler restoration is in progress.
  pending=signum
 try:
  for sig in (signal.SIGTERM,signal.SIGINT):
   previous[sig]=signal.signal(sig,interrupted)
  if cancel_check is not None and cancel_check():raise InterruptedError('Native startup cancelled by caller')
  proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(lease.fileno(),))
  deadline=time.monotonic()+timeout
  while True:
   if pending is not None or (cancel_check is not None and cancel_check()):raise InterruptedError('Owned native wrapper interrupted')
   remaining=deadline-time.monotonic()
   if remaining<=0:
    output.write('OWNED_NATIVE_TIMEOUT '+str(timeout)+'\n');output.flush();code=124;break
   try:code=proc.wait(timeout=min(.1,remaining));break
   except subprocess.TimeoutExpired:pass
 finally:
  try:
   if proc is not None:
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
     try:os.killpg(proc.pid,signal.SIGKILL)
     except ProcessLookupError:pass
    # The direct child may already have exited while descendants remain.
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    if not L['await_quiescence'](proc.pid,cleanup_timeout):
     try:keeper=L['handoff'](proc.pid,lease,cleanup_spec)
     except BaseException:keeper=None
     if keeper is not None:
      try:output.write(f'OWNED_GROUP_CLEANUP_PENDING {proc.pid} {keeper}\n');output.flush()
      except BaseException:pass
      raise CleanupPending(proc.pid,keeper)
     try:output.write('OWNED_GROUP_HANDOFF_FAILED retaining lease until quiescent\n');output.flush()
     except BaseException:pass
     L['await_quiescence'](proc.pid,None)
     proc.wait()
     raise RuntimeError('Group cleanup deadline exceeded; parent retained lease until quiescent')
    proc.wait()
  finally:
   for sig,handler in previous.items():signal.signal(sig,handler)
 if pending is not None or (cancel_check is not None and cancel_check()):raise InterruptedError('Owned native cleanup interrupted')
 return code
