#!/usr/bin/env python3
"""Bounded owned process groups retaining the caller's writer lease.
TERM/INT handlers only record cancellation, including during spawn and cleanup.
Polling unwinds at a safe point; group drain precedes handler/lease release.
An uncatchable wrapper death still leaves the direct child holding the lease.
"""
if not __debug__: raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import os,signal,subprocess,time

def run(command,output,*,cwd,env,lease,timeout=600):
 assert 0 < timeout <= 600
 proc=None;pending=None;previous={};code=None
 def interrupted(signum,frame):
  nonlocal pending
  # Never raise between OS child creation and recording its Popen handle,
  # or while cleanup/handler restoration is in progress.
  pending=signum
 try:
  for sig in (signal.SIGTERM,signal.SIGINT):
   previous[sig]=signal.signal(sig,interrupted)
  proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(lease.fileno(),))
  deadline=time.monotonic()+timeout
  while True:
   if pending is not None:raise InterruptedError('Owned native wrapper interrupted')
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
     proc.wait()
    # The direct child may already have exited while descendants remain.
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    proc.wait()
  finally:
   for sig,handler in previous.items():signal.signal(sig,handler)
 if pending is not None:raise InterruptedError('Owned native cleanup interrupted')
 return code
