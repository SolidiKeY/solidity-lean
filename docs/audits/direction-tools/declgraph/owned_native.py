#!/usr/bin/env python3
"""Bounded owned process groups retaining the caller's writer lease.
TERM/INT unwind and drain the group before the caller can release its lease.
An uncatchable wrapper death still leaves the direct child holding the lease.
"""
if not __debug__: raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import os,signal,subprocess

def run(command,output,*,cwd,env,lease,timeout=600):
 assert 0 < timeout <= 600
 proc=None;previous={}
 def interrupted(signum,frame): raise InterruptedError('Owned native wrapper interrupted')
 try:
  for sig in (signal.SIGTERM,signal.SIGINT):
   previous[sig]=signal.signal(sig,interrupted)
  proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(lease.fileno(),))
  try:return proc.wait(timeout=timeout)
  except subprocess.TimeoutExpired:
   output.write('OWNED_NATIVE_TIMEOUT '+str(timeout)+'\n');output.flush();return 124
 finally:
  try:
   # A second cancellation must not unwind group cleanup prematurely.
   for sig in previous:signal.signal(sig,signal.SIG_IGN)
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
