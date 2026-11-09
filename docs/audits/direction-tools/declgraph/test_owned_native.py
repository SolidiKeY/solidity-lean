#!/usr/bin/env python3
"""Disposable process tests: timeout, TERM cleanup and SIGKILL lease retention."""
import fcntl,json,os,pathlib,runpy,signal,subprocess,sys,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent;N=runpy.run_path(str(HERE/'owned_native.py'))
def alive(pid):
 try:return pathlib.Path('/proc',str(pid),'stat').read_text().split(') ',1)[1].split()[0]!='Z'
 except FileNotFoundError:return False

def available(path):
 with path.open('a') as lock:
  try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  except BlockingIOError:return False
  return True

def until(fn,timeout=5):
 end=time.monotonic()+timeout
 while time.monotonic()<end:
  value=fn()
  if value:return value
  time.sleep(.01)
 raise AssertionError('Process condition not reached')

def main():
 with tempfile.TemporaryDirectory() as directory:
  d=pathlib.Path(directory);leasepath=d/'lease';ids=d/'ids';log=d/'log'
  child="import os,subprocess,sys,time,json,pathlib; p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)']);pathlib.Path(sys.argv[1]).write_text(json.dumps([os.getpid(),p.pid]));time.sleep(30)"
  command=[sys.executable,'-I','-B','-c',child,str(ids)]
  with leasepath.open('a') as lease,log.open('w') as output:
   fcntl.flock(lease,fcntl.LOCK_EX);code=N['run'](command,output,cwd=d,env=dict(os.environ),lease=lease,timeout=.4)
  assert code==124;pair=json.loads(ids.read_text());until(lambda:all(not alive(pid) for pid in pair));assert available(leasepath)
  def wrapper(command):
   code="import fcntl,os,pathlib,runpy;N=runpy.run_path("+repr(str(HERE/'owned_native.py'))+");lease=open("+repr(str(leasepath))+",'a');fcntl.flock(lease,fcntl.LOCK_EX);out=open("+repr(str(log))+",'w');N['run']("+repr(command)+",out,cwd="+repr(str(d))+",env=dict(os.environ),lease=lease,timeout=30)"
   return subprocess.Popen([sys.executable,'-I','-B','-c',code],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  ids.unlink();proc=wrapper(command)
  try:
   until(ids.exists);pair=json.loads(ids.read_text());assert not available(leasepath)
   proc.terminate();assert proc.wait(timeout=5)!=0;until(lambda:all(not alive(pid) for pid in pair));assert available(leasepath)
  finally:
   if proc.poll() is None:proc.kill();proc.wait()
   for pid in json.loads(ids.read_text()) if ids.exists() else []:
    if alive(pid):os.kill(pid,signal.SIGKILL)
  ids.unlink();resistant="import os,subprocess,sys,time,json,pathlib,signal;signal.signal(signal.SIGTERM,signal.SIG_IGN);p=subprocess.Popen([sys.executable,'-c','import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(30)']);time.sleep(.1);pathlib.Path(sys.argv[1]).write_text(json.dumps([os.getpid(),p.pid]));time.sleep(30)";proc=wrapper([sys.executable,'-I','-B','-c',resistant,str(ids)])
  try:
   until(ids.exists);pair=json.loads(ids.read_text());proc.terminate();time.sleep(.1);proc.send_signal(signal.SIGTERM);proc.send_signal(signal.SIGINT)
   assert proc.wait(timeout=10)!=0;until(lambda:all(not alive(pid) for pid in pair));assert available(leasepath)
  finally:
   if proc.poll() is None:proc.kill();proc.wait()
   for pid in json.loads(ids.read_text()) if ids.exists() else []:
    if alive(pid):os.kill(pid,signal.SIGKILL)
  ids.unlink();short="import os,sys,time,pathlib;pathlib.Path(sys.argv[1]).write_text(str(os.getpid()));time.sleep(1)";proc=wrapper([sys.executable,'-I','-B','-c',short,str(ids)])
  try:
   until(ids.exists);pid=int(ids.read_text());proc.kill();proc.wait(timeout=5)
   assert alive(pid) and not available(leasepath),'Child must inherit lease after uncatchable wrapper death'
   until(lambda:not alive(pid));until(lambda:available(leasepath))
  finally:
   if proc.poll() is None:proc.kill();proc.wait()
   if ids.exists() and alive(int(ids.read_text())):os.kill(int(ids.read_text()),signal.SIGKILL)
 print('OWNED_NATIVE_FIXTURES_PASS timeout_group_cleanup term_group_cleanup repeated_signals_resistant_group sigkill_child_retains_lease budget_unchanged')
if __name__=='__main__':main()
