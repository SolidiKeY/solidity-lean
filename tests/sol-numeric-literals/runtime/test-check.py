#!/usr/bin/env python3
"""MOCK regression only: no Docker command or actual resource stop occurs."""
import builtins,contextlib,io,json,pathlib,runpy,subprocess,sys,types,uuid
from unittest.mock import patch
folder=pathlib.Path(__file__).resolve().parents[1]
def control(process_exit):
 label='mock-resource-stop-'+uuid.uuid4().hex
 paths=[pathlib.Path('/workspace/sol-numeric-literals-gate-output')/(label+ext) for ext in ('.json','.log')]
 assert not any(p.exists() for p in paths)
 original_read=pathlib.Path.read_text;original_open=builtins.open
 samples=iter((8,8,3));state=dict(stopped=False,inspections=0)
 identity='MOCK-owned-container-before-auto-removal'
 def open_file(path,*args,**kwargs):
  if str(path)=='/tmp/solidity-lean-feature-groups-20261025/writer.lock':return io.StringIO()
  return original_open(path,*args,**kwargs)
 def read(path,*args,**kwargs):
  if str(path)=='/proc/meminfo':return 'MemAvailable: '+str(next(samples,3)*1024**2)+' kB\n'
  if str(path)=='/sys/fs/cgroup/memory.current':return str(1024**3)
  if str(path)=='/sys/fs/cgroup/memory.max':return str(16*1024**3)
  return original_read(path,*args,**kwargs)
 def inspect(args,**kwargs):
  state['inspections']+=1
  assert args==['docker','inspect','--format','{{.Id}}','sol-nl-proof-worker']
  if state['stopped']:raise subprocess.CalledProcessError(1,args)
  return identity+'\n'
 class Process:
  def __init__(self,args,**kwargs):assert args[:3]==['docker','exec',identity]
  def poll(self):return None
  def wait(self):return process_exit
 def run(args,**kwargs):
  if args==['docker','stop',identity]:state['stopped']=True;return types.SimpleNamespace(returncode=0)
  assert args==['docker','exec',identity,'cat','/sys/fs/cgroup/memory.peak'] and state['stopped']
  return types.SimpleNamespace(returncode=1,stdout='')
 try:
  with patch('builtins.open',open_file),patch.object(pathlib.Path,'read_text',read),patch('subprocess.check_output',inspect),patch('subprocess.Popen',Process),patch('subprocess.run',run),patch('fcntl.flock'),patch.object(sys,'argv',['check.py',label,'MOCK-only-command']),contextlib.redirect_stdout(io.StringIO()):
   try:runpy.run_path(str(folder/'runtime/check.py'),run_name='__main__')
   except SystemExit as e:assert e.code==(process_exit if process_exit else 125)
   else:raise AssertionError('resource stop became a passing check')
  row=json.loads(paths[0].read_text())
  assert state['stopped'] and state['inspections']==1
  assert row['resource_stop'] and row['exit']!=0 and row['process_exit']==process_exit
  assert row['container_id']==identity and row['container_memory_peak_bytes'] is None
  assert row['minimum_parent_headroom_bytes']==3*1024**3
 finally:
  for path in paths:
   if path.exists():path.unlink()
for observed in (137,0):control(observed)
print('MOCK controls: auto-removal and concurrent exit-0 race retain failure evidence and never pass; no actual container stopped')
