#!/usr/bin/env python3
"""Fail-closed terminal identity tests. No Lean, Docker or builds."""
import importlib.util,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('pidfd_runner',Path(__file__).resolve().parents[1]/'scripts/roadmap-v15-bounded-pidfd.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
HEADER='PID ELAPSED RSS STAT COMMAND COMMAND\n'
class Tests(unittest.TestCase):
 def setUp(self):
  self.events=[];self.closed=[];self.dead=False
  self.current=dict(pid=42,comm='lean',state='R',start=10,argv=['/sdk/lean','-j1','f.lean'],exe='/sdk/lean')
  def identity(pid):
   if self.current is None:raise FileNotFoundError()
   return dict(self.current)
  self.t=m.TerminalTracker(self.events.append,exe='/sdk/lean',identity=identity,launch=identity,opener=lambda pid,flags:7,dead=lambda fd:self.dead,closer=self.closed.append)
 def top(self,args='/sdk/lean -j1 f.lean',rss=100):return HEADER+f'42 2 {rss} R lean {args}\n'
 def bind(self):self.assertEqual(self.t.snapshot(self.top()),self.top())
 def test_live_bound(self):self.bind();self.assertEqual(self.events[0]['event'],'pidfd-bound')
 def test_unknown_blank_rejected(self):
  self.dead=True
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_live_blank_rejected(self):
  self.bind()
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_terminal_absent(self):
  self.bind();self.dead=True;self.current=None
  self.assertEqual(self.t.snapshot(self.top('[lean]',0)),HEADER);self.assertEqual(self.closed,[7])
 def test_terminal_zombie(self):
  self.bind();self.dead=True;self.current['state']='Z'
  self.assertEqual(self.t.snapshot(self.top('[lean]',0)),HEADER)
 def test_reused_pid_rejected(self):
  self.bind();self.dead=True;self.current['start']=11;self.current['state']='Z'
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_still_live_rejected(self):
  self.bind();self.dead=True
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_missing_serial_never_excused(self):
  self.bind();self.dead=True;self.current=None
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('/sdk/lean f.lean'))
 def test_changed_executable(self):
  self.bind();self.current['exe']='/other/lean'
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top())
 def test_missing_pidfd(self):
  def fail(*args):raise PermissionError('pidfd blocked')
  self.t.opener=fail
  with self.assertRaises(PermissionError):self.bind()
 def test_duplicate(self):
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top()+self.top().splitlines()[1]+'\n')
 def test_unsafe_label(self):
  with self.assertRaises(ValueError):m.run('/nonexistent','../escape','true')
 def test_missing_live_rejected(self):
  self.bind()
  with self.assertRaises(m.GuardError):self.t.snapshot(HEADER+'1 0 1 S bash bash\n')
 def test_missing_terminal_retired(self):
  self.bind();self.dead=True;self.current=None
  self.t.snapshot(HEADER+'1 0 1 S bash bash\n');self.assertFalse(self.t.bound)
 def test_bind_race_rejected(self):
  original=self.t.launch;calls=[0]
  def moving(pid):
   x=original(pid);calls[0]+=1
   if calls[0]>1:x['start']+=1
   return x
  self.t.launch=moving
  with self.assertRaises(m.GuardError):self.bind()
  self.assertEqual(self.closed,[7])
 def test_pidfd_error_rejected(self):
  self.bind()
  def fail(fd):raise m.GuardError('unverifiable pidfd status')
  self.t.dead=fail
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_terminal_time_boundary_rejected(self):
  self.bind();self.dead=True;self.current=None
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0).replace('42 2 ','42 300 '))
 def test_terminal_below_boundary(self):
  self.bind();self.dead=True;self.current=None
  self.assertEqual(self.t.snapshot(self.top('[lean]',0).replace('42 2 ','42 299 ')),HEADER)
 def test_unchanged_limits(self):
  self.assertEqual((m.base.CAP,m.base.RESERVE),(12884901888,4294967296))
if __name__=='__main__':unittest.main()
