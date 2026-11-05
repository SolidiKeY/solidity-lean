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
  self.t=m.TerminalTracker(self.events.append,exe='/sdk/lean',identity=identity,launch=identity,opener=lambda pid,flags:7,dead=lambda fd:self.dead,closer=self.closed.append,wait_dead=lambda fd:False)
 def top(self,args='/sdk/lean -j1 f.lean',rss=100):return HEADER+f'42 2 {rss} R lean {args}\n'
 def bind(self):self.assertEqual(self.t.snapshot(self.top()),self.top())
 def test_live_bound(self):self.bind();self.assertEqual(self.events[0]['event'],'pidfd-bound')
 def test_terminal_blank_then_zombie(self):
  self.bind();self.dead=True;self.current['state']='Z'
  self.assertEqual(self.t.snapshot(self.top('[lean]',0)),HEADER)
  zombie=self.top('[lean] <defunct>',0).replace(' R lean ',' Zl lean ')
  self.assertEqual(self.t.snapshot(zombie),zombie)
  self.assertTrue(self.t.bound);self.assertEqual(self.closed,[])
  self.current=None;self.t.snapshot(HEADER);self.assertEqual(self.closed,[7])
 def test_terminal_blank_repeated(self):
  self.bind();self.dead=True;self.current['state']='Z'
  for _ in range(3):self.assertEqual(self.t.snapshot(self.top('[lean]',0)),HEADER)
  self.assertTrue(self.t.bound);self.assertEqual(self.closed,[])
  self.current=None;self.t.snapshot(HEADER);self.assertEqual(self.closed,[7])
 def missing_launch(self):
  def missing(pid):raise FileNotFoundError('synthetic exited executable link')
  self.t.launch=missing
 def test_bound_launch_missing_terminal_retained(self):
  self.bind();self.dead=True;self.current['state']='Z';self.missing_launch()
  self.assertEqual(self.t.snapshot(self.top()),HEADER)
  self.assertTrue(self.t.bound);self.assertEqual(self.closed,[])
  self.current=None;self.t.snapshot(HEADER);self.assertEqual(self.closed,[7])
 def test_bound_launch_missing_live_rejected(self):
  self.bind();self.missing_launch()
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top())
  self.assertTrue(self.t.bound)
 def test_bound_launch_missing_reused_rejected(self):
  self.bind();self.dead=True;self.current.update(start=11,state='Z');self.missing_launch()
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top())
 def test_bound_launch_permission_error_rejected(self):
  self.bind();self.dead=True;self.current['state']='Z'
  def denied(pid):raise PermissionError('not an exit observation')
  self.t.launch=denied
  with self.assertRaises(PermissionError):self.t.snapshot(self.top())
 def test_unknown_launch_missing_rejected(self):
  self.dead=True;self.missing_launch()
  with self.assertRaises(FileNotFoundError):self.t.snapshot(self.top())
  self.assertFalse(self.t.bound)
 def test_bound_launch_missing_changed_snapshot_rejected(self):
  self.bind();self.dead=True;self.current['state']='Z';self.missing_launch()
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('/sdk/lean -j1 changed.lean'))
 def test_bound_launch_missing_waits_for_kernel(self):
  self.bind();self.missing_launch()
  def finish(fd):self.dead=True;self.current['state']='Z';return True
  self.t.wait_dead=finish
  self.assertEqual(self.t.snapshot(self.top()),HEADER)
  self.assertTrue(any(x['event']=='terminal-wait' for x in self.events))
 def test_bound_launch_missing_live_identity_rejected(self):
  self.bind();self.dead=True;self.missing_launch()
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top())
 def test_unknown_blank_rejected(self):
  self.dead=True
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_live_blank_rejected(self):
  self.bind()
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_terminal_absent(self):
  self.bind();self.dead=True;self.current=None
  self.assertEqual(self.t.snapshot(self.top('[lean]',0)),HEADER);self.assertEqual(self.closed,[])
  self.t.snapshot(HEADER);self.assertEqual(self.closed,[7])
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
 def test_exit_transition_waits_for_kernel(self):
  self.bind()
  def finish(fd):
   self.assertEqual(fd,7);self.dead=True;self.current['state']='Z';return True
  self.t.wait_dead=finish
  self.assertEqual(self.t.snapshot(self.top('[lean]',0)),HEADER)
  self.assertEqual(self.closed,[])
  self.t.snapshot(HEADER);self.assertEqual(self.closed,[7])
  self.assertTrue(any(x['event']=='terminal-wait' and x['timeoutMs']==50 for x in self.events))
 def test_wait_error_rejected(self):
  self.bind()
  def bad(fd):raise PermissionError('poll denied')
  self.t.wait_dead=bad
  with self.assertRaises(PermissionError):self.t.snapshot(self.top('[lean]',0))
 def test_wait_cannot_forge_readiness(self):
  self.bind();self.t.wait_dead=lambda fd:True
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_wait_does_not_accept_live_identity(self):
  self.bind()
  def ready(fd):self.dead=True;return True
  self.t.wait_dead=ready
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_zombie_live_refused_after_wait(self):
  self.bind();calls=[]
  self.t.wait_dead=lambda fd:calls.append(fd) or False
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top().replace(' R lean ', ' Z lean '))
  self.assertEqual(calls,[7])
 def test_reuse_during_wait_rejected(self):
  self.bind()
  def reuse(fd):
   self.dead=True;self.current['state']='Z';self.current['start']+=1;return True
  self.t.wait_dead=reuse
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top('[lean]',0))
 def test_missing_exit_wait(self):
  self.bind()
  def finish(fd):self.dead=True;self.current=None;return True
  self.t.wait_dead=finish
  self.assertEqual(self.t.snapshot(HEADER),HEADER);self.assertFalse(self.t.bound)
 def test_zl_exit_wait(self):
  self.bind()
  def finish(fd):self.dead=True;self.current['state']='Z';return True
  self.t.wait_dead=finish
  self.t.snapshot(self.top().replace(' R lean ', ' Zl lean '));self.assertTrue(self.t.bound)
 def test_unbound_zl_never_waits(self):
  self.t.wait_dead=lambda fd:self.fail('unbound caller waited')
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top().replace(' R lean ', ' Zl lean '))
 def test_missing_reuse_during_wait_rejected(self):
  self.bind()
  def finish(fd):self.dead=True;self.current['state']='Z';self.current['start']+=1;return True
  self.t.wait_dead=finish
  with self.assertRaises(m.GuardError):self.t.snapshot(HEADER)
 def test_zl_nonterminal_identity_rejected(self):
  self.bind();self.dead=True
  with self.assertRaises(m.GuardError):self.t.snapshot(self.top().replace(' R lean ', ' Zl lean '))
 def test_repeated_zl_then_missing(self):
  self.bind();self.dead=True;self.current['state']='Z'
  zombie=self.top().replace(' R lean ', ' Zl lean ')
  self.assertEqual(self.t.snapshot(zombie),zombie)
  self.assertEqual(self.t.snapshot(zombie),zombie);self.assertEqual(self.closed,[])
  self.current=None;self.assertEqual(self.t.snapshot(HEADER),HEADER);self.assertEqual(self.closed,[7])
 def test_reused_verified_zombie_refused(self):
  self.bind();self.dead=True;self.current['state']='Z'
  zombie=self.top().replace(' R lean ', ' Zl lean ');self.t.snapshot(zombie)
  self.current['start']+=1
  with self.assertRaises(m.GuardError):self.t.snapshot(zombie)
 def test_production_wait_uses_50ms_poll(self):
  self.bind();timeouts=[];registered=[];owner=self
  class Poll:
   def register(self,fd,mask):registered.append((fd,mask))
   def poll(self,timeout):
    timeouts.append(timeout);owner.dead=True;owner.current['state']='Z'
    return [(7,m.select.POLLIN)]
  original=m.select.poll
  default=m.TerminalTracker(self.events.append,exe='/sdk/lean')
  self.t.wait_dead=default.wait_dead
  try:
   m.select.poll=Poll
   self.t.snapshot(HEADER)
  finally:m.select.poll=original
  self.assertEqual(timeouts,[50]);self.assertEqual(registered,[(7,m.select.POLLIN)])
 def test_unchanged_limits(self):
  self.assertEqual((m.base.CAP,m.base.RESERVE),(12884901888,4294967296))
if __name__=='__main__':unittest.main()
