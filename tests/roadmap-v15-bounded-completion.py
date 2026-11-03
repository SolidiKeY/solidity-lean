#!/usr/bin/env python3
"""Pure synthetic lifecycle/control tests: no Docker, Lean, server or build."""
import importlib.util,sys,unittest,copy
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('v15bounded',root/'scripts/roadmap-v15-bounded-completion.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
CID='a'*64
HEADER='PID ELAPSED RSS STAT COMMAND COMMAND\n'
def top(*rows):return HEADER+'\n'.join(rows)+'\n'
def state(running=True,status='running',code=0):return dict(Id=CID,HostConfig=dict(Memory=m.CAP,MemorySwap=m.CAP),Config=dict(Env=['LEAN_NUM_THREADS=1']),State=dict(Running=running,Status=status,ExitCode=code))
FENCE=top('1 1 100 S bash bash -c fixed-fence','2 0 20 S sleep sleep 0.05')
ALLOWED={'sleep 0.05':'sleep'}
class LifecycleTests(unittest.TestCase):
 def setUp(self):self.life=m.Lifecycle(CID,0)
 def test_prestart_missing_pending(self):self.assertEqual(self.life.observe(1,None,None),'pending')
 def test_created_pending(self):self.assertEqual(self.life.observe(1,state(False,'created'),None),'pending')
 def test_prestart_top_gap_pending(self):self.assertEqual(self.life.observe(1,state(),None),'pending')
 def test_startup_deadline_unchanged(self):
  with self.assertRaises(m.GuardError):self.life.observe(10,None,None)
 def test_limits_and_serial_required(self):
  for mutate in [lambda s:s['HostConfig'].update(Memory=m.CAP-1),lambda s:s['HostConfig'].update(MemorySwap=2*m.CAP),lambda s:s['Config'].update(Env=[])]:
   s=state();mutate(s)
   with self.assertRaises(m.GuardError):self.life.observe(1,s,FENCE,[str(m.CAP),'0'])
 def test_exact_id_required(self):
  s=state();s['Id']='b'*64
  with self.assertRaises(m.GuardError):self.life.observe(1,s,FENCE,[str(m.CAP),'0'])
 def test_admit_only_observed_limits(self):
  self.assertEqual(self.life.observe(1,state(),FENCE,None),'pending')
  self.assertEqual(self.life.observe(1,state(),FENCE,[str(m.CAP),'0']),'admit')
 def test_no_lean_before_release(self):
  with self.assertRaises(m.GuardError):self.life.observe(1,state(),top('2 1 10 S lean lean -j1 file.lean'),[str(m.CAP),'0'])
 def test_postrelease_top_gap_fails_even_done(self):
  self.life.admitted=True
  with self.assertRaises(m.GuardError):self.life.observe(2,state(),None)
 def test_missing_j1_workers_time(self):
  self.life.admitted=True
  for rows in [('2 1 10 S lean lean file.lean',),('2 1 10 S lean lean -j1 a.lean','3 1 10 S lean lean -j1 b.lean'),('2 300 10 S lean lean -j1 a.lean',)]:
   with self.assertRaises(m.GuardError):self.life.observe(2,state(),top(*rows))
 def test_exact_terminal_nonzero(self):
  self.life.admitted=True
  self.assertEqual(self.life.observe(2,state(False,'exited',17),None),('terminal',17))
 def test_unknown_terminal_fails(self):
  self.life.admitted=True
  with self.assertRaises(m.GuardError):self.life.observe(2,state(False,'dead'),None)
LOOP='fixed-terminal-loop'
def fenced(code=0,extra=()):
 return 'PID PPID ELAPSED RSS STAT COMMAND COMMAND\n'+'\n'.join([
  '1 0 1 100 S bash bash -c fixed-fence',
  '2 1 1 20 S timeout timeout 10 bash -c '+LOOP+' v15-completion token '+str(code),
  '3 2 1 20 S bash bash -c '+LOOP+' v15-completion token '+str(code),
  '4 3 0 10 S sleep sleep 0.05',*extra])+'\n'
class CompletionTests(unittest.TestCase):
 def check(self,marker,processes=None,reader=lambda p:p):
  return m.completed_workload(marker,'token',fenced() if processes is None else processes,1,'bash -c fixed-fence',LOOP,'mv temp done',reader)
 def test_success_and_real_failure(self):
  self.assertEqual(self.check('token 0 3 2\n'),0)
  self.assertEqual(self.check('token 17 3 2\n',fenced(17)),17)
 def test_marker_missing(self):self.assertIsNone(self.check(None))
 def test_bad_nonce_status_partial(self):
  for marker in ['wrong 0 3 2\n','token 256 3 2\n','token 00 3 2\n','token 0 3 2','token 0 3 2\nextra']:
   with self.assertRaises(m.GuardError):self.check(marker)
 def test_unobserved_completed_fence_fails(self):
  with self.assertRaises(m.GuardError):m.completed_workload('token 0 3 2\n','token',None,1,'bash -c fixed-fence',LOOP,'mv temp done')
 def test_lingering_or_unknown_workload_fails(self):
  for row in ['5 1 1 10 S lean lean -j1 file.lean','5 1 1 10 S lake lake build','5 1 1 10 S bash bash -c unknown','5 1 1 10 S cc cc file.c']:
   with self.assertRaises(m.GuardError):self.check('token 0 3 2\n',fenced(extra=[row]))
 def test_same_command_workload_sleeper_rejected(self):
  with self.assertRaises(m.GuardError):self.check('token 0 3 2\n',fenced(extra=['5 1 0 10 S sleep sleep 0.05']))
 def test_wrong_parent_even_without_duplicate_rejected(self):
  text=fenced().replace('4 3 0 10 S sleep','4 1 0 10 S sleep')
  with self.assertRaises(m.GuardError):self.check('token 0 3 2\n',text)
 def test_spoofed_marker_pid_rejected(self):
  with self.assertRaises(m.GuardError):self.check('token 0 30 20\n')
 def test_unobservable_namespace_rejected(self):
  def unavailable(p):raise PermissionError()
  with self.assertRaises(m.GuardError):self.check('token 0 3 2\n',reader=unavailable)
 def test_wrong_main_pid_comm_and_duplicate_roles_rejected(self):
  for text in [fenced().replace('1 0 1 100 S bash','9 0 1 100 S bash'),fenced().replace('1 0 1 100 S bash','1 0 1 100 S evil'),fenced(extra=['6 1 1 20 S timeout timeout 10 bash -c '+LOOP+' v15-completion token 0'])]:
   with self.assertRaises(m.GuardError):self.check('token 0 3 2\n',text)
 def test_exact_atomic_move_pending(self):
  self.assertIsNone(self.check('token 0 3 2\n',fenced(extra=['5 3 0 10 S mv mv temp done'])))
 def test_inert_zombie_cannot_run(self):self.assertEqual(self.check('token 0 3 2\n',fenced(extra=['5 1 0 0 Z lean lean -j1 old.lean'])),0)
 def test_shell_marker_has_exact_newline_format(self):
  fmt=[c[c.index("printf "):] for c in m.run.__code__.co_consts if isinstance(c,str) and "printf " in c]
  self.assertEqual(fmt,["printf '%s %s %s %s"+chr(92)+"n' "+'"$1" "$2" "$BASHPID" "$PPID" > '])
 def test_active_lifecycle_byte_identical(self):
  old=Path('/workspace/v15-evm-agreement-evidence/p10-help-20261102/run-bounded-02.py').read_text()
  new=(root/'scripts/roadmap-v15-bounded-completion.py').read_text()
  self.assertEqual(old[old.index('class Lifecycle:'):old.index('\ndef run(')].rstrip(),new[new.index('class Lifecycle:'):new.index('\ndef namespace_pid')].rstrip())
 def test_caps_unchanged(self):self.assertEqual((m.CAP,m.RESERVE),(12884901888,4294967296))
if __name__=='__main__':unittest.main(verbosity=2)
