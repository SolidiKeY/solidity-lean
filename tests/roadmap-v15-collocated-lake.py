#!/usr/bin/env python3
import importlib.util,unittest
from pathlib import Path
spec=importlib.util.spec_from_file_location('route',Path(__file__).parents[1]/'scripts/roadmap-v15-collocated-lake.py')
route=importlib.util.module_from_spec(spec);spec.loader.exec_module(route)
GOOD='weakLeanArgs = ["-j1", "--tstack=131072"]\n'
class Tests(unittest.TestCase):
 def runplan(self,args,cwd=None,env=None,text=GOOD):
  return route.plan(args,cwd or route.ROOT,env or {},read=lambda p:text)
 def test_core_exact(self):
  cmd,env=self.runplan(['-j1','build','Solidity.KeySort'])
  self.assertEqual(cmd,[str(route.SDK/'bin/lake'),'--no-cache','-f',str(route.RUNTIME/'core.toml'),'build','Solidity.KeySort'])
  self.assertEqual(env['LEAN_NUM_THREADS'],'1')
 def test_bridge_pins(self):
  cmd,_=self.runplan(['build','SolidityBridge'],route.ROOT/'Bridge')
  self.assertIn('--packages='+str(route.RUNTIME/'package-overrides.json'),cmd)
 def test_override_removed(self):
  _,env=self.runplan(['build','Solidity'],env={'LEAN_NUM_THREADS':'8','LAKE_OVERRIDE_LEAN':'true','LEAN_SYSROOT':'old','LEAN':'old'})
  self.assertEqual(env['LAKE_OVERRIDE_LEAN'],'false');self.assertEqual(env['LEAN_NUM_THREADS'],'1')
  self.assertNotIn('LEAN_SYSROOT',env);self.assertNotIn('LEAN',env)
 def test_j_split(self):self.assertEqual(self.runplan(['-j','1','build','Solidity'])[0][-2:],['build','Solidity'])
 def test_parallel_rejected(self):
  for args in [['-j2','build','Solidity'],['-j','2','build','Solidity'],['build','-j2']]:
   with self.assertRaises(ValueError):self.runplan(args)
 def test_wrong_cwd(self):
  with self.assertRaises(ValueError):self.runplan(['build','Solidity'],Path('/tmp/other'))
 def test_config_change_rejected(self):
  for text in ['',GOOD.replace('-j1','-j2'),GOOD.replace('131072','262144')]:
   with self.assertRaises(ValueError):self.runplan(['build','Solidity'],text=text)
 def test_no_shell_or_env_escape(self):
  for args in [['env','lean','foo.lean'],['build','x;true'],['build','--update'],['build'],[]]:
   with self.assertRaises(ValueError):self.runplan(args)
 def test_metadata_commands(self):
  for args in [['--version'],['-j1','env','/bin/true']]:self.assertEqual(self.runplan(args)[0][-len(args)+int(args[0]=='-j1'):],args[int(args[0]=='-j1'):])
 def test_unknown_zombie_still_refused(self):
  spec=importlib.util.spec_from_file_location('guard',Path(__file__).parents[1]/'scripts/roadmap-v15-bounded-pidfd.py')
  guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
  tracker=guard.TerminalTracker(lambda event:None)
  try:
   with self.assertRaises(guard.GuardError):
    tracker.snapshot('PID ELAPSED RSS STAT COMMAND COMMAND\n1234500 0 0 Z lean [lean] <defunct>\n')
  finally:tracker.close()
if __name__=='__main__':unittest.main()
