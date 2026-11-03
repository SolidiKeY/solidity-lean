#!/usr/bin/env python3
"""Synthetic diagnostic-retention checks; no Docker, Lean, server or build."""
import ast,importlib.util,subprocess,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[1]
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
old=load('v15capture',root/'scripts/roadmap-v15-bounded-capture.py')
new=load('v15diagnostics',root/'scripts/roadmap-v15-bounded-diagnostics.py')
class DiagnosticTests(unittest.TestCase):
 def test_caps_unchanged(self):self.assertEqual((new.CAP,new.RESERVE),(12884901888,4294967296))
 def test_decisions_byte_identical(self):
  a=(root/'scripts/roadmap-v15-bounded-capture.py').read_text();b=(root/'scripts/roadmap-v15-bounded-diagnostics.py').read_text()
  for name in ['Lifecycle','namespace_pid','completed_workload']:
   x=next(n for n in ast.parse(a).body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name==name)
   y=next(n for n in ast.parse(b).body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name==name)
   self.assertEqual(ast.get_source_segment(a,x),ast.get_source_segment(b,y))
 def test_run_has_only_logging_added(self):
  def run(path):return next(n for n in ast.parse(path.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='run')
  a=run(root/'scripts/roadmap-v15-bounded-capture.py');b=run(root/'scripts/roadmap-v15-bounded-diagnostics.py')
  class Strip(ast.NodeTransformer):
   def visit_Expr(self,n):
    if isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Name) and n.value.func.id=='record_completion_snapshot':return None
    return self.generic_visit(n)
  self.assertEqual(ast.dump(a,include_attributes=False),ast.dump(Strip().visit(b),include_attributes=False))
 def test_unknown_process_captured_and_rejected(self):
  events=[];raw='PID PPID ELAPSED RSS STAT COMMAND COMMAND\n99 1 0 20 S unknown unknown-workload\n'
  result=subprocess.CompletedProcess([],0,raw,'');new.record_completion_snapshot(events,'a'*64,'token 0 3 2\n',result)
  with self.assertRaisesRegex(new.GuardError,'unknown process'):
   new.completed_workload('token 0 3 2\n','token',raw,1,'fixed','loop','move')
  self.assertEqual(events[0]['detailedTop'],raw)
 def test_failed_top_captured(self):
  events=[];new.record_completion_snapshot(events,'a'*64,'marker',subprocess.CompletedProcess([],1,'','unobservable'))
  self.assertEqual((events[0]['detailedTopExit'],events[0]['detailedTopStderr']),(1,'unobservable'))
if __name__=='__main__':unittest.main(verbosity=2)
