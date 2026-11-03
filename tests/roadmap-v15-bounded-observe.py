#!/usr/bin/env python3
"""Evidence-only lifecycle logging tests; no Docker, Lean or build."""
import ast,copy,importlib.util,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[1]
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
old=load('old_diagnostics',root/'scripts/roadmap-v15-bounded-diagnostics.py')
new=load('new_observe',root/'scripts/roadmap-v15-bounded-observe.py')
class ObserveTests(unittest.TestCase):
 def test_caps(self):self.assertEqual((new.CAP,new.RESERVE),(old.CAP,old.RESERVE))
 def test_decisions_identical(self):
  a=(root/'scripts/roadmap-v15-bounded-diagnostics.py').read_text();b=(root/'scripts/roadmap-v15-bounded-observe.py').read_text()
  for name in ['Lifecycle','namespace_pid','completed_workload','record_completion_snapshot']:
   x=next(n for n in ast.parse(a).body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name==name)
   y=next(n for n in ast.parse(b).body if isinstance(n,(ast.ClassDef,ast.FunctionDef)) and n.name==name)
   self.assertEqual(ast.get_source_segment(a,x),ast.get_source_segment(b,y))
 def test_run_only_adds_rejection_logging(self):
  def run(path):return next(n for n in ast.parse(path.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='run')
  a=run(root/'scripts/roadmap-v15-bounded-diagnostics.py');b=run(root/'scripts/roadmap-v15-bounded-observe.py')
  class Strip(ast.NodeTransformer):
   def visit_Try(self,n):
    if len(n.handlers)==1 and len(n.body)==1 and isinstance(n.body[0],ast.Assign) and len(n.handlers[0].body)==2:
     first,last=n.handlers[0].body
     if isinstance(first,ast.Expr) and isinstance(first.value,ast.Call) and isinstance(first.value.func,ast.Name) and first.value.func.id=='record_lifecycle_rejection':
      assert isinstance(last,ast.Raise) and last.exc is None and last.cause is None
      assert not n.orelse and not n.finalbody
      return n.body[0]
    return self.generic_visit(n)
  self.assertEqual(ast.dump(a,include_attributes=False),ast.dump(Strip().visit(b),include_attributes=False))
 def test_raw_failure_retained(self):
  events=[];snap={'Id':'a'*64,'State':{'Running':True,'Status':'running','Pid':42},'Config':{'Env':['SECRET=not-exported']}}
  original=copy.deepcopy(snap);top='PID ELAPSED RSS STAT COMMAND COMMAND\n99 0 0 X lean [lean]\n'
  new.record_lifecycle_rejection(events,'a'*64,snap,top,0,'Lean missing explicit -j1')
  self.assertEqual(events[0]['top'],top);self.assertEqual(events[0]['state']['Pid'],42)
  self.assertEqual(snap,original);self.assertNotIn('SECRET',str(events));self.assertNotIn('Env',str(events))
 def test_missing_snapshot_retained(self):
  events=[];new.record_lifecycle_rejection(events,'b'*64,None,None,1,'inspect unavailable')
  self.assertIsNone(events[0]['identity']);self.assertIsNone(events[0]['state']);self.assertEqual(events[0]['topExit'],1)
if __name__=='__main__':unittest.main(verbosity=2)
