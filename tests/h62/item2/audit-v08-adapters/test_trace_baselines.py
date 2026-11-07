"""Guard Git provenance against unchecked deletions, merges and foreign targets."""
import importlib.util, pathlib, subprocess, tempfile, unittest
ROOT = pathlib.Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location('trace_baselines', ROOT/'scripts/h62/item2/audit-v08-adapters/trace_baselines.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
PATH = 'Solidity/Test.lean'

class Trace(unittest.TestCase):
 def repo(self, folder):
  r = pathlib.Path(folder)
  subprocess.run(['git','init','-q','-b','work',str(r)],check=True)
  subprocess.run(['git','-C',str(r),'config','user.name','trace-test'],check=True)
  subprocess.run(['git','-C',str(r),'config','user.email','trace-test@example.invalid'],check=True)
  (r/'Solidity').mkdir(); (r/PATH).write_text('a\nb\nc\n')
  return r
 def git(self,r,*args):return subprocess.check_output(['git','-C',str(r),*args],stderr=subprocess.DEVNULL,text=True).strip()
 def commit(self,r):
  self.git(r,'add','.');self.git(r,'commit','-qm','fixture');return self.git(r,'rev-parse','HEAD')
 def test_replacement_and_pure_deletion_trace_actual_edges(self):
  with tempfile.TemporaryDirectory() as t:
   r=self.repo(t);base=self.commit(r);(r/PATH).write_text('a\nnew\nc\n');change=self.commit(r)
   (r/PATH).write_text('new\nc\n');target=self.commit(r)
   report=m.trace(r,base,target,target,[PATH]);self.assertTrue(report['all_traced'])
   h=report['files'][0]['hunks'][0]
   self.assertEqual(set(h['deletion_edge_commits']),{change,target})
   self.assertEqual(h['surviving_introduction_edge_commits'],[change])
 def test_merge_introduction_and_original_blame_are_distinct(self):
  with tempfile.TemporaryDirectory() as t:
   r=self.repo(t);base=self.commit(r);self.git(r,'checkout','-qb','feature')
   (r/PATH).write_text('a\nbranch\nc\n');feature=self.commit(r)
   self.git(r,'checkout','-q','work');(r/'other.txt').write_text('independent');self.commit(r)
   self.git(r,'merge','--no-ff','-qm','merge-fixture','feature');target=self.git(r,'rev-parse','HEAD')
   report=m.trace(r,base,target,target,[PATH]);self.assertTrue(report['all_traced'])
   h=report['files'][0]['hunks'][0]
   self.assertEqual(h['surviving_introduction_edge_commits'],[target])
   self.assertEqual(h['target_blame_commits'],[feature])
 def test_target_not_on_master_is_rejected(self):
  with tempfile.TemporaryDirectory() as t:
   r=self.repo(t);base=self.commit(r);(r/PATH).write_text('a\nforeign\nc\n');target=self.commit(r)
   with self.assertRaises(ValueError):m.trace(r,base,target,base,[PATH])
 def test_invalid_replay_is_rejected(self):
  a=[dict(text='a\n',introduced='base',base_line=1)]
  with self.assertRaises(ValueError):m.advance(a,['different\n'],[],'commit',{})

unittest.main()
