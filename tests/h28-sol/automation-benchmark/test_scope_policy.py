import pathlib,subprocess,tempfile,unittest
from scope_policy import changed_paths,scope_violations,adoption_ancestry

class ScopePolicyTests(unittest.TestCase):
 def git(self,*args):
  return subprocess.check_output(['git',*args],cwd=self.root,text=True,stderr=subprocess.STDOUT).strip()
 def write(self,path,text):
  p=self.root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
 def commit(self,message):
  self.git('add','.');self.git('commit','-qm',message);return self.git('rev-parse','HEAD')
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(prefix='h28-scope-regression-');self.addCleanup(self.tmp.cleanup);self.root=pathlib.Path(self.tmp.name)
  self.git('init','-q');self.git('config','user.email','scope-test@example.invalid');self.git('config','user.name','Scope test')
  self.outside='Solidity/Calculus/Protected.lean';self.allowed='tests/h28-sol/automation-benchmark/owned.txt'
  self.write(self.outside,'protected original bytes\n');self.base=self.commit('base')
  self.write(self.allowed,'owned');self.previous=self.commit('owned predecessor')
  self.git('checkout','-qb','published',self.base);self.write('Solidity/Backend/Upstream.lean','published upstream');self.published=self.commit('published')
  self.git('update-ref','refs/remotes/origin/master',self.published);self.git('merge','--no-ff','-qm','adopt',self.previous);self.head=self.git('rev-parse','HEAD')
 def test_owned_delta_and_original_base_boundary(self):
  self.write(self.allowed,'new owned bytes');self.assertEqual(scope_violations(self.published,self.root),[])
  self.assertIn('Solidity/Backend/Upstream.lean',scope_violations(self.base,self.root))
 def test_outside_to_owned_rename_keeps_deleted_path(self):
  destination='tests/h28-sol/automation-benchmark/moved.lean';self.git('mv',self.outside,destination)
  self.assertIn(self.outside,changed_paths(self.published,self.root));self.assertIn(self.outside,scope_violations(self.published,self.root))
 def test_unstaged_outside_modification(self):
  self.write(self.outside,'modified');self.assertIn(self.outside,scope_violations(self.published,self.root))
 def test_staged_outside_modification(self):
  self.write(self.outside,'modified');self.git('add',self.outside);self.assertIn(self.outside,scope_violations(self.published,self.root))
 def test_unstaged_outside_deletion(self):
  (self.root/self.outside).unlink();self.assertIn(self.outside,scope_violations(self.published,self.root))
 def test_staged_outside_deletion(self):
  self.git('rm','-q',self.outside);self.assertIn(self.outside,scope_violations(self.published,self.root))
 def test_untracked_outside_rejected_owned_allowed(self):
  self.write('outside.txt','untracked');self.write('Solidity/Automation/H28/Allowed.lean','owned');self.assertEqual(scope_violations(self.published,self.root),['outside.txt'])
 def test_adoption_requires_all_ancestry(self):
  self.assertTrue(all(adoption_ancestry(self.published,self.previous,self.root).values()))
 def test_missing_published_ancestry(self):
  self.git('checkout','-q',self.previous);self.assertFalse(all(adoption_ancestry(self.published,self.previous,self.root).values()))
 def test_missing_predecessor_ancestry(self):
  self.git('checkout','-q',self.published);self.assertFalse(all(adoption_ancestry(self.published,self.previous,self.root).values()))
 def test_missing_remote_ancestry(self):
  self.git('update-ref','refs/remotes/origin/master',self.base);self.assertFalse(all(adoption_ancestry(self.published,self.previous,self.root).values()))

 def test_staged_outside_edit_restored_only_in_worktree(self):
  self.write(self.outside,'unauthorized staged bytes');self.git('add',self.outside)
  self.write(self.outside,'protected original bytes\n')
  self.assertNotIn(self.outside,self.git('diff','--no-renames','--name-only',self.published).splitlines())
  self.assertIn(self.outside,scope_violations(self.published,self.root))
