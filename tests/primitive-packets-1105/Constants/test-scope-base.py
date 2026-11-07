#!/usr/bin/env python3
"""Master advances are inherited; lane and working-tree foreign changes are refused."""
import pathlib,runpy,subprocess,tempfile
ns=runpy.run_path(str(pathlib.Path(__file__).with_name('check.py')))
with tempfile.TemporaryDirectory(prefix='numeric-scope-base-') as td:
 root=pathlib.Path(td)
 def git(*args):return subprocess.check_output(['git',*args],cwd=root,stderr=subprocess.PIPE,text=True).strip()
 def commit(path,text):
  target=root/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text)
  git('add','--',path);git('commit','-qm',text)
 def reject():
  try:ns['validate_scope'](ns['current_scope_changes'](root))
  except AssertionError:return
  raise AssertionError('foreign change escaped scope guard')
 git('init','-q');git('config','user.email','scope-test@example.invalid');git('config','user.name','Scope test')
 commit('Solidity/Foreign.lean','baseline');git('branch','lane')
 git('checkout','-qb','upstream');commit('Solidity/Upstream.lean','published upstream')
 git('update-ref','refs/remotes/origin/master','HEAD')
 git('checkout','-q','lane');commit('tests/primitive-packets-1105/Constants/owned.txt','lane change')
 git('merge','--no-edit','upstream')
 changes=ns['current_scope_changes'](root)
 assert changes=={'tests/primitive-packets-1105/Constants/owned.txt'},changes
 ns['validate_scope'](changes)
 foreign=root/'Solidity/Foreign.lean';foreign.write_text('unstaged foreign');reject()
 git('add','Solidity/Foreign.lean');reject();git('restore','--staged','Solidity/Foreign.lean');git('restore','Solidity/Foreign.lean')
 untracked=root/'Solidity/Untracked.lean';untracked.write_text('untracked foreign');reject();untracked.unlink()
 git('mv','Solidity/Foreign.lean','tests/primitive-packets-1105/Constants/renamed.txt');reject()
 git('commit','-qm','unauthorized lane rename');reject()
print('PASS: advanced master merge accepted; unstaged, staged, untracked, renamed and committed lane foreign changes refused')
