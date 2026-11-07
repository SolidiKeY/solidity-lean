#!/usr/bin/env python3
"""Check adoption boundaries in a temporary Git index; never edit foreign source."""
import os,pathlib,runpy,subprocess,tempfile
root=pathlib.Path(__file__).resolve().parents[2]
ns=runpy.run_path(str(root/'scripts/check-sol-numeric-literals.py'))
published=ns['ADOPTED_MASTER'];validate=ns['validate_foreign_paths']
validate(['AGENTS.md'],set(),published)
with tempfile.TemporaryDirectory(prefix='numeric-adoption-') as directory:
 env=dict(os.environ,GIT_INDEX_FILE=directory+'/index')
 def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=root,env=env,input=input)
 git('read-tree',published)
 blob=git('hash-object','-w','--stdin',input=b'not the approved upstream instructions\n').decode().strip()
 git('update-index','--add','--cacheinfo','100644',blob,'AGENTS.md')
 tree=git('write-tree').decode().strip()
 try:validate(['AGENTS.md'],set(),tree)
 except ValueError as e:assert 'differs from adopted publication' in str(e)
 else:raise AssertionError('foreign edit was accepted as inherited upstream')
 # A published addition disappears from the original-base diff when deleted.
 git('read-tree',published)
 added='docs/feature-work/integration-20261105-checkpoints.md'
 assert subprocess.run(['git','cat-file','-e',ns['BASE']+':'+added],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0
 git('update-index','--force-remove',added)
 deleted_tree=git('write-tree').decode().strip()
 assert added not in git('diff','--name-only',ns['BASE'],deleted_tree,'--').decode().splitlines()
 assert added in ns['changed_paths'](deleted_tree)
 try:validate([added],set(),deleted_tree)
 except ValueError as e:assert 'differs from adopted publication' in str(e)
 else:raise AssertionError('deleted inherited foreign addition bypassed scope')
 # A genuine upstream modification reverted to BASE also vanishes there.
 git('read-tree',published)
 modified='scripts/coord-tools/handoff.sh'
 old_blob=git('rev-parse',ns['BASE']+':'+modified).decode().strip()
 assert old_blob!=git('rev-parse',published+':'+modified).decode().strip()
 git('update-index','--cacheinfo','100755',old_blob,modified)
 reverted_tree=git('write-tree').decode().strip()
 assert modified not in git('diff','--name-only',ns['BASE'],reverted_tree,'--').decode().splitlines()
 assert modified in ns['changed_paths'](reverted_tree)
 try:validate([modified],set(),reverted_tree)
 except ValueError as e:assert 'differs from adopted publication' in str(e)
 else:raise AssertionError('foreign reversion to BASE bypassed scope')

try:validate(['outside-scope-new-file'],{'outside-scope-new-file'})
except ValueError as e:assert 'untracked foreign write' in str(e)
else:raise AssertionError('untracked foreign edit was accepted')
validate(['AGENTS.md'],set())
print('Adoption controls: published bytes accepted; foreign edits, inherited deletion, reversion to BASE and untracked foreign path rejected; checkout untouched')
