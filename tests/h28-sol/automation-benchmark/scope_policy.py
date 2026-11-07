"""Strict lane paths and Git ancestry; no upstream wildcard exclusions."""
import subprocess

def lines(cwd,*args):
 return subprocess.check_output(['git',*args],cwd=cwd,text=True).splitlines()

def changed_paths(reference,cwd):
 # Rename destinations alone can hide unauthorized source deletions.
 working=lines(cwd,'diff','--no-renames','--name-only',reference,'--')
 staged=lines(cwd,'diff','--cached','--no-renames','--name-only',reference,'--')
 return sorted(set(working+staged))

def untracked_paths(cwd):
 return lines(cwd,'ls-files','--others','--exclude-standard')

def allowed_path(path):
 return path.startswith('Solidity/Automation/H28/') or path.startswith('tests/h28-sol/automation-benchmark/') or path=='docs/feature-work/h28-automation-benchmark.md'

def scope_violations(reference,cwd):
 return [p for p in changed_paths(reference,cwd)+untracked_paths(cwd) if not allowed_path(p)]

def adoption_ancestry(published,previous,cwd):
 def ancestor(a,b):
  return subprocess.run(['git','merge-base','--is-ancestor',a,b],cwd=cwd,capture_output=True).returncode==0
 return {published+' ancestor of HEAD':ancestor(published,'HEAD'),previous+' ancestor of HEAD':ancestor(previous,'HEAD'),'published ancestor of origin/master':ancestor(published,'origin/master')}
