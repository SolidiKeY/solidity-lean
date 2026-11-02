#!/usr/bin/env python3
"""External runner controls; no Lean builds or source edits."""
import importlib.util, io, subprocess, sys, signal
from pathlib import Path
sys.dont_write_bytecode = True
root=Path(__file__).resolve().parent.parent
def load(name, filename):
 spec=importlib.util.spec_from_file_location(name,root/'scripts'/filename)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
g=load('graph','v08-build-graph.py');c=load('cleanup','v08-container-cleanup.py')
assert g.header_imports('/- import Bad /- nested -/ -/\nimport Solidity.A -- comment\n/- more -/\nimport Solidity.B\ndef x := "import Bad"')==['Solidity.A','Solidity.B']
graph=g.SourceGraph(root);order=graph.closure(['Solidity.Tools.LatexTerm'])
assert 'LeanTeX' in order and 'LeanTeX.Basic' in order
assert str(graph.source('LeanTeX')).endswith('vendor/LeanTeX/LeanTeX.lean')
for module in order:
 for dep in graph.imports(module):
  if graph.source(dep): assert order.index(dep)<order.index(module)
try: graph.closure(['Nonexistent.Target'])
except ValueError: pass
else: raise AssertionError('missing target accepted')
def scenario(replies,expected,operations):
 calls=[]
 def fake(args,**kwargs):
  calls.append(args[0]);value=replies.pop(0)
  assert kwargs['env']=={'SAFE':'1'}
  if value=='timeout': raise subprocess.TimeoutExpired(args,1)
  return subprocess.CompletedProcess(args,0,value)
 assert c.ensure_stopped([], 'owned','token',io.StringIO(),run=fake,env={'SAFE':'1'})==expected
 assert calls==operations and not replies
scenario(['false token'],(True,False),['inspect'])
scenario(['true token','','false token'],(True,True),['inspect','stop','inspect'])
scenario(['true token','timeout','true token','','false token'],(True,True),['inspect','stop','inspect','kill','inspect'])
scenario(['true foreign'],(False,False),['inspect'])
scenario(['timeout'],(False,False),['inspect'])
assert 'signal.signal(signal.SIGTERM, signal.SIG_IGN)' in (root/'scripts/v08-bounded.py').read_text()
# Cleanup is bounded and ignores repeated termination requests during finally.
old=signal.signal(signal.SIGTERM, signal.SIG_IGN)
try:
 signal.raise_signal(signal.SIGTERM)
 scenario(['true token','','false token'],(True,True),['inspect','stop','inspect'])
finally: signal.signal(signal.SIGTERM,old)
calls=[]
def absent(args,**kwargs):
 calls.append(args[0]);return subprocess.CompletedProcess(args,1,'Error: No such object: owned')
assert c.ensure_stopped([], 'owned','token',io.StringIO(),run=absent)==(True,False)
assert calls==['inspect']
print('PASS: vendored dependency order, header comments, missing target, five ownership/cleanup controls')
