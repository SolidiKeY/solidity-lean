#!/usr/bin/env python3
"""Published-source binding and narrow bridge negatives; no Lean/Docker execution."""
import pathlib,runpy,subprocess,types,sys,os,hashlib
from unittest.mock import patch
root=pathlib.Path('/workspace/v08-world-lowering-published')
n=runpy.run_path(str(root/'scripts/v08-image-access-run.py'),run_name='binding_tests')
f=n['verify_peer'];policy=f();assert len(policy['published_sources'])==124 and len(policy['private_v07_sources'])==0
count=0
def reject(action):
 global count
 try:action()
 except (AssertionError,subprocess.CalledProcessError):count+=1;return
 raise AssertionError('corruption accepted')
read=pathlib.Path.read_bytes
for target in [root/'scripts/v08-published-bindings.json',root/'Solidity/Backend/InternalFlow/RuntimeFrameInterfaceV3.lean',root/'Solidity/Lowering/P8/FrozenInterface.lean',root/'Solidity/Lowering/P8/FailureContractV2.lean',root/'Solidity/Lowering/P8/ResourceContractLaw1.lean',root/'Solidity/Lowering/P8b/Frozen.lean',root/'Solidity/Lowering/V07/Scalar.lean',root/'Solidity/Lowering/V07/SourceReads.lean']:
 with patch.object(pathlib.Path,'read_bytes',lambda p: read(p)+b' ' if p==target else read(p)):reject(f)
glob0=pathlib.Path.glob
def extra_private(p,pat):
 values=list(glob0(p,pat))
 if p==root/'Solidity/Lowering/V07':values.append(p/'PrivateRelay.lean')
 return iter(values)
with patch.object(pathlib.Path,'glob',extra_private):reject(f)
check=subprocess.check_output
for suffix in ['24149fd567ec273e5c72760ecf0a25a940c4c4fc:Solidity/Backend/InternalFlow/RuntimeFrameInterfaceV3.lean','24149fd567ec273e5c72760ecf0a25a940c4c4fc:Solidity/Lowering/V07/SourceReads.lean']:
 def bad(command,*a,**kw):
  if command[-1]==suffix:return 'bad\n' if kw.get('text') else b'bad'
  return check(command,*a,**kw)
 with patch.object(subprocess,'check_output',bad):reject(f)
glob=pathlib.Path.glob
def extra(p,pat):
 values=list(glob(p,pat))
 if p==root/'Solidity/Backend/InternalFlow':values.append(p/'ParallelRelay.lean')
 return iter(values)
with patch.object(pathlib.Path,'glob',extra):reject(f)
run=subprocess.run
def wrong_ancestry(command,*a,**kw):
 if 'merge-base' in command:raise subprocess.CalledProcessError(1,command)
 return run(command,*a,**kw)
with patch.object(subprocess,'run',wrong_ancestry):reject(f)
f();assert count==13
print('Published124/private0 positives;13 identity-corruption controls PASS')

# Caller holds the actual inherited writer descriptor9. Every rejection occurs
# before current-file metadata writes and before loading the bounded runner.
bridge=root/'scripts/v08-coord-file.py';current=pathlib.Path('/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt')
before=read(current);begin=count
for args in [['build','Solidity'],['env','lean','--tstack=262144',str(root/'Solidity/Lowering/V08/WorldImageAccess.lean')],['env','lean','--tstack=131072',str(root/'Solidity/Source/Eval.lean')]]:
 with patch.object(sys,'argv',[str(bridge),*args]):reject(lambda:runpy.run_path(str(bridge),run_name='negative_bridge'))
args=[str(bridge),'env','lean','--tstack=131072',str(root/'Solidity/Lowering/V08/WorldImageAccess.lean')]
with patch.object(sys,'argv',args),patch.dict(os.environ,{'V08_TOOL_LOCK_FD':'8'}):reject(lambda:runpy.run_path(str(bridge),run_name='negative_bridge'))
fstat=os.fstat
def other_inode(fd):
 s=fstat(fd)
 return types.SimpleNamespace(st_dev=s.st_dev,st_ino=s.st_ino+1) if fd==9 else s
with patch.object(sys,'argv',args),patch.object(os,'fstat',other_inode):reject(lambda:runpy.run_path(str(bridge),run_name='negative_bridge'))
symlink=pathlib.Path.is_symlink
with patch.object(sys,'argv',args),patch.object(pathlib.Path,'is_symlink',lambda p:True if p==root/'Solidity/Lowering/V08/WorldImageAccess.lean' else symlink(p)):reject(lambda:runpy.run_path(str(bridge),run_name='negative_bridge'))
assert count-begin==6 and read(current)==before
print('Six command/path/lease/symlink bridge negatives PASS; filename metadata unchanged; no Lean/Docker')
