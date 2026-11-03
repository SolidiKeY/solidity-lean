#!/usr/bin/env python3
"""Narrow shared-tool lake adapter: real Lean in the unchanged bounded runtime."""
import os,sys,pathlib,fcntl,runpy
root=pathlib.Path('/workspace/v08-world-lowering-published')
evidence=pathlib.Path('/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102')
assert os.environ.get('V08_TOOL_LOCK_FD')=='9'
expected=pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').stat()
actual=os.fstat(9);assert (actual.st_dev,actual.st_ino)==(expected.st_dev,expected.st_ino)
fcntl.flock(9,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert len(sys.argv)==5 and sys.argv[1:4]==['env','lean','--tstack=131072'],'only exact gate.sh per-file command'
file=pathlib.Path(sys.argv[4]);file=file if file.is_absolute() else root/file
assert not file.is_symlink();file=file.resolve()
assert file in [root/'Solidity/Lowering/V08/WorldImageAccess.lean',root/'Solidity/Lowering/V08/WorldImageAccessControls.lean',root/'Solidity/Lowering/V08/SourceClockTransactions.lean',root/'Solidity/Lowering/V08/LocalCallableTransport.lean'] and file.is_file()
(evidence/'coord-access/current-file.txt').write_text(str(file)+'\n')
previous={p.name for p in evidence.glob('run-*')}
runner=root/'scripts/v08-coord-file-run.py';sys.argv=[str(runner)]
n=runpy.run_path(str(runner),run_name='bounded_shared_file');code=n['run']()
new=[p for p in evidence.glob('run-*') if p.name not in previous];assert len(new)==1
log=new[0]/'build.log'
if log.exists():sys.stdout.write(log.read_text())
sys.exit(code)
