#!/usr/bin/env python3
"""Recheck owned proofs serially; run from Bridge after pinned input setup.

No external package build, cache download, re-pin or shared registration write.
Each Lean child is monitored by run-file.py: -j1, <=12 GiB RSS, zero swap,
>=4 GiB available reserve. The checkout writer lock covers the entire run.
"""
from pathlib import Path
import fcntl,hashlib,json,os,re,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[3]
BRIDGE=ROOT/'Bridge'; TESTS=BRIDGE/'tests/precompile-agreement'; EVIDENCE=TESTS/'evidence'
PROOFS=BRIDGE/'SolidityBridge/PrecompileAgreement'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run():
 os.chdir(BRIDGE)
 env={**os.environ,'LEAN_NUM_THREADS':'1'}
 subprocess.run([str(ROOT/'scripts/coord-tools/lean-mcp'),'stop'],cwd=ROOT,env=env,check=True,stdout=subprocess.DEVNULL)
 subprocess.run(['git','status','--porcelain'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 sources={str(p.relative_to(ROOT)) for p in PROOFS.glob('*.lean')}
 sources |= {'scripts/check-precompile-agreement.py'}
 sources |= {'Bridge/tests/precompile-agreement/'+p for p in
   ('Acceptance.lean','Axioms.lean','AllDeclarations.lean','ActualAxioms.lean','BoundaryVectors.lean',
    'required-coverage.json','declarations.json','axiom-pins.json','inventory.json','run-file.py','verify.py')}
 initial={p:sha(ROOT/p) for p in sources}
 logs={}
 for name in ('Bytes','Identity','Gas','Header','Controls','Acceptance','Axioms','BoundaryVectors','AllDeclarations','ActualAxioms'):
  module=name in ('Bytes','Identity','Gas','Header','Controls')
  source=('SolidityBridge/PrecompileAgreement/' if module else 'tests/precompile-agreement/')+name+'.lean'
  log=EVIDENCE/(name+'-kernel.log')
  cmd=[sys.executable,str(TESTS/'run-file.py'),source,str(log)]
  if module:cmd+=['.lake/build/lib/lean/SolidityBridge/PrecompileAgreement/'+name+'.olean']
  result=subprocess.run(cmd,env=env,stdout=subprocess.DEVNULL)
  decisive=log.read_text().splitlines()[-1];print(name+': '+decisive,flush=True)
  if result.returncode:raise SystemExit(result.returncode)
  if 'warning:' in log.read_text():raise RuntimeError('Owned-file warning in '+name)
  logs[log.name]=sha(log)
 if initial!={p:sha(ROOT/p) for p in sources}:raise RuntimeError('sources changed during kernel gate')
 report=(EVIDENCE/'ActualAxioms-kernel.log').read_text()
 found={}
 for m in re.finditer(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",report,re.M):
  found[m[1]]=sorted([] if m[2] is None else [v.strip() for v in m[2].split(',')])
 if found!=json.loads((TESTS/'axiom-pins.json').read_text()):raise RuntimeError('actual axiom sets differ from explicit pins')
 receipt={'status':'pass','time_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
   'pre_commit_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
   'lean':subprocess.check_output(['lean','--version'],env=env,text=True).strip(),
   'lake':subprocess.check_output(['lake','--version'],env=env,text=True).strip(),
   'sources':initial,'inputs':json.loads((TESTS/'inventory.json').read_text())['pins'],
   'logs':logs,'input_build_sha256':sha(EVIDENCE/'pinned-input-build.log')}
 (EVIDENCE/'kernel-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 subprocess.run([sys.executable,str(ROOT/'scripts/check-precompile-agreement.py')],cwd=ROOT,env=env,check=True)
 print('BOUNDED_PRECOMPILE_KERNEL_GATE_PASS; central/full runtime gates remain separate',flush=True)
if __name__=='__main__':
 lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock');lock.parent.mkdir(parents=True,exist_ok=True)
 with lock.open('a') as writer:
  fcntl.flock(writer,fcntl.LOCK_EX)
  run()
