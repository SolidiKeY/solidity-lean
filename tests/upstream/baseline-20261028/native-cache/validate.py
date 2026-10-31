#!/usr/bin/env python3
"""Lightweight final checks; no build, Lean server or native replay rerun."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,time,subprocess
ROOT=Path(__file__).resolve().parents[4];OUT=Path(__file__).resolve().parent
COMMANDS=[
 ['python3','scripts/solidity-baseline-native-index.py','--check'],
 ['python3','scripts/solidity-baseline-native.test.py'],
 ['node','scripts/solidity-baseline-native-verify.mjs'],
 ['node','--check','scripts/solidity-baseline-native.mjs'],
 ['node','--check','scripts/solidity-baseline-native-boundaries.mjs'],
 ['bash','-n','scripts/run-solidity-baseline-native.sh'],
 ['node','--test','scripts/solidity-upstream.test.mjs'],
 ['python3','scripts/solidity-feature-audit.py','--check'],
 ['node','scripts/check-orphans.mjs'],['node','scripts/check-layers.mjs'],
 ['node','scripts/check-automatic.mjs','--strict'],['bash','scripts/check-trust.sh'],
 ['bash','scripts/check-doc-paths.sh'],['git','diff','--check'],['git','diff','--cached','--check'],
]
def main():
 os.chdir(ROOT);os.environ['LEAN_NUM_THREADS']='1';started=time.monotonic();rows=[]
 # Historical bytes are immutable; document hashes refer to their checkpoint.
 preserved=[]
 for name in ['gaps/gaps.json','attribution/index.json','probes/matrix.json','probes/evidence.tar.gz','portable-evidence.tar.gz','summary.json']:
  p=Path('tests/upstream/baseline-20261028')/name;data=p.read_bytes();old=subprocess.check_output(['git','show','c4a5a2f1:'+str(p)]);assert data==old;preserved.append(dict(path=str(p),sha256=hashlib.sha256(data).hexdigest(),byteIdenticalToStartingCommit=True))
 subprocess.run(['git','diff','--exit-code','c4a5a2f1','--','Solidity','Solidity.lean','lakefile.toml','docs/solidity-features.json','tests/upstream/results','tests/upstream/solidity-0.8.38.tar.gz'],check=True,stdout=subprocess.DEVNULL)
 for i,command in enumerate(COMMANDS):
  p=OUT/f'check-{i:02}.log';before=time.monotonic()
  with p.open('wb') as log:
   pid=os.fork()
   if pid==0:os.dup2(log.fileno(),1);os.dup2(log.fileno(),2);os.execvp(command[0],command)
   _,status,r=os.wait4(pid,0)
  code=os.waitstatus_to_exitcode(status);data=p.read_bytes();p.unlink()
  with gzip.GzipFile(filename=str(p)+'.gz',mode='wb',mtime=0) as z:z.write(data)
  row=dict(command=command,exitCode=code,elapsedSeconds=time.monotonic()-before,wait4MaxRssKiB=r.ru_maxrss,log=p.name+'.gz',uncompressedLogSha256=hashlib.sha256(data).hexdigest());expected=0
  if 'scripts/check-doc-paths.sh' in command:
   expected=1;original=gzip.decompress((ROOT/'tests/upstream/baseline-20261028/final-gates/doc-paths.log.gz').read_bytes());assert data==original;assert data.count(b'missing:')==20;row.update(historicalMissingReferences=20,originalDiagnosticsByteIdentical=True)
  rows.append(row);print(json.dumps(row),flush=True)
  if code!=expected:raise RuntimeError('unexpected gate exit')
 (OUT/'validation.json').write_text(json.dumps(dict(recordedAt=datetime.datetime.now(datetime.timezone.utc).isoformat(),commands=rows,elapsedSeconds=time.monotonic()-started,maxWait4JobRssKiB=max(r['wait4MaxRssKiB'] for r in rows),historicalFiles=preserved,historicalGeneratorNote='Prior document hashes are snapshot provenance; historical reproduction belongs at its recorded checkpoint. No old derived report regenerated.',resourceInterpretation='wait4 maximum is per reaped lightweight job, not aggregate cgroup peak. Actual native checks used12GiB/no-swap cgroups; metrics are archived logs/*.json.',nativeValidationComplete=False,remainingNativeCapability='nonzero-msg.value external-entry discriminator; proof listing is a separate stale Testing closure'),indent=2)+'\n')
if __name__=='__main__':main()
