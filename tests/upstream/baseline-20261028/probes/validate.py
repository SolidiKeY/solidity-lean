#!/usr/bin/env python3
"""Final lightweight checks only. Does not start Lean or rerun diagnostics."""
import datetime,gzip,hashlib,json,os,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];OUT=Path(__file__).resolve().parent
COMMANDS=[
 ['python3','scripts/solidity-baseline-probe-index.py','--check'],
 ['python3','scripts/solidity-baseline-probe-index.test.py'],
 ['node','scripts/solidity-baseline-probe-verify.mjs'],
 ['node','--check','scripts/solidity-baseline-probe.mjs'],
 ['node','--check','scripts/solidity-baseline-reader-metadata.mjs'],
 ['bash','-n','scripts/run-solidity-baseline-probes.sh'],
 ['python3','scripts/solidity-baseline-attribution.py','--check'],
 ['python3','scripts/solidity-baseline-attribution.test.py'],
 ['python3','scripts/solidity-baseline.test.py'],
 ['python3','scripts/solidity-baseline-retries.test.py'],
 ['node','--test','scripts/solidity-upstream.test.mjs'],
 ['python3','scripts/solidity-feature-audit.py','--check'],
 ['node','scripts/check-orphans.mjs'],
 ['node','scripts/check-layers.mjs'],
 ['node','scripts/check-automatic.mjs','--strict'],
 ['bash','scripts/check-trust.sh'],
 ['bash','scripts/check-doc-paths.sh'],
 ['git','diff','--check'],['git','diff','--cached','--check'],
]
def main():
 os.chdir(ROOT);os.environ['LEAN_NUM_THREADS']='1';start=time.monotonic();rows=[]
 for i,command in enumerate(COMMANDS):
  path=OUT/f'check-{i:02}.log';before=time.monotonic()
  with path.open('wb') as log:
   pid=os.fork()
   if pid==0:
    os.dup2(log.fileno(),1);os.dup2(log.fileno(),2);os.execvp(command[0],command)
   _,status,usage=os.wait4(pid,0)
  data=path.read_bytes();path.unlink();code=os.waitstatus_to_exitcode(status);expected=1 if 'scripts/check-doc-paths.sh' in command else 0
  with gzip.GzipFile(filename=str(path)+'.gz',mode='wb',mtime=0) as z:z.write(data)
  row=dict(command=command,exitCode=code,elapsedSeconds=time.monotonic()-before,wait4MaxRssKiB=usage.ru_maxrss,log=path.name+'.gz',uncompressedLogSha256=hashlib.sha256(data).hexdigest())
  if 'scripts/check-doc-paths.sh' in command:
   original=gzip.decompress((ROOT/'tests/upstream/baseline-20261028/final-gates/doc-paths.log.gz').read_bytes());assert data==original;assert data.count(b'missing:')==20;row.update(historicalMissing=20,originalDiagnosticsByteIdentical=True)
  rows.append(row);print(json.dumps(row),flush=True)
  if code!=expected:raise RuntimeError('unexpected gate result')
 result=dict(recordedAt=datetime.datetime.now(datetime.timezone.utc).isoformat(),commands=rows,elapsedSeconds=time.monotonic()-start,maxWait4JobRssKiB=max(r['wait4MaxRssKiB'] for r in rows),resourceInterpretation='These are lightweight read-only Python/Node/shell checks; wait4 peak is per reaped job, not an aggregate cgroup peak. Actual Lean stage cgroup peaks/stops are in evidence.tar.gz logs/*.json.',nativeValidation='blocked, no new Lean job in these final checks',originalCoreAndCorpus='unchanged',newTheoremAxiomAudit='N/A; generated IO diagnostic wrappers add no semantic theorem or axiom. Static trust inventory only.')
 (OUT/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
