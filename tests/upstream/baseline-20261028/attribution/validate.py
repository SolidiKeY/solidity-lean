#!/usr/bin/env python3
"""Run sequential read-only diagnostic gates; archive exact exit/log/rusage.

No Lean/compiler process is invoked. Max RSS is wait4's per-reaped-job statistic,
not kernel cgroup peak or a claim of aggregate process-group peak. The historical
cold-build measurement remains separate and unchanged.
"""
import datetime,gzip,hashlib,json,os,resource,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
COMMANDS=[
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
 ['git','diff','--check'],
 ['git','diff','--cached','--check'],
]
def main():
 os.chdir(ROOT);os.environ['LEAN_NUM_THREADS']='1';started=time.monotonic();rows=[]
 for i,command in enumerate(COMMANDS):
  # Isolate wait4 accounting for each job. Output is losslessly gzipped to
  # avoid duplicated historical citations becoming new documentation references.
  path=OUT/f'gate-{i:02}.log';start=time.monotonic()
  with path.open('wb') as log:
   pid=os.fork()
   if pid==0:
    os.dup2(log.fileno(),1);os.dup2(log.fileno(),2)
    os.execvp(command[0],command)
   _,status,usage=os.wait4(pid,0)
  elapsed=time.monotonic()-start;code=os.waitstatus_to_exitcode(status);data=path.read_bytes()
  with gzip.GzipFile(filename=str(path)+'.gz',mode='wb',mtime=0) as z:z.write(data)
  path.unlink()
  expected=1 if 'scripts/check-doc-paths.sh' in command else 0
  # The path gate's twenty historical missing references remain blocked.
  doc_missing=data.count(b'missing:')
  if 'scripts/check-doc-paths.sh' in command:
   previous=gzip.decompress((ROOT/'tests/upstream/baseline-20261028/final-gates/doc-paths.log.gz').read_bytes())
   if data!=previous: raise RuntimeError('documentation diagnostics drifted from original checkpoint')
   if doc_missing!=20: raise RuntimeError('expected exactly20 historical missing references')
  row=dict(command=command,exitCode=code,expectedExitCode=expected,elapsedSeconds=elapsed,
   wait4MaxRssKiB=usage.ru_maxrss,userSeconds=usage.ru_utime,systemSeconds=usage.ru_stime,
   log=path.name+'.gz',uncompressedLogSha256=hashlib.sha256(data).hexdigest())
  if 'scripts/check-doc-paths.sh' in command: row.update(historicalMissingReferences=doc_missing,originalDiagnosticLogByteIdentical=True)
  rows.append(row);print(json.dumps({k:v for k,v in row.items() if k!='historicalDiagnosticLog'}),flush=True)
  if code!=expected: raise RuntimeError('unexpected gate result '+repr(command))
 x=json.loads((OUT/'index.json').read_text())
 result=dict(recordedAt=datetime.datetime.now(datetime.timezone.utc).isoformat(),startingCommit='66629757c15a819af17bb2d97e18c9bea4777351',
 commands=rows,totalSequentialGateSeconds=time.monotonic()-started,maxWait4JobRssKiB=max(r['wait4MaxRssKiB'] for r in rows),
 resourceInterpretation='Lightweight Python/Node/shell read-only checks only. wait4 job maximum RSS is not an aggregate cgroup peak; no Lean build/server/compiler/EVM execution, no memory or proof limits changed.',
 assessmentCounts=x['assessmentCounts'],immutableInputs=x['provenance'],
 historicalCold=dict(exitCode=124,completedTargets=546,totalTargets=685,peakCgroupBytes=8195923968),warm='unrun; not retried',
 missingAssignedValidation='25 feature-specific evidence-needed rows and15 additional documentary-boundary reproduction/assurance questions are explicit in index.json. Diagnostic review of all84 is complete; semantic attribution is not claimed complete.',
 theoremAxiomChecks='N/A: no Lean declarations changed. Static trust inventory gate only; existing proof claims are source citations, not new kernel checking.',
 sharedFilesEdited=['docs/coverage-plan.md','docs/solidity-upstream-tests.md','tests/upstream/baseline-20261028/README.md'])
 # Keep diagnostic text only inside the compressed log; don't recursively add
 # the old missing citations as fresh checked prose in a new JSON file.
 for r in result['commands']:r.pop('historicalDiagnosticLog',None)
 (OUT/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
