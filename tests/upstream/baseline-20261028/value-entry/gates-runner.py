import json,subprocess,time,resource,hashlib,gzip
from pathlib import Path
out=Path('tests/upstream/baseline-20261028/value-entry');records=[]
commands=[['python3','scripts/solidity-baseline-value-entry-audit.py','--out',str(out/'audit.json')],['python3','scripts/solidity-baseline-native-index.py','--check'],['python3','scripts/solidity-baseline-native.test.py'],['node','scripts/solidity-baseline-native-verify.mjs'],['node','--test','scripts/solidity-upstream.test.mjs'],['python3','scripts/solidity-feature-audit.py','--check'],['node','scripts/check-orphans.mjs'],['node','scripts/check-layers.mjs'],['node','scripts/check-automatic.mjs','--strict'],['bash','scripts/check-trust.sh'],['bash','scripts/check-doc-paths.sh'],['git','diff','--check']]
for i,cmd in enumerate(commands):
 start=time.monotonic();p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);r=resource.getrusage(resource.RUSAGE_CHILDREN);name=f'gate-{i:02}.log.gz';(out/name).write_bytes(gzip.compress(p.stdout,mtime=0));records.append(dict(command=cmd,exitCode=p.returncode,elapsedSeconds=time.monotonic()-start,cumulativeChildrenMaxRssKiB=r.ru_maxrss,log=name,uncompressedSha256=hashlib.sha256(p.stdout).hexdigest()));print(i,p.returncode,cmd,flush=True)
 if p.returncode and cmd!=['bash','scripts/check-doc-paths.sh']:break
(out/'commands.json').write_text(json.dumps(dict(commands=records,memoryMetric='RUSAGE_CHILDREN cumulative child maximum RSS; not aggregate cgroup peak',noLeanNoBuild=True),indent=2)+'\n')
