import json,subprocess,time,resource,gzip,hashlib,os,tarfile
from pathlib import Path
out=Path('tests/upstream/baseline-20261028/value-runtime');logs=out/'checks';logs.mkdir(exist_ok=False);records=[]
cmds=[(['python3','scripts/solidity-baseline-value-verify.py','.lake/upstream/value-entry-runtime-20261028','--out',str(logs/'verification.json')],0),(['python3','-c',"from pathlib import Path; [compile(Path(p).read_text(),p,'exec') for p in ['scripts/solidity-baseline-lifetime-root.py','scripts/solidity-baseline-value-runtime.py','scripts/solidity-baseline-value-verify.py']]; print('syntax pass')"],0),(['bash','-n','scripts/run-solidity-baseline-value.sh'],0),(['python3','scripts/solidity-baseline-native-index.py','--check'],0),(['python3','scripts/solidity-baseline-native.test.py'],0),(['node','scripts/solidity-baseline-native-verify.mjs'],0),(['node','--test','scripts/solidity-upstream.test.mjs'],0),(['python3','scripts/solidity-feature-audit.py','--check'],0),(['node','scripts/check-orphans.mjs'],0),(['node','scripts/check-layers.mjs'],0),(['node','scripts/check-automatic.mjs','--strict'],0),(['bash','scripts/check-trust.sh'],0),(['bash','scripts/check-doc-paths.sh'],1),(['git','diff','--check'],0),(['git','diff','--exit-code','29b73d0e','--','Solidity','Solidity.lean','lakefile.toml','docs/solidity-features.json','docs/solidity-feature-inventory.md','tests/upstream/baseline-20261028/gaps','tests/upstream/baseline-20261028/attribution','tests/upstream/baseline-20261028/probes','tests/upstream/baseline-20261028/native-cache','tests/upstream/baseline-20261028/value-entry','tests/upstream/results','tests/upstream/solidity-0.8.38.tar.gz'],0)]
for i,(cmd,want) in enumerate(cmds):
 start=time.monotonic();p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);name=f'gate-{i:02}.log.gz';(logs/name).write_bytes(gzip.compress(p.stdout,mtime=0));records.append(dict(command=cmd,exitCode=p.returncode,expectedExitCode=want,elapsedSeconds=time.monotonic()-start,cumulativeChildrenMaxRssKiB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,log='checks/'+name,uncompressedSha256=hashlib.sha256(p.stdout).hexdigest()));print(i,p.returncode,flush=True)
 if p.returncode!=want:break
ledger=json.load(open(out/'archive.json'));archive=out/ledger['path'];assert hashlib.sha256(archive.read_bytes()).hexdigest()==ledger['sha256']
with tarfile.open(archive,'r:gz') as tf:
 seen={}
 for m in tf:
  assert m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
  data=tf.extractfile(m).read();seen[m.name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 assert seen==ledger['files']
prior=Path('tests/upstream/baseline-20261028/native-cache');old=next(c for c in json.load(open(prior/'validation.json'))['commands'] if c['command']==['bash','scripts/check-doc-paths.sh'])
assert gzip.decompress((prior/old['log']).read_bytes())==gzip.decompress((logs/'gate-12.log.gz').read_bytes())
x=dict(commands=records,archiveRegularFilesVerified=len(seen),docPathOutputUnchanged=True,noLeanOrBuildInFinalGates=True,cgroupPeakBytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()),memoryMaxBytes=int(Path('/sys/fs/cgroup/memory.max').read_text()),swapMaxBytes=int(Path('/sys/fs/cgroup/memory.swap.max').read_text()),memoryEvents=Path('/sys/fs/cgroup/memory.events').read_text())
(out/'validation.json').write_text(json.dumps(x,indent=2)+'\n');assert len(records)==len(cmds) and all(c['exitCode']==c['expectedExitCode'] for c in records)
