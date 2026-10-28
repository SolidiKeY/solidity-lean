import subprocess,time,json
from pathlib import Path
out=Path('/workspace/solidity-lean/.lake/transient-step8')
assert Path('/sys/fs/cgroup/memory.max').read_text().strip()=='12884901888'
assert Path('/sys/fs/cgroup/memory.swap.max').read_text().strip()=='0'
commands=[('staged-diff',['git','diff','--cached','--check']),('inventory-final',['python3','scripts/solidity-feature-audit.py','--check']),('orphans-final',['node','scripts/check-orphans.mjs']),('layers-final',['node','scripts/check-layers.mjs']),('automatic-final',['node','scripts/check-automatic.mjs','--strict']),('trust-final',['bash','scripts/check-trust.sh']),('doc-paths-final',['bash','scripts/check-doc-paths.sh'])]
for label,cmd in commands:
 start=time.monotonic()
 with (out/(label+'.log')).open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 row=dict(label=label,command=cmd,exit=p.returncode,elapsed_seconds=time.monotonic()-start,cgroup_peak_bytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()),cgroup_events=Path('/sys/fs/cgroup/memory.events').read_text())
 with (out/'static-final.ndjson').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
