import subprocess,time,json,datetime
from pathlib import Path
out=Path('/workspace/solidity-lean/.lake/transient-step8')
policy={n:Path('/sys/fs/cgroup/'+n).read_text().strip() for n in ['memory.max','memory.swap.max']}
assert policy=={'memory.max':'12884901888','memory.swap.max':'0'},policy
(out/'remaining-policy.json').write_text(json.dumps(policy,indent=2)+'\n')
lake='/workspace/.setup/tools/lean-4.24.0-linux/bin/lake'
lean=[lake,'-f','lakefile.transient.toml','env','lean','-j1','--tstack=131072']
commands=[
 ('baseline-both',lean+['.lake/transient-step8/BaselineWorldImport.lean']),
 ('core-final',lean+['Solidity/Semantics/TransientWorld.lean']),
 ('source-final',lean+['Solidity/Examples/Tactics/TransientWorldSource.lean']),
 ('axioms-final',lean+['.lake/transient-step8/AxiomAudit.lean']),
 ('reference-final',['node','scripts/check-transient-world-vectors.mjs','/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js','/workspace/.setup/transient-reference/node_modules']),
]
for label,cmd in commands:
 start=time.monotonic()
 with (out/(label+'.log')).open('w') as f: p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 row=dict(label=label,command=cmd,exit=p.returncode,elapsed_seconds=time.monotonic()-start,
 finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),cgroup_peak_bytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()),cgroup_events=Path('/sys/fs/cgroup/memory.events').read_text())
 with (out/'remaining-gates.ndjson').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
