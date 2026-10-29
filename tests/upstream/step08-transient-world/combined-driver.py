import subprocess,time,json,datetime
from pathlib import Path
out=Path('/workspace/solidity-lean/.lake/transient-step8')
meta={name:Path('/sys/fs/cgroup/'+name).read_text().strip() for name in ['memory.max','memory.swap.max','memory.current','memory.peak']}
(out/'cgroup-policy.json').write_text(json.dumps(meta,indent=2)+'\n')
assert meta['memory.max']=='12884901888' and meta['memory.swap.max']=='0',meta
commands=[
 ('full-cgroup',['bash','./run-lean.sh']),
 ('node-tests-final',['node','--test','scripts/contract-world.test.mjs','scripts/transient-storage.test.mjs','scripts/solidity-upstream.test.mjs']),
]
for label,path in [
 ('upstream-constructor','test/libsolidity/semanticTests/constructor/transient_state_variable_initialization.sol'),
 ('upstream-frames','test/libsolidity/semanticTests/getters/transient_value_types_multi_frame_call.sol'),
 ('upstream-tuple','test/libsolidity/semanticTests/variables/transient_state_variable_tuple_assignment.sol')]:
 commands.append((label,['node','scripts/solidity-upstream.mjs','run','--compiler','/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js','--filter',path,'--batch-size','1','--out',str(out/label)]))
for label,cmd in commands:
 start=time.monotonic()
 with (out/(label+'.log')).open('w') as f:
  proc=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 row=dict(label=label,command=cmd,exit=proc.returncode,elapsed_seconds=time.monotonic()-start,
  finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  cgroup_peak_bytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()),
  cgroup_events=Path('/sys/fs/cgroup/memory.events').read_text())
 with (out/'cgroup-gates.ndjson').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
