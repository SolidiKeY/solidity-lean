#!/usr/bin/env python3
"""Serial bounded checking of generated audit declarations, without budget changes."""
import argparse,json,os,sys
from pathlib import Path
from bounded import run
ap=argparse.ArgumentParser()
ap.add_argument('--generated',type=Path,required=True)
ap.add_argument('--resume',action='store_true')
ap.add_argument('--lean',type=Path,default=Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean'))
a=ap.parse_args();a.generated=a.generated.resolve()
e=a.generated.parent;cache=e.parent/'olean'
os.environ['LEAN_NUM_THREADS']='1';os.environ['LEAN_PATH']=str(cache)
paths=[a.generated/'EmptyWitnesses.lean',a.generated/'NegativeWitnesses.lean']
paths += [Path(p) for p in json.loads((a.generated/'batches.json').read_text())]
previous=[]
if a.resume:
    for line in (a.generated/'metrics.jsonl').read_text().splitlines():
        record=json.loads(line)
        if record['exit'] or record['stop_reason'] or not record['clean_diagnostics']:break
        previous.append(record)
    for i,record in enumerate(previous):
        assert record['command'][-1]==str(paths[i])
        assert record['source_sha256']==__import__('hashlib').sha256(paths[i].read_bytes()).hexdigest()
        artifact=cache/(paths[i].stem+'.olean')
        assert artifact.exists()
        record['current_olean_sha256']=__import__('hashlib').sha256(artifact.read_bytes()).hexdigest()
    (a.generated/'resume-prefix.json').write_text(json.dumps(previous,indent=2)+'\n')
    (a.generated/'metrics.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in previous))
with (a.generated/'metrics.jsonl').open('a' if a.resume else 'w') as metrics:
    for index,source in enumerate(paths):
        if index < len(previous):continue
        r=run([str(a.lean),'-j1','-DElab.async=false','--tstack=131072','--root='+str(a.generated),'-o',str(cache/(source.stem+'.olean')),str(source)],a.generated/(source.stem+'.log'))
        r['source_sha256']=__import__('hashlib').sha256(source.read_bytes()).hexdigest()
        text=Path(r['log']).read_text()
        r['clean_diagnostics']=not any(token in text for token in ['PANIC','error:','sorryAx'])
        metrics.write(json.dumps(r)+'\n');metrics.flush()
        print(source.name,'exit',r['exit'],'seconds',round(r['wall_seconds'],2),flush=True)
        if r['exit'] or r['stop_reason'] or not r['clean_diagnostics']:raise SystemExit(1)
print('PASS all generated driver checks; unresolved search rows remain unproved',flush=True)
