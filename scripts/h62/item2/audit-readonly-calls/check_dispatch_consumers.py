#!/usr/bin/env python3
"""Guard migrated consumers being certified from changed statements or warm noise.

Compile only four fixed consumers against current imported objects. Premises is
imported from cache, never rebuilt or timed. This gate is not a full dependency
recertification and cannot clear the original held Premises workload.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import time

import dispatch_v2_audit as audit
ROOT=audit.census.ROOT
COMPILER=Path("/workspace/.setup/tools/lean-4.24.0-linux/bin/lean")



def header_view(root,name):
    previous=audit.census.ROOT
    try:
        audit.census.ROOT=root
        rows=audit.census.declarations(name)
    finally:audit.census.ROOT=previous
    result={row["source_name"]:{key:row[key] for key in ("signature_sha256","variable_context","visibility")} for row in rows}
    if len(result)!=len(rows):raise ValueError("duplicate consumer declaration")
    return result


def check_headers(before,after,names):
    counts={}
    for name in names:
        old=header_view(before,name);new=header_view(after,name)
        if old!=new:raise ValueError("consumer statement/context drift: "+name)
        counts[name]=len(old)
    return counts


def main():
    if not audit.MIGRATED:
        raise ValueError("empty migrated consumer scope")
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);p.add_argument("--before",required=True);args=p.parse_args()
    if not args.output.is_absolute():p.error("output must be absolute")
    args.output.mkdir(mode=0o700,exist_ok=False)
    records=[];sources={}
    held_source=ROOT/'Solidity/Backend/WorldCalls/Premises.lean';held_artifact=ROOT/'.lake/build/lib/lean/Solidity/Backend/WorldCalls/Premises.olean'
    held_before={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (held_source,held_artifact)}
    for label in ('before','after'):
        sources[label]={}
        for name in audit.MIGRATED:
            raw=subprocess.check_output(['git','show',args.before+':'+name],cwd=ROOT) if label=='before' else (ROOT/name).read_bytes()
            target=args.output/label/'sources'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);target.chmod(0o444)
            sources[label][name]=hashlib.sha256(raw).hexdigest()
    retained_headers=check_headers(args.output/"before/sources",args.output/"after/sources",audit.MIGRATED)
    # Lean resolves a package root before its leaf: a sparse Solidity overlay
    # shadows the cached package. Link its unchanged leaves, excluding every
    # migrated module/companion so compiler output cannot follow a cache link.
    cache=ROOT/'.lake/build/lib/lean'
    excluded=[name[:-5] for name in audit.MIGRATED]
    for label in ('before','after'):
        library=args.output/label/'library'
        for path in (cache/'Solidity').rglob('*'):
            if not path.is_file():continue
            relative=path.relative_to(cache).as_posix()
            if any(relative.startswith(name+'.') for name in excluded):continue
            target=library/relative;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(path.resolve())
    for iteration in range(6):
        for label in (('before','after') if iteration%2==0 else ('after','before')):
            source_root=args.output/label/'sources';library=args.output/label/'library'
            env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(library)+':'+os.environ.get('LEAN_PATH',''))
            for index,name in enumerate(audit.MIGRATED):
                artifact=library/(name[:-5]+'.olean');artifact.parent.mkdir(parents=True,exist_ok=True)
                command=[str(COMPILER),'-j1','--tstack=131072','--root='+str(source_root),'-o',str(artifact),str(source_root/name)]
                log=args.output/f'{iteration}-{label}-{index}.log'
                with log.open('w') as stream:
                    start=time.monotonic();child=subprocess.Popen(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
                    _,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
                records.append({'iteration':iteration,'label':label,'file':name,'command':command,'exit':child.returncode,'seconds':time.monotonic()-start,'rss_kib':usage.ru_maxrss,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
                (args.output/'samples.json').write_text(json.dumps(records,indent=2)+'\n')
                if child.returncode:raise SystemExit('CONSUMER_CHECK_FAIL: '+str(log))
    comparisons=[]
    for name in audit.MIGRATED:
        med={label:statistics.median(r['seconds'] for r in records if r['file']==name and r['label']==label and r['iteration']) for label in ('before','after')}
        rss={label:max(r['rss_kib'] for r in records if r['file']==name and r['label']==label) for label in ('before','after')}
        comparisons.append({'file':name,'median_seconds':med,'peak_rss_kib':rss,'delta_percent':100*(med['after']/med['before']-1)})
    if held_before!={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (held_source,held_artifact)}:raise SystemExit('HELD_CACHE_CHANGED')
    result={'retained_headers':retained_headers,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'held_cache_snapshot':held_before,'sources':sources,'comparisons':comparisons,'checks':len(records),'boundary':__doc__,'before':args.before}
    (args.output/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
    if any(r['delta_percent']>10 for r in comparisons):raise SystemExit('SLOWDOWN_STOP')


if __name__=='__main__':main()
