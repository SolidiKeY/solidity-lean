#!/usr/bin/env python3
"""Paired file-group timings; prerequisite failures never produce a speed delta.

Supply the full affected before/after file groups, including extracted helpers.
This harness does not prove that a caller-supplied scope is complete. Final
run-lean.sh and semantic acceptance are separate mandatory gates.
Run under the repository writer lock, after check.py passes all affected imports.
"""
import argparse
import json
import os
from pathlib import Path
import statistics
import subprocess
import time
from census import ROOT
from runtime import compiler, memory_cap, guard, bound, fingerprint, sha


def measure(args, report, save):
    evidence=args.evidence.resolve()
    dependency=json.loads((evidence/'dependency-status.json').read_text())
    if dependency['status'] != 'pass':
        raise ValueError('affected dependency build has not passed')
    for row in json.loads((evidence/'dependency-results.json').read_text()):
        if row['exit'] != 0 or sha(Path(row.get('source_path',str(ROOT/(row['module'].replace('.','/')+'.lean'))))) != row['source_sha256'] or sha(evidence/'build'/(row['module'].replace('.','/')+'.olean')) != row['output_sha256']:
            raise ValueError('dependency evidence is failed or stale')
    dependency_sources={row.get('source_path',str(ROOT/(row['module'].replace('.','/')+'.lean'))):row['source_sha256'] for row in json.loads((evidence/'dependency-results.json').read_text())}
    dependency_roots={row.get('source_path',str(ROOT/(row['module'].replace('.','/')+'.lean'))):row.get('source_root',str(ROOT)) for row in json.loads((evidence/'dependency-results.json').read_text())}
    binary,pin=compiler(evidence)
    build=evidence/'build'
    env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(build))
    groups={key:[p.resolve() for p in getattr(args,key)] for key in ('before','after')}
    if groups['before'] == groups['after']:
        raise ValueError('identical file groups are not a migration comparison')
    hashes={**dependency_sources,**{str(p):sha(p) for paths in groups.values() for p in paths}}
    snapshot=fingerprint(build)
    cap=memory_cap()
    report.update(snapshot=snapshot,toolchain=pin,source_sha256=hashes,memory_cap_bytes=cap,
                  boundary='explicit file groups; full affected-scope completeness is a separate review obligation')
    save()
    def unchanged():
        if fingerprint(build) != snapshot or any(sha(Path(p)) != h for p,h in hashes.items()):
            raise ValueError('HEAD, tree contents, inputs, or import artifacts changed')
    for pair in range(-1,args.repetitions):
        for key in (('before','after') if pair % 2 == 0 else ('after','before')):
            unchanged()
            guard(cap)
            total=0
            for index,source in enumerate(groups[key]):
                guard(cap)
                log=evidence/f'timing-{pair}-{key}-{index}.log'
                if not source.is_relative_to(ROOT) and str(source) not in dependency_roots:
                    raise ValueError('external timing input needs a validated source root')
                source_root=dependency_roots.get(str(source),str(ROOT))
                cmd=[str(binary),'-j1','--tstack=131072','--root='+source_root,str(source)]
                start=time.monotonic()
                with log.open('w') as stream:
                    try:
                        code=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=300,preexec_fn=bound(cap)).returncode
                    except subprocess.TimeoutExpired:
                        code=124
                seconds=time.monotonic()-start
                total+=seconds
                report['records'].append(dict(pair=pair,warmup=pair<0,variant=key,source=str(source),command=cmd,exit=code,seconds=seconds,log=str(log)))
                save()
                if code:
                    raise ValueError('baseline or migration check failed')
            report['pairs'].append(dict(pair=pair,warmup=pair<0,variant=key,seconds=total))
            unchanged()
            save()
    medians={key:statistics.median(r['seconds'] for r in report['pairs'] if r['variant']==key and not r['warmup']) for key in groups}
    report['medians_seconds']=medians
    report['delta_percent']=(medians['after']/medians['before']-1)*100
    report['status']='fail-slowdown' if medians['after'] > medians['before']*1.1 else 'pass'
    save()
    print(json.dumps(report,indent=2))
    return 0 if report['status']=='pass' else 1


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence',type=Path,required=True)
    parser.add_argument('--before',type=Path,nargs='+',required=True)
    parser.add_argument('--after',type=Path,nargs='+',required=True)
    parser.add_argument('--repetitions',type=int,default=3)
    args=parser.parse_args()
    report=dict(status='pending',delta_percent=None,records=[],pairs=[])
    path=args.evidence/'timings.json'
    def save():
        path.write_text(json.dumps(report,indent=2)+'\n')
    save()
    try:
        if args.repetitions < 3:
            raise ValueError('at least three alternating pairs required')
        code=measure(args,report,save)
    except Exception as error:
        report.update(status='blocked',error=str(error),delta_percent=None)
        save()
        raise
    raise SystemExit(code)


if __name__=='__main__':
    main()
