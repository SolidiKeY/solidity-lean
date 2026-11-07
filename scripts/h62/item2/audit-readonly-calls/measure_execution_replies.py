#!/usr/bin/env python3
"""Measure native adapter classifier reuse; never rebaseline held Premises.

Alternate before/after source bytes at the same path with identical private
imports, compiler, flags and warm caches. Five matched pairs follow two warmups.
Run only inside the serial bounded runner. This is timing, not proof acceptance.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import statistics
import subprocess
import time

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('measure_execution_check',ROOT/'scripts/h62/item2/audit-readonly-calls/check_execution_replies.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


def run_checked(command, env, source, raw, log):
    """Seal the actual compiler input before/after, not just the intended buffer."""
    source.write_bytes(raw);digest=hashlib.sha256(raw).hexdigest()
    m.check.verify_hashes({str(source):digest});started=time.perf_counter()
    with log.open('wb') as stream:
        child=subprocess.Popen(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        _,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
    seconds=time.perf_counter()-started
    m.check.verify_hashes({str(source):digest})
    if child.returncode:raise ValueError('measurement Lean failure: '+str(log))
    return {'command':command,'seconds':seconds,'peak_rss_bytes':usage.ru_maxrss*1024,
            'exit':child.returncode,'source_sha256':digest,'log':str(log),'log_sha256':m.check.sha(log)}


def seal_logs(rows):
    m.check.verify_hashes({r['log']:r['log_sha256'] for r in rows})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['before','after','library','output']:parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    sources={label:getattr(args,label).read_bytes() for label in ['before','after']}
    for raw in sources.values():m.theorem_inventory(raw)
    pins={str(getattr(args,label).resolve()):hashlib.sha256(raw).hexdigest() for label,raw in sources.items()}
    receipt_path=args.library.resolve().parent/'receipt.json';rawreceipt=receipt_path.read_bytes();receipt=json.loads(rawreceipt)
    if receipt.get('target')!=m.TARGET:raise ValueError('wrong measurement dependency closure')
    order,current_pins=m.profile.closure(ROOT,[m.TARGET],{})
    if receipt.get('project_order')!=order or receipt['source_pins']!=current_pins:
        raise ValueError('measurement source/import graph mismatch')
    for relative,pin in receipt['source_pins'].items():
        source=ROOT/relative;artifact=args.library/(relative[:-5]+'.olean')
        pins[str(source)]=pin['source_sha256'];pins[str(artifact)]=receipt['artifacts'][relative]['artifact_sha256']
    for path,digest in receipt['protected_sha256'].items():
        if path.startswith(str(ROOT/'scripts')+'/'):pins[path]=digest
    pins[str(receipt_path)]=hashlib.sha256(rawreceipt).hexdigest()
    pins[str(m.check.LEAN)]=m.check.sha(m.check.LEAN)
    pins[str(Path(__file__).resolve())]=m.check.sha(Path(__file__).resolve())
    pins[str(ROOT/'scripts/h62/item2/audit-readonly-calls/check_execution_replies.py')]=m.check.sha(ROOT/'scripts/h62/item2/audit-readonly-calls/check_execution_replies.py')
    pins[str(ROOT/'lean-toolchain')]=m.check.sha(ROOT/'lean-toolchain')
    m.check.verify_hashes(pins)
    env=m.profile.isolated_environment(os.environ,args.library.resolve());source=out/'ExecutionReplies.lean'
    command=[str(m.check.LEAN),'-j1','--tstack=131072','--root='+str(out),str(source)]
    rows=[]
    def run(label,tag):
        row=run_checked(command,env,source,sources[label],out/(tag+'-'+label+'.log'))
        row.update(label=label,tag=tag);rows.append(row)
    for label in ['before','after']:run(label,'warm')
    for pair in range(5):
        for label in (['before','after'] if pair%2==0 else ['after','before']):run(label,str(pair))
    m.check.verify_hashes(pins)
    seal_logs(rows)
    medians={label:statistics.median(r['seconds'] for r in rows if r['label']==label and r['tag']!='warm')
             for label in sources}
    ratio=medians['after']/medians['before'];passed=ratio<=1.1
    result={'boundary':__doc__,'input_pins':pins,'runs':rows,'median_seconds':medians,
            'slowdown_percent':100*(ratio-1),'status':'pass' if passed else 'STOP',
            'library_boundary':'Caller-supplied receipt: current source/import graph and object byte hashes checked; this utility does not authenticate a dependency build or certify SDK source.',
            'historical_premises_stop_unchanged':True,'runtime_gate_pass':False}
    (out/'timing.json').write_text(json.dumps(result,indent=2)+'\n')
    print('ADAPTER_TIMING_'+('PASS' if passed else 'STOP')+' '+json.dumps(medians)+' delta='+str(result['slowdown_percent']))
    if not passed:raise SystemExit(2)


if __name__=='__main__':main()
