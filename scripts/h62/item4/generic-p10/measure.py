#!/usr/bin/env python3
"""Predeclared five-pair checking-time gate for the single-file owner proposal.

Same v4.24 MCP process/import cache/resources; all original controls, helper
proofs and trust commands included. Fresh equal-length namespaces force fresh
body elaboration. This measures elaboration/kernel checking, not native code
generation. Never overwrite a completed timing run or cherry-pick retries.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import statistics
import subprocess
import time
from export_migration import owner_source, wrapped
from bounded import process_table, process_tree, signal_owned
from accept_semantics import require_success


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def backend(repo):
    status=subprocess.check_output(['scripts/coord-tools/lean-mcp','status'],cwd=repo,text=True,timeout=15).strip()
    match=re.fullmatch(r'pid=(\d+) server=(\d+) socket=(\S+)',status)
    if not match: raise ValueError(f'MCP backend is not idle/identified: {status}')
    daemon,server=int(match[1]),int(match[2])
    table=process_table()
    if daemon not in table or server not in table: raise ValueError('MCP backend exited')
    command=(Path('/proc')/str(server)/'cmdline').read_bytes().split(b'\0')
    if str(repo/'scripts/h62/item4/generic-p10/bounded.py').encode() not in command:
        raise ValueError('refuse an MCP backend outside this lane resource guard')
    owned,_,_=process_tree(-1,{server:table[server]['started']})
    watchdogs=[]
    for pid,started in owned.items():
        try: args=(Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0')
        except OSError: continue
        if b'--server' in args and b'--worker' not in args: watchdogs.append([pid,started])
    if len(watchdogs)!=1: raise ValueError('require one prewarmed Lean watchdog before timing')
    return dict(daemon_pid=daemon,daemon_started=table[daemon]['started'],
        server_pid=server,server_started=table[server]['started'],socket=match[3],
        server_command_sha256=hashlib.sha256(b'\0'.join(command)).hexdigest(),
        lean_watchdogs=sorted(watchdogs))


def quiesce(identity,output):
    """Timeout kills a CLI only; stop its identity-checked lane MCP guard too."""
    pid,started=identity['server_pid'],identity['server_started']
    current=process_table().get(pid)
    if current is None or current['started']!=started:
        (output/'quiescence.json').write_text(json.dumps(dict(stopped=False,reason='guard identity lost; no unrelated process signaled'))+'\n')
        raise SystemExit('BLOCKED: cannot verify MCP guard identity; no further heavy gates')
    known,_,_=process_tree(-1,{pid:started})
    signal_owned({pid:started},signal.SIGTERM)
    deadline=time.monotonic()+10
    live=set()
    while time.monotonic()<deadline:
        known,live,_=process_tree(-1,known)
        if not live: break
        time.sleep(0.1)
    if live:
        signal_owned(known,signal.SIGKILL)
        time.sleep(0.2)
        known,live,_=process_tree(-1,known)
    # The repository daemon can remain idle with a dead stdio backend. Stop
    # only its captured identity, so a later session cannot reuse that socket.
    daemon_stopped=None
    if not live and 'daemon_pid' in identity:
        daemon=identity['daemon_pid']; daemon_start=identity['daemon_started']
        signal_owned({daemon:daemon_start},signal.SIGTERM)
        deadline=time.monotonic()+2
        while time.monotonic()<deadline:
            row=process_table().get(daemon)
            if row is None or row['started']!=daemon_start or row['state']=='Z': break
            time.sleep(.1)
        row=process_table().get(daemon)
        daemon_stopped=row is None or row['started']!=daemon_start or row['state']=='Z'
    (output/'quiescence.json').write_text(json.dumps(dict(stopped=not live and daemon_stopped is not False,remaining_owned_pids=sorted(live),daemon_stopped=daemon_stopped),indent=2)+'\n')
    if live or daemon_stopped is False: raise SystemExit('BLOCKED: own MCP worker not quiescent; no further heavy gates')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[4])
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--recover-from',type=Path,help='only an incomplete failed warmup with no measured samples')
    args=parser.parse_args()
    repo,output=args.repo.resolve(),args.output.resolve()
    if not output.is_relative_to(repo.parent/'generic-p10-artifacts'): parser.error('timings must remain in this lane artifact directory')
    if output.exists() and any(output.iterdir()): parser.error('preserve existing timing run; do not retry to obtain a pass')
    output.mkdir(parents=True,exist_ok=True)
    if os.environ.get('LEAN_NUM_THREADS')!='1' or os.environ.get('LEAN_MCP_SCRATCH_SLOTS')!='1':
        parser.error('require the serial runtime environment')
    compiler=os.environ['GENERIC_P10_LEAN_EXE']
    version=subprocess.check_output([compiler,'--version'],text=True).strip()
    if not version.startswith('Lean (version 4.24.0,'): parser.error('wrong toolchain')
    before,after=owner_source(repo)
    identity=backend(repo)
    sources={'before':before,'after':after}
    order=[['before','after'],['after','before'],['before','after'],['after','before'],['before','after']]
    plan=dict(metric='ratio of median wall times; stop if after/before > 1.10',pairs=5,
        driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        committed_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
        warmups=['before','after'],order=order,tool='lean_run_code',version=version,
        conditions='same guarded MCP process; warm identical native imports; fresh equal-length namespace every trial; single scratch slot; explicit -j1; full original 32 declarations plus proposed helpers; trust commands retained',
        boundary='Lean elaboration/kernel checking only; no native compilation or whole-repository timing claim',
        before_sha256=sha(before),after_sha256=sha(after),backend_identity=identity,
        scope='one existing BYTE control module; all original21public propositions retained')
    if args.recover_from:
        previous=args.recover_from.resolve()
        old=json.loads((previous/'plan.json').read_text())
        oldruns=json.loads((previous/'runs.json').read_text())
        if (previous/'result.json').exists() or not oldruns or any(not row.get('warmup') for row in oldruns):
            parser.error('recovery cannot discard any measured sample or completed verdict')
        for key in ['metric','pairs','warmups','order','before_sha256','after_sha256']:
            if old[key]!=plan[key]: parser.error(f'recovery changed frozen timing input: {key}')
        plan['infrastructure_recovery']=dict(previous=str(previous),previous_plan_sha256=hashlib.sha256((previous/'plan.json').read_bytes()).hexdigest(),
            reason='incomplete warmup after import-header transition; fresh dedicated backend and explicit identical-header priming; no measured samples discarded')
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    (output/'before.lean').write_text(before)
    (output/'after.lean').write_text(after)
    # Prime this exact header before changing only body namespaces. Lean4.24
    # restarts file workers on import-header changes; that path is not timed.
    prime='import SolidityBridge.RoadmapV15.P10.ByteObservation\n#check SolidityBridge.RoadmapV15.P10.byte_fetched\n'
    try:
        preflight=subprocess.run(['scripts/coord-tools/lean-mcp','call','lean_run_code',json.dumps(dict(code=prime))],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    except subprocess.TimeoutExpired as error:
        (output/'header-prime-timeout.log').write_bytes(error.stdout or b'')
        quiesce(identity,output)
        raise SystemExit('STOP: common-header priming timeout; no samples or verdict')
    (output/'header-prime.json').write_bytes(preflight.stdout)
    try:
        if preflight.returncode: raise ValueError('header priming transport failed')
        require_success(json.loads(preflight.stdout))
    except (ValueError,UnicodeDecodeError):
        quiesce(identity,output)
        raise SystemExit('STOP: common-header priming failed; no timing acceptance')
    if backend(repo)!=identity:
        quiesce(identity,output)
        raise SystemExit('STOP: backend changed during priming')
    print('common-header priming PASS; fixed backend identity; no measured samples yet',flush=True)
    runs=[]
    def trial(variant,index,warmup=False):
        if backend(repo)!=identity: raise SystemExit('STOP: MCP backend changed before trial; no mixed-cache acceptance')
        prefix=f'Timing{index:06d}'
        code=wrapped(sources[variant],prefix)
        command=['scripts/coord-tools/lean-mcp','call','lean_run_code',json.dumps({'code':code})]
        start=time.monotonic()
        try:
            result=subprocess.run(command,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
        except subprocess.TimeoutExpired as error:
            (output/f'{index:02d}-{variant}-timeout.log').write_bytes(error.stdout or b'')
            runs.append(dict(variant=variant,index=index,warmup=warmup,proof_success=False,reason='300s client timeout'))
            (output/'runs.json').write_text(json.dumps(runs,indent=2)+'\n')
            quiesce(identity,output)
            raise SystemExit('STOP: checking timeout; own MCP workers quiesced; no timing pass')
        seconds=time.monotonic()-start
        path=output/f'{index:02d}-{variant}.json'
        path.write_bytes(result.stdout)
        try: report=json.loads(result.stdout)
        except (ValueError,UnicodeDecodeError):
            (output/'invalid-report.json').write_text(json.dumps(dict(index=index,variant=variant,reason='invalid/incomplete MCP result'))+'\n')
            quiesce(identity,output)
            raise SystemExit('STOP: incomplete MCP report; own workers quiesced')
        try:
            require_success(report)
            errors=[d for d in report['diagnostics'] if d.get('severity')=='error']
            passed=result.returncode==0 and not errors
        except ValueError: passed=False
        row=dict(variant=variant,index=index,warmup=warmup,seconds=seconds,code_sha256=sha(code),
                 proof_success=passed,evidence=str(path))
        runs.append(row)
        (output/'runs.json').write_text(json.dumps(runs,indent=2)+'\n')
        print(f'{index:02d} {variant} {seconds:.6f}s proof_success={passed} warmup={warmup}',flush=True)
        if not passed:
            quiesce(identity,output)
            raise SystemExit('STOP: semantic/checking failure; timing gate not accepted')
        current=backend(repo)
        if current!=identity:
            (output/'backend-change.json').write_text(json.dumps(dict(expected=identity,actual=current),indent=2)+'\n')
            quiesce(identity,output)
            raise SystemExit('STOP: MCP backend changed during trial; no mixed-cache acceptance')
    trial('before',0,True)
    trial('after',1,True)
    index=2
    for pair in order:
        for variant in pair:
            trial(variant,index)
            index+=1
    old=statistics.median(r['seconds'] for r in runs if not r['warmup'] and r['variant']=='before')
    new=statistics.median(r['seconds'] for r in runs if not r['warmup'] and r['variant']=='after')
    slowdown=100*(new/old-1)
    passed=new/old<=1.10
    summary=dict(status='pass' if passed else 'fail',before_median_seconds=old,
        after_median_seconds=new,slowdown_percent=slowdown,limit_percent=10,
        plan_sha256=hashlib.sha256((output/'plan.json').read_bytes()).hexdigest(),
        original_cases=21,original_declarations=32,new_helpers=8,
        boundary=plan['boundary'],required_next_action='owner relay still required' if passed else 'STOP refactor; preserve originals and report slowdown')
    (output/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)
    raise SystemExit(0 if passed else 2)


if __name__=='__main__':main()
