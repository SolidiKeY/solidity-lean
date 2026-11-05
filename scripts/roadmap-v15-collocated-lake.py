#!/usr/bin/env python3
"""Serial build route using the same pinned SDK's co-located Lake/Lean.
No process monitor or toolchain file is changed. Production always uses the
existing bounded monitor to execute Lake; the host planner never executes Lean.
The pinned package weakLeanArgs retain explicit-j1; the existing monitor still
rejects any missing flag, extra worker, unknown identity or expired process.
"""
import os,re,sys,shlex,subprocess
from pathlib import Path
SDK=Path('/workspace/.setup/tools/lean-4.24.0-linux')
ROOT=Path('/workspace/solidity-lean-v15-p10-help')
RUNTIME=Path('/workspace/v15-evm-agreement-evidence/metadata-push-20261103/runtime-H21')

def plan(args,cwd,environment,read=lambda p:p.read_text()):
    args=list(args)
    while args and args[0].startswith('-j'):
        flag=args.pop(0)
        if flag=='-j':
            if not args or args.pop(0)!='1':raise ValueError('only one worker allowed')
        elif flag!='-j1':raise ValueError('only one worker allowed')
    cwd=Path(cwd)
    if cwd==ROOT:cfg=RUNTIME/'core.toml';extra=[]
    elif cwd==ROOT/'Bridge':
        cfg=RUNTIME/'bridge.toml';extra=['--packages='+str(RUNTIME/'package-overrides.json')]
    else:raise ValueError('unsupported checkout')
    if not args:raise ValueError('command required')
    allowed=(args==['--version'] or args==['env','/bin/true'] or
        (args[0]=='build' and len(args)>1 and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_.:]*',x) for x in args[1:])))
    if not allowed:raise ValueError('unsupported command/flag')
    text=read(cfg)
    if not text.splitlines() or text.splitlines()[0]!='weakLeanArgs = ["-j1", "--tstack=131072"]':
        raise ValueError('unchanged serial/stack package configuration required')
    env=dict(environment);env['LEAN_NUM_THREADS']='1';env['LAKE_OVERRIDE_LEAN']='false'
    env.pop('LEAN_SYSROOT',None);env.pop('LEAN',None)
    command=[str(SDK/'bin/lake'),'--no-cache','-f',str(cfg),*extra,*args]
    return command,env

def main():
    if len(sys.argv)<4:raise SystemExit('usage: route EVIDENCE LABEL -j1 COMMAND ...')
    evidence,label,*args=sys.argv[1:]
    if not Path(evidence).is_absolute():raise ValueError('absolute evidence path required')
    command,env=plan(args,Path.cwd(),os.environ)
    # Only the old guarded runner executes native code. No unguarded/dry-run
    # production path is provided, and its barrier and terminal checks stay intact.
    shell=('unset LEAN_SYSROOT LEAN; export LAKE_OVERRIDE_LEAN=false LEAN_NUM_THREADS=1; '
        +'cd '+shlex.quote(str(Path.cwd()))+'; timeout 300 '+shlex.join(command))
    runner=Path(__file__).with_name('roadmap-v15-bounded-pidfd.py')
    return subprocess.run([sys.executable,str(runner),evidence,label,shell]).returncode
if __name__=='__main__':raise SystemExit(main())
