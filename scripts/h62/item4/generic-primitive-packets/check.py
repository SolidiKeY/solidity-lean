#!/usr/bin/env python3
"""Serial official-v4.35 compiler fallback when Lean MCP is unavailable.

No v4.24 cache is used. Produces isolated dependency artifacts and per-file
logs, fail-fast at the first failed prerequisite. Run under the writer lock.
The 300-second limit applies per source, without changing proof options.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time
import sys
from census import ROOT, masked
from runtime import memory_cap, guard, bound, sha


def closure(modules):
    visited, active, ordered = set(), set(), []
    def visit(name):
        if name in visited:
            return
        path = ROOT/(name.replace('.', '/')+'.lean')
        if not path.is_file():
            # Official distribution modules are resolved by Lean itself.
            if name.split('.')[0] in ('Init', 'Lean', 'Std', 'Lake'):
                return
            raise ValueError(f'missing local dependency {name}')
        if name in active:
            raise ValueError(f'import cycle at {name}')
        active.add(name)
        for line in masked(path.read_text()).splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    visit(dep)
        active.remove(name)
        visited.add(name)
        ordered.append(name)
    for module in modules:
        visit(module)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--pin', type=Path, default=Path('/workspace/h62-coordinator-inputs/toolchain-pin.json'))
    parser.add_argument('--list', action='store_true')
    parser.add_argument('modules', nargs='+')
    args = parser.parse_args()
    modules = closure(args.modules)
    if args.list:
        print('\n'.join(modules))
        return
    evidence = args.evidence.resolve()
    (evidence/'dependency-status.json').write_text(json.dumps(dict(status='pending',roots=args.modules))+'\n')
    (evidence/'dependency-results.json').write_text('[]\n')
    pin = json.loads(args.pin.read_text())
    if pin['toolchain'] != 'leanprover/lean4:v4.35.0':
        raise ValueError('unexpected toolchain pin')
    archive = evidence/'toolchain'/pin['asset']
    if hashlib.file_digest(archive.open('rb'),'sha256').hexdigest() != pin['sha256']:
        raise ValueError('official archive checksum mismatch')
    binary = evidence/'toolchain'/pin['asset'].removesuffix('.tar.zst')/'bin'/'lean'
    build = evidence/'build'
    logs = evidence/'dependency-logs'
    logs.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(build))
    cap = memory_cap()
    records = []
    for name in modules:
        guard(cap)
        source = ROOT/(name.replace('.', '/')+'.lean')
        output = build/(name.replace('.', '/')+'.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(name+'.log')
        cmd = [str(binary), '-j1','--tstack=131072','-o',str(output),str(source)]
        start = time.monotonic()
        with log.open('w') as stream:
            try:
                result = subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT,
                                        timeout=300,preexec_fn=bound(cap))
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 124
        record = dict(module=name, command=cmd, exit=code, seconds=time.monotonic()-start,
                      memory_cap_bytes=cap, log=str(log), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
        record['output_sha256'] = sha(output) if code == 0 else None
        records.append(record)
        (evidence/'dependency-results.json').write_text(json.dumps(records,indent=2)+'\n')
        print(f'{name}: exit={code} seconds={record["seconds"]:.3f}',flush=True)
        if code:
            (evidence/'dependency-status.json').write_text(json.dumps(dict(status='blocked',module=name,exit=code,roots=args.modules))+'\n')
            output.unlink(missing_ok=True)
            raise SystemExit(code if code > 0 else 1)
    (evidence/'dependency-status.json').write_text(json.dumps(dict(status='pass',roots=args.modules))+'\n')
    print('AFFECTED_DEPENDENCIES_PASS')


if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        if '--evidence' in sys.argv and '--list' not in sys.argv and not (isinstance(error,SystemExit) and error.code == 0):
            evidence=Path(sys.argv[sys.argv.index('--evidence')+1])
            (evidence/'dependency-status.json').write_text(json.dumps(dict(status='blocked',error=str(error)))+'\n')
        raise
