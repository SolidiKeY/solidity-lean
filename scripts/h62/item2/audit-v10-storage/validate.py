#!/usr/bin/env python3
"""Reproduce pinned prerequisite/dependency checks with off-Git evidence.
One command at a time, explicit Lean -j1 in the isolated Lake configuration.
Kill only this runner's process group on 12 GiB aggregate RSS or <4 GiB reserve.
Never use old artifacts, systemd-run, swap, or modify the frozen toolchain file.
Invoke through validate.sh, which acquires the required writer lock.
"""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import signal
import subprocess
import time

GIB = 1024**3

def memory():
    info = dict(line.split(":", 1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines())
    return int(info['MemAvailable'].split()[0])*1024, int(info['SwapTotal'].split()[0])*1024

def rss(pgid):
    total = 0
    for path in pathlib.Path('/proc').glob('[0-9]*/stat'):
        try:
            parts = path.read_text().rsplit(')', 1)[1].split()
            if int(parts[2]) == pgid: total += int(parts[21])*os.sysconf('SC_PAGE_SIZE')
        except (OSError, ValueError, IndexError): pass
    return total

def limits():
    resource.setrlimit(resource.RLIMIT_AS, (12*GIB, 12*GIB))

def run(cmd, name, output, env):
    available, swap = memory()
    if swap or available < 4*GIB: raise RuntimeError('resource prerequisite: swap must be zero and reserve >=4GiB')
    start = time.monotonic(); peak = 0; stopped = None
    with (output/(name+'.log')).open('w') as log:
        proc = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True, preexec_fn=limits)
        while proc.poll() is None:
            used = rss(proc.pid); peak = max(peak, used)
            available, swap = memory()
            if used > 12*GIB or available < 4*GIB or swap:
                stopped = 'resource guard'
                os.killpg(proc.pid, signal.SIGTERM)
                try: proc.wait(timeout=2)
                except subprocess.TimeoutExpired: pass
                try: os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                break
            time.sleep(.2)
        code = proc.wait(timeout=5)
    effective = code if code else (125 if stopped else 0)
    result = dict(command=cmd, exit=effective, child_exit=code, elapsed_seconds=time.monotonic()-start, peak_group_rss_bytes=peak, stopped=stopped)
    (output/(name+'.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
    return effective

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tools', type=pathlib.Path, default=pathlib.Path('/workspace/audit-v10-storage-tools'))
    ap.add_argument('--evidence', type=pathlib.Path, required=True)
    ap.add_argument('gate', choices=['prerequisite', 'dependencies'])
    a=ap.parse_args(); root=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
    os.chdir(root)
    evidence=a.evidence.resolve()
    if evidence==root or root in evidence.parents: ap.error('evidence must be outside checkout')
    evidence.mkdir(parents=True,exist_ok=True)
    pin=json.loads(pathlib.Path('/workspace/h62-coordinator-inputs/toolchain-pin.json').read_text())
    archive=a.tools/pin['asset']
    with archive.open('rb') as f: actual=hashlib.file_digest(f,'sha256').hexdigest()
    if actual != pin['sha256']: raise RuntimeError('official archive SHA256 mismatch')
    binary=a.tools/'lean-4.35.0-linux/bin'
    env=os.environ|{'PATH':str(binary)+':'+os.environ['PATH'],'LEAN_NUM_THREADS':'1','XDG_CACHE_HOME':str(evidence/'cache-v4.35.0')}
    if a.gate=='prerequisite':
        commands=[('lean-version',[str(binary/'lean'),'--version']),('lake-version',[str(binary/'lake'),'--version']),('keysort',[str(binary/'lean'),'-j1','--tstack=131072','Solidity/KeySort.lean'])]
    else:
        commands=[('dependencies',[str(binary/'lake'),'-f','scripts/h62/item2/audit-v10-storage/pinned-lakefile.toml','build','+Solidity.Backend.StorageOps.LoopLaws','+Solidity.Backend.StorageOps.TargetOperations','+Solidity.Lowering.StorageOps.SourceWordReadControls'])]
    for name,cmd in commands:
        code=run(cmd,name,evidence,env)
        if code: return code
    return 0

if __name__=='__main__': raise SystemExit(main())
