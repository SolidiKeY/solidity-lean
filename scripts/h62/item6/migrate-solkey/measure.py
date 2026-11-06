#!/usr/bin/env python3
"""Bounded serial clean source compilation of the assigned import closure.

No Lake cache is read. Each dependency is built once in topological order with
explicit -j1. This narrow timing gate does not replace run-lean.sh final gates.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time
from census import census

GIB = 1024**3

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--toolchain', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--timeout', type=int, default=1800)
    a = p.parse_args()
    root, out = a.root.resolve(), a.out.resolve()
    if out.exists(): raise SystemExit('Refusing reused output: clean runs require a new path')
    out.mkdir(parents=True)
    lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if Path('/proc/swaps').read_text().count('\n') != 1: raise SystemExit('Swap is configured')
    data = census(root)
    identity = {m['source']: {'source_sha256': m['source_sha256'], 'fixtures': m['fixtures']} for m in data['modules']}
    identity.update({v['source']: v['sha256'] for v in data['external_dependency_closure'].values() if v is not None})
    identity_hash = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    (out/'census.json').write_text(json.dumps(data, indent=2)+'\n')
    deps = data['external_dependency_closure']
    names = [m['source'][:-5].replace('/', '.') for m in data['modules']]
    graph = {m: d['imports'] for m, d in deps.items() if d is not None}
    graph.update({n: m['imports'] for n, m in zip(names, data['modules'])})
    order, visiting, done = [], set(), set()
    def visit(n):
        if n in done or n not in graph: return
        if n in visiting: raise ValueError('cyclic imports: '+n)
        visiting.add(n)
        for dep in graph[n]: visit(dep)
        visiting.remove(n); done.add(n); order.append(n)
    visit('Solidity.KeySort')
    for n in names: visit(n)
    # KeySort is deliberately first even if a future import graph changes.
    if 'Solidity.KeySort' not in order: order.insert(0, 'Solidity.KeySort')
    lean = str(a.toolchain.resolve()/'bin/lean')
    versions = {exe: subprocess.check_output([str(a.toolchain.resolve()/'bin'/exe), '--version'], text=True).strip() for exe in ('lean','lake')}
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(out/'lib'))
    results = []
    start = time.monotonic()
    peak = 0
    def cap():
        resource.setrlimit(resource.RLIMIT_AS, (12*GIB, 12*GIB))
        os.setsid()
    def headroom():
        current = int(Path('/sys/fs/cgroup/memory.current').read_text())
        maximum = int(Path('/sys/fs/cgroup/memory.max').read_text())
        available = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))) * 1024
        return current, min(maximum-current, available) >= 4*GIB
    for n in order:
        if not headroom()[1]: raise SystemExit('RESOURCE_RESERVE_STOP before launch')
        source = root/(n.replace('.', '/')+'.lean')
        dest = out/'lib'/(n.replace('.', '/')+'.olean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        cmd = [lean, '-j1', '--tstack=131072', '--root='+str(root), '-o', str(dest), str(source)]
        t = time.monotonic(); reason = None
        with (out/(n+'.log')).open('w') as log:
            child = subprocess.Popen(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=cap)
            while child.poll() is None:
                current, enough = headroom()
                peak = max(peak, current)
                if not enough: reason = 'RESOURCE_RESERVE_STOP'
                if time.monotonic()-t > a.timeout: reason = 'TIMEOUT_STOP'
                if reason:
                    os.killpg(child.pid, signal.SIGTERM)
                    try: child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=5)
                    break
                time.sleep(.25)
        results.append({'module': n, 'command': cmd, 'exit': child.returncode, 'wall_seconds': time.monotonic()-t, 'stop': reason})
        report = {'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'complete': len(results) == len(order) and not child.returncode and not reason, 'source_identity_sha256': identity_hash, 'versions': versions, 'settings': {'threads': 1, 'as_cap_bytes': 12*GIB, 'cgroup_reserve_bytes': 4*GIB, 'swap': False, 'cache': 'fresh olean outputs; OS page cache uncontrolled'}, 'modules': results, 'wall_seconds': time.monotonic()-start, 'peak_cgroup_memory_bytes': peak, 'max_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, 'source_census_sha256': hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()}
        (out/'measurement.json').write_text(json.dumps(report, indent=2)+'\n')
        print(f'{n}: exit={child.returncode} wall={results[-1]["wall_seconds"]:.3f}s', flush=True)
        if child.returncode or reason: raise SystemExit(1)
    print('ASSIGNED_CLOSURE_PASS (not RUNTIME_GATE_PASS)', flush=True)

if __name__ == '__main__': main()
