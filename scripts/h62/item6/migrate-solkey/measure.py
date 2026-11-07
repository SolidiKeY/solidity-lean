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
    p.add_argument('--check-file', type=Path, help='Diagnostic file; requires --inventory-imports')
    p.add_argument('--inventory-imports', type=Path, help='Check only the interface fixture using this completed closure output')
    p.add_argument('--timeout', type=int, default=1800)
    a = p.parse_args()
    root, out = a.root.resolve(), a.out.resolve()
    if a.check_file and not a.inventory_imports: raise SystemExit('--check-file requires --inventory-imports')
    if out.exists(): raise SystemExit('Refusing reused output: clean runs require a new path')
    out.mkdir(parents=True)
    lock = open('/tmp/solidity-lean-feature-groups-20261025/writer.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if Path('/proc/swaps').read_text().count('\n') != 1: raise SystemExit('Swap is configured')
    tooling = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__), Path(__file__).with_name('census.py')]}
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
    if a.inventory_imports:
        if not a.inventory_imports.is_dir(): raise SystemExit('Missing completed closure import path')
        selected = a.check_file.resolve().relative_to(root).with_suffix('').as_posix().replace('/', '.') if a.check_file else 'tests.h62.item6.migrate-solkey.FrozenInterfaces'
        order = [selected]
    lean = str(a.toolchain.resolve()/'bin/lean')
    versions = {exe: subprocess.check_output([str(a.toolchain.resolve()/'bin'/exe), '--version'], text=True).strip() for exe in ('lean','lake')}
    if a.inventory_imports and not a.check_file:
        closure = json.loads((a.inventory_imports.resolve().parent/'measurement.json').read_text())
        if closure.get('complete') is not True or closure['settings']['mode'] != 'assigned-closure':
            raise SystemExit('Interface inventory requires a completed assigned closure')
        if closure['source_identity_sha256'] != identity_hash or closure['versions'] != versions:
            raise SystemExit('Interface inventory source/toolchain mismatch')
        for entry in closure['modules']:
            artifact = a.inventory_imports.resolve()/(entry['module'].replace('.', '/')+'.olean')
            if entry['exit'] or entry['stop'] or hashlib.sha256(artifact.read_bytes()).hexdigest() != entry['olean_sha256']:
                raise SystemExit('Interface inventory artifact mismatch: '+entry['module'])
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=(str(a.inventory_imports.resolve())+os.pathsep if a.inventory_imports else '') + str(out/'lib'))
    results = []
    start = time.monotonic()
    peak = 0
    def isolate():
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
            child = subprocess.Popen(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, preexec_fn=isolate)
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
        results.append({'module': n, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'olean_sha256': hashlib.sha256(dest.read_bytes()).hexdigest() if child.returncode == 0 and dest.exists() else None, 'command': cmd, 'exit': child.returncode, 'wall_seconds': time.monotonic()-t, 'stop': reason})
        report = {'tooling_sha256': tooling, 'complete': len(results) == len(order) and not child.returncode and not reason, 'source_identity_sha256': identity_hash, 'versions': versions, 'settings': {'mode': ('per-file' if a.check_file else 'interface-fixture') if a.inventory_imports else 'assigned-closure', 'threads': 1, 'vm_cgroup_max_bytes': int(Path('/sys/fs/cgroup/memory.max').read_text()), 'cgroup_reserve_bytes': 4*GIB, 'swap': False, 'cache': 'fresh olean outputs; OS page cache uncontrolled'}, 'modules': results, 'wall_seconds': time.monotonic()-start, 'peak_cgroup_memory_bytes': peak, 'max_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, 'source_census_sha256': hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()}
        (out/'measurement.json').write_text(json.dumps(report, indent=2)+'\n')
        print(f'{n}: exit={child.returncode} wall={results[-1]["wall_seconds"]:.3f}s', flush=True)
        if child.returncode or reason: raise SystemExit(1)
    print((('PER_FILE_PASS' if a.check_file else 'INTERFACE_FIXTURE_PASS') if a.inventory_imports else 'ASSIGNED_CLOSURE_PASS')+' (not RUNTIME_GATE_PASS)', flush=True)

if __name__ == '__main__': main()
