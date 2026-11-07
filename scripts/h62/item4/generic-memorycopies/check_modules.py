#!/usr/bin/env python3
"""Serial migration prerequisite checks; uses a private v4.35 cache.

One Lake target at a time, in dependency order, with each Lean invocation
-j1/-M8192. Monitor process-tree RSS and cgroup/host headroom; stop rather
than count resource refusals as passes. No generated roots or source edits.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time
from census import mask

GIB = 1024 ** 3

def available():
    host = next(int(line.split()[1]) * 1024 for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
    cg = Path('/sys/fs/cgroup')
    maximum = (cg / 'memory.max').read_text().strip()
    return min(host, int(maximum) - int((cg / 'memory.current').read_text())) if maximum != 'max' else host

def descendants(parent):
    processes = {}
    for directory in Path('/proc').iterdir():
        if not directory.name.isdigit():
            continue
        try:
            status = dict(line.split(':', 1) for line in (directory / 'status').read_text().splitlines() if ':' in line)
            processes[int(directory.name)] = (int(status['PPid']), int(status.get('VmRSS', '0 kB').split()[0]) * 1024, status['Name'].strip())
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            pass
    owned = {parent}
    while True:
        more = {pid for pid, (ppid, _, _) in processes.items() if ppid in owned}
        if more <= owned:
            break
        owned |= more
    return [processes[pid] for pid in owned if pid in processes]

def closure(root, modules):
    ordered = []
    active = set()
    done = set()
    def visit(module):
        if module in done or not module.startswith('Solidity.'):
            return
        if module in active:
            raise ValueError('cyclic imports: ' + module)
        active.add(module)
        text = mask((root / (module.replace('.', '/') + '.lean')).read_text())
        for match in re.finditer(r'(?m)^import +([^\n]+)', text):
            for imported in match[1].split():
                visit(imported)
        active.remove(module)
        done.add(module)
        ordered.append(module)
    for module in modules:
        visit(module)
    return ordered

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path.cwd())
    p.add_argument('--toolchain', type=Path, required=True)
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--plan-only', action='store_true')
    p.add_argument('--validate-only', action='store_true')
    p.add_argument('--pin', type=Path, default=Path('/workspace/h62-coordinator-inputs/toolchain-pin.json'))
    p.add_argument('modules', nargs='+')
    a = p.parse_args()
    a.root = a.root.resolve()
    a.evidence = a.evidence.resolve()
    a.toolchain = a.toolchain.resolve()
    a.pin = a.pin.resolve()
    modules = closure(a.root, a.modules)
    if a.plan_only:
        print(json.dumps(modules, indent=2)); return
    pin = json.loads(a.pin.read_text())
    archive = a.toolchain.parent / pin['asset']
    with archive.open('rb') as source:
        archive_sha = hashlib.file_digest(source, 'sha256').hexdigest()
    if archive_sha != pin['sha256']:
        raise SystemExit('TOOLCHAIN_BLOCK: official archive SHA256 mismatch')
    lean_version = subprocess.check_output([str(a.toolchain / 'bin/lean'), '--version'], text=True).strip()
    lake_version = subprocess.check_output([str(a.toolchain / 'bin/lake'), '--version'], text=True).strip()
    version = pin['toolchain'].rsplit(':v', 1)[1]
    if f'version {version},' not in lean_version or f'Lean version {version}' not in lake_version:
        raise SystemExit('TOOLCHAIN_BLOCK: Lean/Lake do not match coordinator pin')
    a.evidence.mkdir(parents=True, exist_ok=True)
    (a.evidence / 'toolchain.json').write_text(json.dumps(dict(pin=pin, archive_sha256=archive_sha,
        lean=lean_version, lake=lake_version), indent=2) + '\n')
    if a.validate_only:
        print('TOOLCHAIN_PIN_PASS: ' + lean_version)
        return
    lockpath = Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
    lockpath.parent.mkdir(exist_ok=True)
    with lockpath.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        status = subprocess.check_output(['git', 'status', '--porcelain'], cwd=a.root, text=True)
        (a.evidence / 'git-status-before.txt').write_text(status)
        config = (a.root / 'lakefile.toml').read_text()
        config = config.replace('enableArtifactCache = true', 'enableArtifactCache = false\nsrcDir = ' + json.dumps(str(a.root)) + '\nbuildDir = ' + json.dumps(str(a.evidence / 'build-v4.35.0')))
        config = config.replace('weakLeanArgs = ["--tstack=131072"]', 'weakLeanArgs = ["--tstack=131072", "-j1", "-M8192"]')
        configpath = a.evidence / 'lakefile.toml'
        configpath.write_text(config)
        records = []
        for module in modules:
            if available() < 4 * GIB:
                raise SystemExit('RESOURCE_BLOCK: less than 4 GiB headroom')
            command = [str(a.toolchain / 'bin/lake'), '-f', str(configpath), '--no-cache', '--fail-fast', 'build', module]
            started = time.monotonic()
            peak = 0
            reason = None
            log = a.evidence / (module + '.log')
            with log.open('w') as output:
                child = subprocess.Popen(command, cwd=a.root, stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
                                         env={**os.environ, 'LEAN_NUM_THREADS': '1'})
                while child.poll() is None:
                    processes = descendants(child.pid)
                    peak = max(peak, sum(proc[1] for proc in processes))
                    if available() < 4 * GIB or peak > 12 * GIB:
                        reason = 'RESOURCE_BLOCK'
                    elif sum(proc[2] == 'lean' for proc in processes) > 1:
                        reason = 'SERIALITY_BLOCK'
                    elif time.monotonic() - started > 300:
                        reason = 'MODULE_TIME_BLOCK'
                    if reason:
                        os.killpg(child.pid, signal.SIGTERM)
                        try:
                            child.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            os.killpg(child.pid, signal.SIGKILL)
                        break
                    time.sleep(0.25)
                code = child.wait()
            row = dict(module=module, command=command, exit=code, elapsed_seconds=time.monotonic()-started,
                       sampled_peak_tree_rss_bytes=peak, blocker=reason, log=str(log))
            records.append(row)
            (a.evidence / 'module-checks.json').write_text(json.dumps(records, indent=2) + '\n')
            print(json.dumps(row), flush=True)
            if code or reason:
                raise SystemExit(1)

if __name__ == '__main__':
    main()
