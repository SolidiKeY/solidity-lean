"""Conservative process limits and content fingerprints for this isolated lane."""
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
from census import ROOT

RESERVE = 4*1024**3


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def available():
    host = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
    limit = Path('/sys/fs/cgroup/memory.max').read_text().strip()
    current = int(Path('/sys/fs/cgroup/memory.current').read_text())
    return min(host,int(limit)-current) if limit != 'max' else host


def memory_cap():
    if len(Path('/proc/swaps').read_text().splitlines()) != 1:
        raise ValueError('active swap is forbidden')
    cap = min(12*1024**3,available()-RESERVE)
    cap = cap//(256*1024**2)*(256*1024**2)
    if cap < 1024**3:
        raise ValueError('no bounded 1 GiB job fits with 4 GiB reserve')
    return cap


def guard(cap):
    if available() < cap+RESERVE:
        raise ValueError('cgroup/host 4 GiB reserve unavailable')


def bound(cap):
    def apply():
        resource.setrlimit(resource.RLIMIT_AS,(cap,cap))
    return apply


def compiler(evidence):
    pin=json.loads(Path('/workspace/h62-coordinator-inputs/toolchain-pin.json').read_text())
    if pin['toolchain'] != 'leanprover/lean4:v4.35.0' or sha(evidence/'toolchain'/pin['asset']) != pin['sha256']:
        raise ValueError('official toolchain pin mismatch')
    return evidence/'toolchain'/pin['asset'].removesuffix('.tar.zst')/'bin'/'lean',pin


def fingerprint(build):
    paths=subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard'],cwd=ROOT).decode().split('\0')
    source={}
    for name in sorted(set(paths)-{''}):
        path=ROOT/name
        source[name]=hashlib.sha256(os.readlink(path).encode()).hexdigest() if path.is_symlink() else sha(path) if path.is_file() else 'missing'
    artifacts={p.relative_to(build).as_posix():sha(p) for p in sorted(build.rglob('*')) if p.is_file()}
    return dict(head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
                tree_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest(),
                artifacts_sha256=hashlib.sha256(json.dumps(artifacts,sort_keys=True).encode()).hexdigest())
