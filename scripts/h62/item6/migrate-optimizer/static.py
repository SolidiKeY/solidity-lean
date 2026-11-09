#!/usr/bin/env python3
"""Non-Lean frozen-base, scope, trust-token and reproduction gate."""
from pathlib import Path
import hashlib,json,re,subprocess
from bulk import bulk_path, load_bulk_json
root=Path(__file__).resolve().parents[4]
def run(*args):return subprocess.check_output(args,cwd=root,text=True)
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
branch='codex/solidity-h62-6-20261106/migrate-optimizer'
assert run('git','branch','--show-current').strip()==branch
run('git','merge-base','--is-ancestor',base,'HEAD')
run('git','merge-base','--is-ancestor',base,'origin/master')
run('git','diff','--exit-code',base,'--','Solidity/Optimizer','lean-toolchain')
run('git','diff','--check')
x=load_bulk_json('census.json')
for f in x['files'].values():
 old=subprocess.check_output(['git','show',base+':'+f['path']],cwd=root)
 assert hashlib.sha256(old).hexdigest()==f['sha256']
 assert hashlib.sha256((root/f['path']).read_bytes()).hexdigest()==f['sha256']
assert run('python3','scripts/h62/item6/migrate-optimizer/census.py')==bulk_path('census.json').read_text()
run('python3','scripts/h62/item6/migrate-optimizer/fixtures.py','--check')
for p in (root/'tests/h62/item6/migrate-optimizer').glob('*.lean'):
 assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats)\b',p.read_text()),str(p)
allowed=['scripts/h62/item6/migrate-optimizer/','tests/h62/item6/migrate-optimizer/','docs/feature-work/h62-6-migrate-optimizer.md']
for line in run('git','status','--porcelain','--untracked-files=all').splitlines():
 path=line[3:];assert any(path.startswith(a) for a in allowed),path
inputs=Path('/workspace/h62-coordinator-inputs')
for name,digest in json.loads((inputs/'sha256.json').read_text()).items():
 assert hashlib.file_digest((inputs/name).open('rb'),'sha256').hexdigest()==digest
pin=json.loads((inputs/'toolchain-pin.json').read_text())
archive=Path('/workspace/migrate-optimizer-evidence/toolchains')/pin['asset']
assert hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()==pin['sha256']
summary=load_bulk_json('measurements.json')
assert summary['performance_status']=='STOP_GT_10_PERCENT'
for label,result in summary['results'].items():
 inspect=json.loads((Path('/workspace/migrate-optimizer-evidence')/label/'container.json').read_text())[0]
 h=inspect['HostConfig'];assert h['Memory']==h['MemorySwap']==12*1024**3 and h['NanoCpus']==1000000000
 assert not inspect['State']['Running'] and not inspect['State']['OOMKilled']
 samples=json.loads((Path('/workspace/migrate-optimizer-evidence')/label/'samples.json').read_text());assert samples
 assert all(len([r for r in s['processes'] if r[1]=='lean'])<=1 for s in samples)
 assert all(s['available']>=4*1024**3 for s in samples)
print('STATIC_GATE_PASS: pinned base/ancestry, scope, unchanged originals/toolchain, source trust tokens, deterministic generators, shared official pin, fixed-resource stopped containers, sampled serial Lean and headroom')
print('No Lean executed. Full migration remains BLOCKED; no runtime gate pass.')
