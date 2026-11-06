#!/usr/bin/env python3
"""Export committed lane work and deterministic off-Git JSON/log evidence.

Invoke only after measurement processes have stopped. Official archives and
compiled oleans remain at their recorded VM paths; this archive carries the
reproducible generators' observations, not a cache shipment or proof shortcut.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'


def archive_evidence(evidence, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    files = sorted(p for p in evidence.rglob('*') if p.is_file() and p.suffix in {'.json','.log'} and p.name not in {'continuation-state.json','CLOUDVM-RESULT.json'} and 'lean-4.35.0-linux' not in p.relative_to(evidence).parts)
    with destination.open('xb') as raw, gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz, tarfile.open(fileobj=gz,mode='w') as tar:
        for path in files:
            info = tar.gettarinfo(str(path),arcname=str(path.relative_to(evidence)))
            info.uid = info.gid = info.mtime = 0
            info.mode = 0o644
            info.uname = info.gname = ''
            with path.open('rb') as f: tar.addfile(info,f)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive-only', action='store_true', help='Create immutable bulk archive before committing its checksum')
    p.add_argument('--root', required=True, type=Path)
    p.add_argument('--evidence', required=True, type=Path)
    p.add_argument('--out', required=True, type=Path)
    a = p.parse_args()
    root, evidence, out = a.root.resolve(), a.evidence.resolve(), a.out.resolve()
    if a.archive_only:
        archive_evidence(evidence, out)
        print(hashlib.sha256(out.read_bytes()).hexdigest()+'  '+str(out))
        return
    if out.exists(): raise SystemExit('Refusing to overwrite an existing handoff')
    if subprocess.check_output(['git','status','--porcelain'],cwd=root,text=True).strip():
        raise SystemExit('Commit the reviewable work before export')
    subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=root,check=True)
    head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    out.mkdir(parents=True)
    with (out/'migration.patch').open('wb') as f:
        subprocess.run(['git','diff','--binary',BASE,head],cwd=root,stdout=f,check=True)
    subprocess.run(['git','bundle','create',str(out/'migration.bundle'),'HEAD','^'+BASE],cwd=root,check=True)
    bundled = subprocess.check_output(['git','bundle','list-heads',str(out/'migration.bundle')],cwd=root,text=True).strip()
    if bundled != head+' HEAD': raise SystemExit('Bundle tip differs from committed handoff head')
    subprocess.run(['git','bundle','verify',str(out/'migration.bundle')],cwd=root,check=True)
    (out/'HANDOFF.md').write_text(f'Committed head: `{head}`\nBase: `{BASE}`\nRepository: `{root}`\n\n'+(root/'docs/feature-work/h62-6-migrate-solkey.md').read_text())
    archive_evidence(evidence, out/'evidence.tar.gz')
    (out/'identity.json').write_text(json.dumps({'base':BASE,'head':head,'repository':str(root),'evidence':str(evidence)},indent=2)+'\n')
    manifest = []
    for path in sorted(out.iterdir()):
        if path.is_file(): manifest.append(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+path.name)
    (out/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
    print(out)

if __name__ == '__main__': main()
