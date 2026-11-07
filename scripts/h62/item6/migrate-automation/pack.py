#!/usr/bin/env python3
"""Deterministically package off-git receipts and checksum their exact bytes.

Run only after measured jobs and reviews finish. Source/build snapshots and
release binaries stay off Git and are intentionally not duplicated here.
"""
import argparse,gzip,hashlib,io,json,pathlib,tarfile
p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);p.add_argument('--archive',required=True);p.add_argument('--manifest',required=True);a=p.parse_args()
r=pathlib.Path(a.evidence).resolve();archive=pathlib.Path(a.archive).resolve()
if archive.is_relative_to(r) or pathlib.Path(a.manifest).resolve().is_relative_to(r):
    p.error('archive and manifest outputs must be outside the evidence input directory')
paths=list(r.glob('*.json'))
for d in r.iterdir():
    if d.is_dir() and (d/'result.json').is_file():
        paths.extend([d/'result.json',d/'output.log'])
paths.extend((r/'static').glob('*.log'))
paths=sorted(set(paths),key=lambda p:p.relative_to(r).as_posix())
assert paths and not archive.exists()
members=[]
with archive.open('xb') as output, gzip.GzipFile(filename='',mode='wb',fileobj=output,mtime=0) as zipped, tarfile.open(fileobj=zipped,mode='w|') as tar:
    for f in paths:
        data=f.read_bytes();name=f.relative_to(r).as_posix();info=tarfile.TarInfo(name)
        info.size=len(data);info.mode=0o644;info.mtime=0;info.uid=0;info.gid=0
        tar.addfile(info,io.BytesIO(data));members.append({'path':name,'sha256':hashlib.sha256(data).hexdigest()})
manifest={'archive':str(archive),'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'members':members,
    'boundary':'Build/source snapshots and the pinned release archive remain separately off Git; reconstruct snapshots with prepare.py. No failed receipt proves acceptance.'}
pathlib.Path(a.manifest).write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'archive':str(archive),'sha256':manifest['sha256'],'members':len(members)}))
