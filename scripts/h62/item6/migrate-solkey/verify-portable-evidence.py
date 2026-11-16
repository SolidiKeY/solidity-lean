#!/usr/bin/env python3
"""Verify repo-relative summaries; optionally authenticate supplied H44 archives.

Missing bulk is reported as unavailable, never as proof/compatibility success.
No extraction, download, Lean invocation or workspace writes occur.
"""
import argparse,hashlib,json,tarfile
from pathlib import Path,PurePosixPath

def digest_file(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()

def relative(value):
 p=PurePosixPath(value)
 if p.is_absolute() or '..' in p.parts or not p.parts:raise ValueError('Unsafe relative path: '+value)
 return p

ROOT = Path(__file__).resolve().parents[4]

def load_catalog():
 return json.loads((ROOT/'tests/h62/item6/migrate-solkey/portable-evidence/catalog.json').read_text())

def repository_digest(row):
 path=ROOT.joinpath(*relative(row['path']).parts)
 return digest_file(path) if path.is_file() else None

def verify(catalog, artifact_dir=None, *, read_digest=repository_digest):
 for row in catalog['repository_files']:
  relative(row['path'])
  if read_digest(row)!=row['sha256']:raise ValueError('Repository checksum mismatch: '+row['path'])
 statuses=[]
 for archive in catalog['bulk_archives']:
  name=str(relative(archive['filename']))
  path=artifact_dir/name if artifact_dir else None
  if path is None or not path.is_file():
   statuses.append({'archive':name,'status':'unavailable'})
   continue
  if digest_file(path)!=archive['sha256']:raise ValueError('Archive checksum mismatch: '+name)
  pending={str(relative(m['path'])):m['sha256'] for m in archive['required_members']};seen=set()
  with tarfile.open(path,mode='r|gz') as tar:
   for member in tar:
    relative(member.name)
    if not member.isfile():raise ValueError('Non-regular archive member: '+member.name)
    if member.name in seen:raise ValueError('Duplicate member: '+member.name)
    seen.add(member.name)
    if member.name in pending:
     h=hashlib.sha256();stream=tar.extractfile(member)
     for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
     if h.hexdigest()!=pending.pop(member.name):raise ValueError('Member checksum mismatch: '+member.name)
  if pending:raise ValueError('Missing archive members: '+str(sorted(pending)))
  statuses.append({'archive':name,'status':'verified'})
 return {'repository_summaries':'verified','bulk':statuses,'compatibility_accepted':False,'lean_run':False}

def main():
 p=argparse.ArgumentParser();p.add_argument('--artifact-dir',type=Path);p.add_argument('--require-bulk',action='store_true');a=p.parse_args()
 report=verify(load_catalog(),a.artifact_dir)
 print(json.dumps(report,indent=2))
 if a.require_bulk and any(s['status']!='verified' for s in report['bulk']):raise SystemExit(1)

if __name__=='__main__':main()
