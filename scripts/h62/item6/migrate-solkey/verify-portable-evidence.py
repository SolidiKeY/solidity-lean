#!/usr/bin/env python3
"""Verify repo-relative summaries; optionally authenticate supplied H44 archives.

Missing bulk is reported as unavailable, never as proof/compatibility success.
No extraction, download, Lean invocation or workspace writes occur.
Use --interface-version 2 --historical-input-root DIR for exact private
historical summaries from archive fa68e0ac599d1f6a59dab0af5b19dbf2ae029c9f.
DIR contains tests/h62/... outside the repository; no fallback occurs.
V1 remains the default; v2 reports historical and repository inputs separately.
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


HISTORICAL_PINS = {
    "tests/h62/item6/migrate-solkey/portable-evidence/old-api-summary.json":
        (1117, "d2c695899dbdc3ac7c90ab4a2cb6f4e6bf2a6ed3f040ad977ad9fdd5a41e2b9a"),
    "tests/h62/item6/migrate-solkey/portable-evidence/sdk-summary.json":
        (879, "b6b45e6ef3463cffebabae36705955dc6aa0b0d0df265c1575687fe74cf46fc6"),
}


def verify_v2(directory, artifact_dir=None):
    root = directory.resolve()
    if root.is_relative_to(ROOT.resolve()):
        raise ValueError("Historical input root must be outside the repository")
    catalog = load_catalog()
    selected = [r for r in catalog["repository_files"] if r["path"] in HISTORICAL_PINS]
    if len(selected) != len(HISTORICAL_PINS) or {r["path"] for r in selected} != set(HISTORICAL_PINS):
        raise ValueError("Historical summary catalog membership mismatch")
    for row in selected:
        if row["sha256"] != HISTORICAL_PINS[row["path"]][1]:
            raise ValueError("Historical summary catalog checksum mismatch: " + row["path"])

    def read_digest(row):
        name = row["path"]
        if name not in HISTORICAL_PINS:
            return repository_digest(row)
        path = (root / name).resolve(strict=True)
        if not path.is_relative_to(root):
            raise ValueError("Historical summary escapes its input root: " + name)
        raw = path.read_bytes()
        size, expected = HISTORICAL_PINS[name]
        actual = hashlib.sha256(raw).hexdigest()
        if len(raw) != size or actual != expected:
            raise ValueError("Historical summary checksum mismatch: " + name)
        return actual

    report = verify(catalog, artifact_dir, read_digest=read_digest)
    del report["repository_summaries"]
    return {"interface_version": 2, "historical_summaries": "verified",
            "repository_support_files": "verified", **report}



def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--artifact-dir',type=Path);p.add_argument('--require-bulk',action='store_true')
 p.add_argument('--interface-version',type=int,choices=(1,2),default=1);p.add_argument('--historical-input-root',type=Path);a=p.parse_args()
 if a.interface_version==2:
  if a.historical_input_root is None:p.error('v2 requires --historical-input-root')
  report=verify_v2(a.historical_input_root,a.artifact_dir)
 else:
  if a.historical_input_root is not None:p.error('--historical-input-root requires --interface-version 2')
  report=verify(load_catalog(),a.artifact_dir)
 print(json.dumps(report,indent=2))
 if a.require_bulk and any(s['status']!='verified' for s in report['bulk']):raise SystemExit(1)

if __name__=='__main__':main()
