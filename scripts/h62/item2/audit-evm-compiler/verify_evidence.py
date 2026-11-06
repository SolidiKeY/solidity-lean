#!/usr/bin/env python3
"""Verify committed, repository-relative evidence pins against a downloaded archive.
Bulk data stays off Git. No VM path is needed; source pins bind the checker code.
"""
import argparse,hashlib,json,pathlib,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[4]
DEFAULT=ROOT/'tests/h62/item2/audit-evm-compiler/evidence-manifest.json'

def relative(value):
    p=pathlib.PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or '\\' in value:
        raise ValueError('invalid relative evidence path: '+value)
    return p

def digest(stream):
    return hashlib.file_digest(stream,'sha256').hexdigest()

def check_file(path,expected):
    with path.open('rb') as stream:actual=digest(stream)
    if actual!=expected:raise ValueError('checksum mismatch: '+str(path))

def verify(manifest,*,artifact_root=None,archive=None,repo_root=ROOT,sources_only=False):
    m=json.loads(pathlib.Path(manifest).read_text())
    if m['schema_version']!=1 or not m['artifacts'] or not m['sources']:raise ValueError('unsupported or empty manifest')
    if not sources_only and (artifact_root is None)==(archive is None):raise ValueError('provide one evidence source')
    if sources_only and (artifact_root is not None or archive is not None):raise ValueError('conflicting verification modes')
    for item in m['sources']:
        path=pathlib.Path(repo_root)/relative(item['path'])
        check_file(path,item['sha256'])
    if sources_only:
        return dict(sources_verified=len(m['sources']),artifacts_verified=0,status='source-pins-pass')
    paths=[str(relative(item['path'])) for item in m['artifacts']]
    if len(paths)!=len(set(paths)):raise ValueError('duplicate manifest evidence path')
    if archive is not None:
        prefix=str(relative(m['archive_root']))
        with tarfile.open(archive,'r:*') as bundle:
            members={}
            for entry in bundle.getmembers():members.setdefault(entry.name,[]).append(entry)
            for item in m['artifacts']:
                name=prefix+'/'+str(relative(item['path']));entries=members.get(name,[])
                if len(entries)!=1 or not entries[0].isfile():raise ValueError('missing, duplicate or non-file archive evidence: '+name)
                with bundle.extractfile(entries[0]) as stream:actual=digest(stream)
                if actual!=item['sha256']:raise ValueError('checksum mismatch: '+name)
    else:
        root=pathlib.Path(artifact_root).resolve()
        for item in m['artifacts']:
            path=(root/relative(item['path'])).resolve()
            if not path.is_relative_to(root):raise ValueError('evidence path escapes root')
            check_file(path,item['sha256'])
    return dict(sources_verified=len(m['sources']),artifacts_verified=len(m['artifacts']),status='pass')

def main():
    p=argparse.ArgumentParser();p.add_argument('--manifest',default=str(DEFAULT))
    group=p.add_mutually_exclusive_group(required=True);group.add_argument('--artifact-root');group.add_argument('--archive');group.add_argument('--sources-only',action='store_true')
    a=p.parse_args();print(json.dumps(verify(a.manifest,artifact_root=a.artifact_root,archive=a.archive,sources_only=a.sources_only)))
if __name__=='__main__':main()
