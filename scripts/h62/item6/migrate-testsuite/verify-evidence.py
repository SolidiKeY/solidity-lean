#!/usr/bin/env python3
"""Verify checkout files and separately supplied H44 evidence without extraction.
Missing external evidence is pending (exit2), never a successful evidence gate.
These are integrity checks, not Lean proofs or migration acceptance.
"""
import argparse,hashlib,json,re,tarfile
from pathlib import Path,PurePosixPath

def digest(stream):
    h=hashlib.sha256()
    for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()

def relative_name(value):
    if not isinstance(value,str) or not value or '\\' in value:raise ValueError('INVALID_RELATIVE_PATH')
    p=PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or p.as_posix()!=value or value=='.':raise ValueError('INVALID_RELATIVE_PATH')
    return value

def entries(rows):
    result={}
    if not isinstance(rows,list) or not rows:raise ValueError('EMPTY_MANIFEST')
    for row in rows:
        if not isinstance(row,dict) or set(row)!={'path','sha256','bytes'}:raise ValueError('INVALID_MANIFEST_ROW')
        name=relative_name(row['path'])
        if name in result:raise ValueError('DUPLICATE_MANIFEST_PATH')
        if not isinstance(row['sha256'],str) or re.fullmatch('[0-9a-f]{64}',row['sha256']) is None or type(row['bytes']) is not int or row['bytes']<0:raise ValueError('INVALID_MANIFEST_ROW')
        result[name]=row
    return result

def verify_directory(root,rows,allow_missing=False):
    root=Path(root).resolve();missing=[]
    if root.exists() and not root.is_dir():raise ValueError('INVALID_ROOT')
    for name,row in rows.items():
        path=(root/name).resolve()
        if not path.is_relative_to(root):raise ValueError('PATH_ESCAPES_ROOT: '+name)
        if not path.is_file():
            if allow_missing and not path.exists():missing.append(name);continue
            raise ValueError('MISSING_FILE: '+name)
        with path.open('rb') as stream: actual=digest(stream)
        if path.stat().st_size!=row['bytes'] or actual!=row['sha256']:raise ValueError('HASH_MISMATCH: '+name)
    return missing

def verify_archive(path,archive,rows):
    path=Path(path)
    if not path.is_file():raise ValueError('MISSING_ARCHIVE')
    with path.open('rb') as stream: actual=digest(stream)
    if path.stat().st_size!=archive['bytes'] or actual!=archive['sha256']:raise ValueError('ARCHIVE_HASH_MISMATCH')
    seen=set()
    with tarfile.open(path,mode='r|gz') as tar:
        for member in tar:
            if not member.name.startswith('evidence/'):continue
            name=member.name[len('evidence/'):]
            if name not in rows:continue
            if name in seen or not member.isfile():raise ValueError('INVALID_ARCHIVE_MEMBER: '+name)
            row=rows[name];stream=tar.extractfile(member)
            if member.size!=row['bytes'] or stream is None or digest(stream)!=row['sha256']:raise ValueError('ARCHIVE_MEMBER_HASH_MISMATCH: '+name)
            seen.add(name)
    if seen!=set(rows):raise ValueError('MISSING_ARCHIVE_MEMBERS')

def expand_manifest(manifest,detail_path=None):
    version=manifest.get('schema_version')
    if type(version) is not int:raise ValueError('UNSUPPORTED_MANIFEST')
    if version==1:
        if detail_path is not None:raise ValueError('UNEXPECTED_DETAIL_MANIFEST')
        return manifest
    if version!=2:raise ValueError('UNSUPPORTED_MANIFEST')
    def record(key):
        r=manifest[key]
        return next(iter(entries([{k:r[k] for k in ('path','bytes','sha256')}]).values()))
    detail=record('detail_manifest');archive=record('bulk_archive')
    if detail_path is None or not Path(detail_path).exists():return None
    path=Path(detail_path)
    if not path.is_file():raise ValueError('INVALID_DETAIL_MANIFEST_FILE')
    with path.open('rb') as stream:actual=digest(stream)
    if path.stat().st_size!=detail['bytes'] or actual!=detail['sha256']:raise ValueError('DETAIL_MANIFEST_HASH_MISMATCH')
    expanded=json.loads(path.read_text())
    if not isinstance(expanded,dict) or type(expanded.get('schema_version')) is not int or expanded.get('schema_version')!=1 or expanded.get('base')!=manifest.get('base') or expanded.get('archive')!=archive:raise ValueError('DETAIL_MANIFEST_DESCRIPTOR_MISMATCH')
    return expanded

def verify(manifest,repo,evidence_root=None,archive_path=None):
    if manifest.get('schema_version')!=1:raise ValueError('UNSUPPORTED_MANIFEST')
    tracked=entries(manifest['repository_files']);external=entries(manifest['evidence_files'])
    archive_rows=entries([manifest['archive']]);archive=next(iter(archive_rows.values()))
    verify_directory(repo,tracked)
    checked=[];missing=[]
    if evidence_root is not None:
        absent=verify_directory(evidence_root,external,allow_missing=True)
        if absent:missing.extend('directory:'+name for name in absent)
        else:checked.append('directory')
    if archive_path is not None:
        if not Path(archive_path).exists():missing.append('archive')
        else:verify_archive(archive_path,archive,external);checked.append('archive')
    if evidence_root is None and archive_path is None:missing.append('external evidence not supplied')
    return {'status':'pass' if checked and not missing else 'pending_artifacts','missing_artifacts':missing,'repository_files':len(tracked),'external_files':len(external),'external_checked':checked,'boundary':'File integrity/source provenance only; not Lean proof, API compatibility or runtime acceptance.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[4]);ap.add_argument('--manifest',type=Path);ap.add_argument('--evidence-root',type=Path);ap.add_argument('--archive',type=Path);ap.add_argument('--detail-manifest',type=Path);a=ap.parse_args()
    manifest=a.manifest or a.repo/'tests/h62/item6/migrate-testsuite/evidence-manifest.json'
    expanded=expand_manifest(json.loads(manifest.read_text()),a.detail_manifest)
    result=(verify(expanded,a.repo,a.evidence_root,a.archive) if expanded is not None else {'status':'pending_artifacts','missing_artifacts':['detail_manifest'],'repository_files':0,'external_files':0,'checks_pending':['repository integrity','external evidence integrity'],'boundary':'Detailed hash inventory required; no integrity, proof or runtime acceptance claimed.'})
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['status']=='pass' else 2)
