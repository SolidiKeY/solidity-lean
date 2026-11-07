#!/usr/bin/env python3
"""Verify or restore H44 VM-only evidence; never downloads data or changes gates."""
import argparse, hashlib, json, pathlib, subprocess, tarfile

def digest(data): return hashlib.sha256(data).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parents[2]/'docs/dafny-parity-bulk-manifest.json')
    parser.add_argument('--directory',type=pathlib.Path,help='Directory containing bulk.tar.gz and files.json, if relocated')
    parser.add_argument('--repo',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parents[2])
    parser.add_argument('--restore',action='store_true',help='Restore ignored paths from the verified snapshot; existing differences fail')
    args=parser.parse_args(); manifest=json.loads(args.manifest.read_text()); repo=args.repo.resolve()
    archive=args.directory/'bulk.tar.gz' if args.directory else pathlib.Path(manifest['archive']['path'])
    index=args.directory/'files.json' if args.directory else pathlib.Path(manifest['index']['path'])
    if not archive.is_file() or not index.is_file(): raise FileNotFoundError('H44 bulk bundle required: provision bulk.tar.gz and files.json; use --directory DIR after copying the checksum-bound VM bundle. No tests or gates were skipped.')
    if digest(archive.read_bytes())!=manifest['archive']['sha256']: raise ValueError('Archive checksum mismatch')
    if digest(index.read_bytes())!=manifest['index']['sha256']: raise ValueError('File index checksum mismatch')
    rows=json.loads(index.read_text()); expected={row['path']:row for row in rows}
    if len(expected)!=len(rows) or len(rows)!=manifest['fileCount']: raise ValueError('File count/duplicate mismatch')
    payload={}
    with tarfile.open(archive,'r:gz') as tar:
        members=tar.getmembers()
        if len(members)!=len(expected) or {m.name for m in members}!=set(expected): raise ValueError('Archive member mismatch')
        for member in members:
            name=pathlib.PurePosixPath(member.name)
            if not member.isfile() or name.is_absolute() or '..' in name.parts or not member.name.startswith('tests/editor-parity/'): raise ValueError('Unsafe archive path/type')
            target=repo/member.name
            if not target.resolve().is_relative_to(repo) or target.is_symlink() or any(p.is_symlink() for p in target.parents if p!=repo and p.is_relative_to(repo)): raise ValueError('Unsafe destination')
            if subprocess.run(['git','ls-files','--error-unmatch','--',member.name],cwd=repo,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0: raise ValueError('Refusing tracked destination '+member.name)
            if subprocess.run(['git','check-ignore','-q','--',member.name],cwd=repo).returncode!=0: raise ValueError('Destination must be ignored '+member.name)
            row=expected[member.name]
            if member.size!=row['bytes']: raise ValueError('Member size mismatch')
            data=tar.extractfile(member).read()
            if len(data)!=row['bytes'] or digest(data)!=row['sha256']: raise ValueError('Member checksum mismatch '+member.name)
            if target.exists() and (not target.is_file() or digest(target.read_bytes())!=row['sha256']): raise ValueError('Existing file differs; preserve it before restoring '+member.name)
            payload[member.name]=(data,member.mode & 0o777)
    if args.restore:
        for name,(data,mode) in payload.items():
            target=repo/name
            if not target.exists(): target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data); target.chmod(mode)
    else:
        for name,(data,mode) in payload.items():
            target=repo/name
            if not target.is_file() or digest(target.read_bytes())!=digest(data): raise ValueError('Working evidence missing/different '+name)
    print(json.dumps({'status':'verified','restored':args.restore,'files':len(rows),'bytes':sum(r['bytes'] for r in rows),'archive':str(archive)}))
if __name__=='__main__': main()
