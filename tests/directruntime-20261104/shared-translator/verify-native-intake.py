"""Guards historical native/WASM intake identity and safe artifact-only extraction.
Verification never executes delivered binaries, JS, WASM or stopped benchmarks.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,tarfile
ARCHIVE_SHA='729b0cb18b0d9f11232c6db92358a3e53d6a7075a2e775fee1e0a2f3e3df31da'
REQUEST_SHA='d75cbfd8d9b8550f99db4dfdc5507cbf1fa1cf3f47df2ab124654375b45f406f'
SOURCE='0140eb13b2f122d421deb07a19575a6801b21dfc'
DEFAULT=Path('/workspace/h62-coordinator-inputs/exact-A-intake-729b0cb18b0d.tar.gz')
def sha_stream(stream):
 h=hashlib.sha256()
 for b in iter(lambda:stream.read(1048576),b''):h.update(b)
 return h.hexdigest()
def safe_name(name):
 p=PurePosixPath(name)
 assert not p.is_absolute() and '..' not in p.parts and str(p)==name and name not in ('','.'),'unsafe member'
 return p
def safe_target(root,name):
 root=root.absolute()
 for parent in [*root.parents,root]:assert not parent.is_symlink(),'symlink extraction ancestor'
 target=root.joinpath(*safe_name(name).parts)
 current=root
 for part in safe_name(name).parts:
  current=current/part;assert not current.is_symlink(),'symlink extraction ancestor'
 assert target.resolve().is_relative_to(root.resolve()),'extraction outside root'
 assert not target.exists() or target.is_file(),'nonregular extraction target'
 return target
def verify(archive,extract=None):
 with archive.open('rb') as f:assert sha_stream(f)==ARCHIVE_SHA,'archive hash mismatch'
 assert archive.stat().st_size==10873861,'archive size mismatch'
 with tarfile.open(archive,'r:gz') as tar:
  members=tar.getmembers();assert all(m.isfile() for m in members),'nonregular member'
  names=[m.name for m in members];assert len(names)==len(set(names))==11,'member count/duplicate'
  for name in names:safe_name(name)
  requestRaw=tar.extractfile('delivery-request.json').read();assert hashlib.sha256(requestRaw).hexdigest()==REQUEST_SHA,'request hash mismatch'
  request=json.loads(requestRaw);assert request['sourceBuildHead']==SOURCE
  records=request['files'];assert len(records)==10 and len({r['member'] for r in records})==10
  assert set(names)=={'delivery-request.json'}|{r['member'] for r in records},'member set mismatch'
  verified=[]
  for r in records:
   member=tar.getmember(r['member']);assert member.size==r['bytes'],'member size mismatch'
   assert sha_stream(tar.extractfile(member))==r['sha256'],'member hash mismatch'
   verified.append({k:r[k] for k in ['member','sha256','bytes']})
  if extract:
   for m in members:safe_target(extract,m.name)
   extract.mkdir(parents=True,exist_ok=True)
   for m in members:
    target=safe_target(extract,m.name);target.parent.mkdir(parents=True,exist_ok=True)
    assert not target.is_symlink(),'existing extraction symlink'
    if target.exists():
     with target.open('rb') as f:assert sha_stream(f)==sha_stream(tar.extractfile(m)),'existing extraction differs'
    else:
     with target.open('xb') as output:
      source=tar.extractfile(m)
      for b in iter(lambda:source.read(1048576),b''):output.write(b)
     target.chmod(0o600)
 return {'regression':'Historical D evidence must not imply current H90 binary freshness','archive':str(archive),'archiveSha256':ARCHIVE_SHA,'sourceBuildHead':SOURCE,'members':verified,'extraction':str(extract) if extract else None,'boundary':'Hash/size intake only; no binary/JS/WASM execution, compiler preservation, H90 freshness, benchmark rerun or whole-goal acceptance.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,default=DEFAULT);p.add_argument('--extract',type=Path);p.add_argument('--report',type=Path);a=p.parse_args();r=verify(a.archive,a.extract)
 if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:v for k,v in r.items() if k!='members'}))
