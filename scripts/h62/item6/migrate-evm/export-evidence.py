"""Export a committed, isolated blocked-lane checkpoint without network writes."""
import gzip,hashlib,io,json,subprocess,tarfile
from pathlib import Path
ROOT=Path('/workspace/migrate-evm'); ART=Path('/workspace/migrate-evm-artifacts'); E=ART/'evidence'
BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
BRANCH='codex/solidity-h62-6-20261106/migrate-evm'
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert git('branch','--show-current').decode().strip()==BRANCH
assert not git('status','--porcelain'), 'preserve unexpected local work; commit authorized checkpoint first'
subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
assert not git('diff','--name-only',BASE,'HEAD','--','Solidity/Evm','lean-toolchain'), 'production/toolchain scope drift'
head=git('rev-parse','HEAD').decode().strip(); dest=ART/'exports'/head
assert not dest.exists(), 'immutable export already exists'
dest.mkdir(parents=True)
patch=dest/'migrate-evm.patch';patch.write_bytes(git('format-patch','--stdout',BASE+'..'+head))
bundle=dest/'migrate-evm.bundle'
subprocess.run(['git','bundle','create',str(bundle),BASE+'..'+BRANCH],cwd=ROOT,check=True)
with (E/'gates/bundle-verify.log').open('wb') as log:
    subprocess.run(['git','bundle','verify',str(bundle)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
cache={str(p.relative_to(E)):sha(p) for p in sorted(E.rglob('*.olean'))}
(E/'private-cache-sha256.json').write_text(json.dumps(cache,sort_keys=True,indent=2)+'\n')
review_files=[]
for p in sorted(E.rglob('*')):
    if p.is_file() and 'lib' not in p.relative_to(E).parts and p.name!='evidence-file-sha256.json':
        assert not p.is_symlink(), 'unexpected evidence symlink'
        review_files.append(p)
manifest={str(p.relative_to(E)):sha(p) for p in review_files}
inside=E/'evidence-file-sha256.json';inside.write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n');review_files.append(inside)
archive=dest/'evidence.tar.gz'
with archive.open('wb') as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as compressed:
        with tarfile.open(fileobj=compressed,mode='w') as tar:
            for p in sorted(review_files):
                info=tarfile.TarInfo('evidence/'+str(p.relative_to(E)))
                info.size=p.stat().st_size;info.mode=0o600;info.mtime=0;info.uid=0;info.gid=0
                with p.open('rb') as source:tar.addfile(info,source)
handoff=dest/'HANDOFF.md'
document=(ROOT/'docs/feature-work/h62-6-migrate-evm.md').read_text().replace('](../../', ']('+str(ROOT)+'/')
goal_label='USER PAUSED / worker retired; platform PAUSED operation unavailable; assignment unfinished' if (ROOT/'tests/h62/item6/migrate-evm/handoff/h82-retirement-authority.txt').exists() else 'BLOCKED, unfinished'
handoff.write_text(f'Committed head: {head}\nBase: {BASE}\nRepository: {ROOT}\nBranch: {BRANCH}\n\nGoal disposition: {goal_label}. No implementation continuation by retired worker; successor preserves STOP/owner conditions.\nPrivate original proof caches remain at {E}; cache object hashes are in the evidence archive.\n\n'+document)
checks=dest/'SHA256SUMS';paths=[patch,bundle,handoff,archive]
checks.write_text(''.join(sha(p)+'  '+str(p)+'\n' for p in paths))
record={'head':head,'base':BASE,'repository':str(ROOT),'branch':BRANCH,'status':'partial' if 'USER PAUSED' in goal_label else 'blocked','disposition':goal_label,'handoff_to':'solidity-h62-6-20261106/migrate-root-gate','paths':{'original_patch':str(patch),'bundle':str(bundle),'handoff':str(handoff),'evidence':str(archive),'checksums':str(checks)},'sha256':{p.name:sha(p) for p in paths},'archived_review_files':len(review_files),'private_cached_objects':len(cache)}
(ART/'EXPORT.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
