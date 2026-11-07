"""Exact H70 Hash owner relay, applied only in an off-checkout source copy."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
REL_PATH = Path('Solidity/Hash/CollisionBound.lean')
BUNDLE = ROOT/'tests/h62/item5/statement-graph/overlays'
BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'


def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def check_base(data, meta):
    if blob(data) != meta['baseBlob'] or hashlib.sha256(data).hexdigest() != meta['baseSha256']:
        raise ValueError('H70 owner overlay base mismatch; original source is read-only')


def prepare(source_root):
    source_root = Path(source_root).resolve()
    registered = subprocess.check_output(['git','worktree','list','--porcelain','-z'],cwd=ROOT)
    worktrees = [Path(field.removeprefix(b'worktree ').decode()).resolve()
                 for field in registered.split(b'\0') if field.startswith(b'worktree ')]
    if any(source_root.is_relative_to(tree) for tree in worktrees):
        raise ValueError('H70 overlay source copy must be outside every registered checkout')
    ancestor = source_root
    while not ancestor.exists():
        ancestor = ancestor.parent
    probe = subprocess.run(['git','-C',str(ancestor),'rev-parse','--show-toplevel'],
                           stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if probe.returncode == 0:
        raise ValueError('H70 overlay source copy must be outside any Git checkout')
    meta_path = BUNDLE/'h70-collision-bound.json'
    meta = json.loads(meta_path.read_text())
    patch = BUNDLE/'h70-collision-bound.patch.json'
    envelope = json.loads(patch.read_text())
    patch_bytes = envelope['patch'].encode()
    if meta['path'] != str(REL_PATH) or envelope['sha256'] != meta['patchSha256'] or hashlib.sha256(patch_bytes).hexdigest() != meta['patchSha256']:
        raise ValueError('H70 relay patch identity mismatch')
    numstat = subprocess.check_output(['git','apply','--numstat'],input=patch_bytes).decode().splitlines()
    if len(numstat) != 1 or numstat[0].split('\t')[-1] != str(REL_PATH):
        raise ValueError('H70 overlay contains an unexpected file')
    original = (ROOT/REL_PATH).read_bytes()
    check_base(original,meta)
    pinned = subprocess.check_output(['git','show',BASE+':'+str(REL_PATH)],cwd=ROOT)
    check_base(pinned,meta)
    if original != pinned:
        raise ValueError('H70 checkout and pinned-base bytes differ')
    dest = source_root/REL_PATH
    if not dest.resolve().is_relative_to(source_root):
        raise ValueError('H70 overlay destination escapes source copy')
    dest.parent.mkdir(parents=True,exist_ok=True)
    if dest.exists():
        if blob(dest.read_bytes()) != meta['targetBlob']:
            raise ValueError('H70 existing overlay copy differs; refusing to overwrite')
    else:
        with dest.open('xb') as out:
            out.write(original)
        subprocess.run(['git','apply','--check'],input=patch_bytes,cwd=source_root,check=True,capture_output=True)
        subprocess.run(['git','apply'],input=patch_bytes,cwd=source_root,check=True,capture_output=True)
    result = dest.read_bytes()
    if blob(result) != meta['targetBlob'] or hashlib.sha256(result).hexdigest() != meta['targetSha256']:
        raise ValueError('H70 patched source does not match relayed target')
    if not meta['targetBlob'].startswith(meta['publishedTargetPrefix']):
        raise ValueError('H70 target does not match published owner prefix')
    if (ROOT/REL_PATH).read_bytes() != original:
        raise ValueError('H70 original source changed during preparation')
    return dest,dict(meta,metadataSha256=hashlib.sha256(meta_path.read_bytes()).hexdigest(),
                     sourceCopy=str(dest),ownerCommitVerification='Owner commit ID is relayed metadata; exact file base/target independently verified. No local owner commit object.')
