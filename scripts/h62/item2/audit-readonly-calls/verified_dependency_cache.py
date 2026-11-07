"""Guard source/object substitution when reusing previously executed audit dependencies.
Only two exact executed primitive-transport receipts are admitted. This is
explicit checked-object reuse, never a fresh rebuild or arbitrary cache fallback.
All previous sources/objects/logs must still match; changed tracked Python tools
are recovered only as exact hash-matched Git bytes at the admitted receipt head; every reused module's
fresh source and import list must match. New leaves are always compiled.
"""
import hashlib
import shutil
import subprocess
from pathlib import Path
ADMITTED={'frozen':'4802c491d6e5bd616e8af86ecec8514da33480f573de1f04cc5dbe4e1ad57f48',
          'current':'16b93f2f1ca30d81538b405936413a69bb16271f68de5dc3f3cd025c10bc5d7b'}

def authenticate_tools(repo,head,pins,archive,create=True):
    authenticated={};snapshots={}
    for path,digest in pins.items():
        file=Path(path)
        if file.is_relative_to(repo/'scripts') and file.suffix=='.py' and hashlib.sha256(file.read_bytes()).hexdigest()!=digest:
            relative=str(file.relative_to(repo))
            raw=subprocess.check_output(['git','show',head+':'+relative],cwd=repo)
            if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('historical tool object mismatch')
            saved=archive/relative
            if not saved.exists():
                if not create:raise ValueError('missing historical tool snapshot')
                saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(raw)
            if hashlib.sha256(saved.read_bytes()).hexdigest()!=digest:raise ValueError('historical tool snapshot drift')
            authenticated[str(saved)]=digest
            snapshots[path]={'source_head':head,'sha256':digest,'saved':str(saved)}
        else:authenticated[path]=digest
    for path,digest in authenticated.items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest()!=digest:raise ValueError('unrecoverable protected input drift')
    return authenticated,snapshots

class Cache:
    def __init__(self,gate,root,mode,pins,archive,create=True):
        self.gate=gate;self.root=root.resolve();self.path=self.root/'receipt.json';self.mode=mode
        self.receipt=gate.current.original.load_pinned(self.path,ADMITTED[mode])
        self.archive=archive;self.create=create;self.historical_tools={}
        r=self.receipt
        if r['mode']!=mode or r['base']!=gate.original.BASE:raise ValueError('cache mode/base mismatch')
        if set(r['project_order'])!=set(r['source_pins']) or len(r['project_order'])!=len(r['source_pins']):raise ValueError('incomplete parent closure')
        for relative,pin in r['source_pins'].items():
            if not relative.startswith('Solidity/') or pins.get(relative)!=pin:raise ValueError('cached source/import drift')
        self.used=[];self.verify()

    def verify(self):
        g=self.gate;r=self.receipt
        g.original.pin_authenticated_file({},self.path,ADMITTED[self.mode])
        pins,snapshots=authenticate_tools(g.original.ROOT,r['head'],r['protected_sha256'],self.archive,create=self.create)
        self.historical_tools.update(snapshots)
        g.check.verify_hashes(pins|{s['log']:s['sha256'] for s in r['steps']})
        g.check.verify_hashes({item['saved']:item['sha256'] for item in self.historical_tools.values()})
        if not r['steps'] or any(s['exit']!=0 for s in r['steps']):raise ValueError('failed parent step')
        for relative in r['project_order']:
            old=self.root/'library'/(relative[:-5]+'.olean')
            if g.check.sha(old)!=r['artifacts'][relative]['artifact_sha256']:raise ValueError('cached object drift')

    def copy(self,relative,captured,staged,artifact):
        r=self.receipt
        if relative not in r['source_pins']:return None
        pin=r['source_pins'][relative];record=r['artifacts'][relative]
        raw=captured.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=pin['source_sha256'] or record['source_sha256']!=pin['source_sha256']:raise ValueError('cached source replacement')
        staged.parent.mkdir(parents=True,exist_ok=True);staged.write_bytes(raw)
        old=self.root/'library'/(relative[:-5]+'.olean')
        if self.gate.check.sha(old)!=record['artifact_sha256']:raise ValueError('cached object replacement')
        artifact.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(old,artifact)
        if self.gate.check.sha(artifact)!=record['artifact_sha256']:raise ValueError('cached object copy drift')
        self.used.append(relative)
        return dict(record)

    def provenance(self):
        return {'kind':'checked-reuse-not-fresh-closure','parent_receipt':str(self.path),'parent_receipt_sha256':ADMITTED[self.mode],
                'parent_head':self.receipt['head'],'modules':list(self.used),'count':len(self.used),'historical_tool_snapshots':dict(self.historical_tools)}
