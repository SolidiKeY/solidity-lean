#!/usr/bin/env python3
"""Reproduce coordinator-consumable patches on fresh pinned-source copies.
Usage: verify-overlays.py EVIDENCE_DIRECTORY
No live source, branch, toolchain or ownership changes.
"""
import hashlib,json,pathlib,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4];out=pathlib.Path(sys.argv[1]).resolve()
response=json.loads((repo/'tests/h62/item6/migrate-language/producer-response.json').read_text())
base=response['base'];records=[]
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--','Solidity/Language/'],cwd=repo,text=True).splitlines()
paths=[p for p in paths if p.endswith('.lean')]
for i,item in enumerate(response['patches']):
    patch=pathlib.Path(item['path']);assert hashlib.sha256(patch.read_bytes()).hexdigest()==item['sha256']
    target=out/'patch-verification'/response['head']/str(i);target.mkdir(parents=True,exist_ok=False)
    original={}
    for rel in paths:
        data=subprocess.check_output(['git','show',base+':'+rel],cwd=repo);original[rel]=data
        p=target/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    subprocess.run(['git','apply','--check',str(patch)],cwd=target,check=True)
    subprocess.run(['git','apply',str(patch)],cwd=target,check=True)
    checks=[]
    for rel in paths:
        in_scope=any(rel==scope or rel.startswith(scope) for scope in item['source_paths'])
        expected=subprocess.check_output(['git','show',response['head']+':'+rel],cwd=repo) if in_scope else original[rel]
        if in_scope: assert (repo/rel).read_bytes()==expected, 'working tree differs from recorded producer commit: '+rel
        assert (target/rel).read_bytes()==expected, rel
        checks.append(dict(path=rel,sha256=hashlib.sha256(expected).hexdigest()))
    records.append(dict(patch=str(patch),sha256=item['sha256'],base=base,producer_head=response['head'],git_apply_check_exit=0,byte_reproduction=True,files=checks))
(out/'patch-verification.json').write_text(json.dumps(records,indent=2)+'\n')
print('Both producer overlays apply to fresh pinned-source copies and reproduce the expected committed bytes.')
