#!/usr/bin/env python3
"""Inspect B05 fixture evidence without accepting the untouched migration."""
import argparse,gzip,hashlib,json,pathlib,subprocess,sys
import interfaces
p=argparse.ArgumentParser();p.add_argument('evidence',type=pathlib.Path);a=p.parse_args()
subprocess.run([sys.executable,str(pathlib.Path(__file__).with_name('generate-reserved-fixture.py')),'--check'],check=True)
labels=['old-original','old-candidate','new-candidate']
snapshots=[json.loads((a.evidence/('b05-'+v+'.json')).read_text()) for v in labels]
names=['Solidity.Yul.reservedNames','Solidity.Yul.reservedNames_count','Solidity.Yul.slotnum_not_reserved']
rows=[{d['display_name']:d for d in s['declarations']} for s in snapshots]
assert set(rows[0])==set(names)
helper='Solidity.Yul.reservedNames_count._proof_1_1'
assert set(rows[1])==set(rows[2])==set(names+[helper])
for name in names:
    for field in ['type_sha256','signature_sha256','declaration_metadata_sha256']:
        assert len({r[name][field] for r in rows})==1, (name,field)
assert len({r[names[2]]['proof_sha256'] for r in rows})==1
assert snapshots[0]['footer']['axiom_union']==snapshots[1]['footer']['axiom_union']==snapshots[2]['footer']['axiom_union']
assert rows[1]==rows[2], 'candidate kernel declarations differ between releases'
impl=[]
for v in labels:
    with gzip.open(a.evidence/('b05-'+v+'.jsonl.gz'),'rt') as f:
        raw=[json.loads(line) for line in f]
    assert hashlib.sha256((a.evidence/('b05-'+v+'.jsonl.gz')).read_bytes()).hexdigest()==snapshots[labels.index(v)]['compressed_sha256']
    with gzip.open(a.evidence/('b05-'+v+'.jsonl.gz'),'rb') as f:
        assert hashlib.sha256(f.read()).hexdigest()==snapshots[labels.index(v)]['raw_sha256']
    probe=interfaces.validate_probe(snapshots[labels.index(v)]['probe'])
    assert next(iter(probe['probe_outputs_after'].values()))['sha256']==snapshots[labels.index(v)]['raw_sha256']
    impl.append(json.loads(next(d for d in raw if d.get('display_name')==names[0])['payload']['implementation']))
# Diagnostic only: retain all raw hashes. Count differing binder names while
# requiring exact equality of every other expression field and constant name.
stack=[(impl[0],impl[1])];binders=0
while stack:
    x,y=stack.pop()
    if isinstance(x,list):
        assert isinstance(y,list) and len(x)==len(y)
        skip=1 if x and x[0] in ['let','lam','forall'] else None
        if skip is not None:
            assert x[0]==y[0]
            binders+=x[1]!=y[1]
        stack.extend((u,v) for i,(u,v) in enumerate(zip(x,y)) if i!=skip)
    else:assert x==y,(x,y)
assert impl[1]==impl[2]
print(json.dumps(dict(status='pass',original_declarations=3,candidate_declarations=4,generated_kernel_helpers=[helper],original_signatures_equal=True,table_source_exact=True,table_raw_hash_difference='fixture module hygiene binder names',differing_binder_names=binders,axiom_union=snapshots[0]['footer']['axiom_union'],migration_acceptance=False),sort_keys=True))
