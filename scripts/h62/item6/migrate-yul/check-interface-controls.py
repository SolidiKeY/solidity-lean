#!/usr/bin/env python3
"""Validate the isolated inspector controls; never accepts a migration diff."""
import gzip,hashlib,json,pathlib,sys

def check(path):
    path=pathlib.Path(path);s=json.loads(path.read_text())
    raw=gzip.open(s['compressed'],'rb').read()
    assert hashlib.sha256(raw).hexdigest()==s['raw_sha256']
    data=[json.loads(line) for line in raw.decode().splitlines()]
    rows=[r for r in data if r['record']=='declaration']
    assert len(rows)==s['footer']['count']==27
    private=[r for r in rows if r['private']]
    assert {r['display_name'].rsplit('.',1)[1] for r in private}=={'hidden','hidden_ok','private_ext'}
    assert s['footer']['axiom_union']==[['str',['anonymous'],'propext']]
    names={r['display_name']:r for r in rows};prefix='H62.MigrateYul.InterfaceFixture.'
    for suffix in ['identity_eq','transitive_ext']:
        r=names[prefix+suffix];assert r['kind']=='theorem' and 'proof' in r['payload']
    sealed=names[prefix+'sealed'];assert sealed['kind']=='opaque' and sealed['payload']['mutual']==[sealed['name']]
    assert 'implementation' in sealed['payload']
    assert names[prefix+'PairBox.rec']['kind']=='recursor'
    assert names[prefix+'PairBox.mk']['kind']=='constructor'
    quoted=[r for r in rows if r['name'][-1]=='a.b']
    nested=[r for r in rows if r['name'][-1]=='b' and r['name'][1][-1]=='a']
    assert len(quoted)==len(nested)==1 and quoted[0]['name']!=nested[0]['name']
    p=json.loads(pathlib.Path(s['probe']).read_text())
    bound=p['probe_outputs_after'];assert len(bound)==1
    assert next(iter(bound.values()))['sha256']==s['raw_sha256']
    return s

if __name__=='__main__':
    old,new=map(check,sys.argv[1:3]);prefix='H62.MigrateYul.InterfaceFixture.'
    a={r['display_name']:r for r in old['declarations']};b={r['display_name']:r for r in new['declarations']}
    assert set(a)==set(b)
    for suffix in ['identity','identity_eq','withLet','sealed','transitive_ext']:
        assert a[prefix+suffix]['type_sha256']==b[prefix+suffix]['type_sha256']
    differences=[n for n in sorted(a) if a[n]['type_sha256']!=b[n]['type_sha256']]
    print(json.dumps(dict(status='control_integrity_pass',declarations_each=27,private_each=3,axioms=['propext'],raw_type_differences=differences,migration_acceptance=False),indent=2))
