"""Exact external fixture provenance/coverage preflight; not a Lean proof."""
import collections,hashlib,json,pathlib
area=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def validate_case_membership(manifest,data):
    expected={}
    for f in manifest['fixtures']:
        sources=f['type_sources'] if f['expect_accept'] else [f['type_source']]
        for src in sources:
            key=(src,f['expect_accept'])
            expected.setdefault(key,set()).add(f['id'])
    assert len(expected)==13241,'expected exact frozen case count'
    seen=set()
    for c in data['cases']:
        assert type(c['expect_accept']) is bool,'case polarity type'
        key=(c['source'],c['expect_accept'])
        assert key in expected and key not in seen,'unexpected/duplicate case'
        assert set(c['fixtures'])==expected[key] and len(set(c['fixtures']))==len(c['fixtures']),'case source provenance'
        if c['expect_accept']:assert c['root_kind'] in manifest['expected_type_nodes'],'positive root kind'
        else:assert c['root_kind'] is None,'negative root kind'
        seen.add(key)
    assert seen==set(expected),'missing cases'
    assert sum(accept for _,accept in seen)==13218,'positive count'
    assert sum(not accept for _,accept in seen)==23,'negative count'
def validate():
    raw=(area/'fixtures.json').read_bytes();manifest=json.loads(raw)
    assert manifest['phase']=='parsing'
    assert manifest['compiler']=={'version':'0.8.38+commit.1835d247.Emscripten.clang','filename':'soljson-v0.8.38+commit.1835d247.js','sha256':'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'}
    assert manifest['enumeration']==dict(elementary_spellings=5287,mapping_elementary_keys=5286,function_attribute_variants=32,function_parameter_variants=9,function_return_variants=9,function_cross_product=2592)
    fixtures=manifest['fixtures'];assert len(fixtures)==29 and sum(f['expect_accept'] for f in fixtures)==6
    assert len({f['id'] for f in fixtures})==29 and len({f['file'] for f in fixtures})==29
    assert {str(p.relative_to(area)) for p in (area/'fixtures').rglob('*.sol')}=={f['file'] for f in fixtures}
    for f in fixtures:assert sha((area/f['file']).read_bytes())==f['sha256'],f['id']
    dataRaw=(area/'evidence/solc-type-cases.json').read_bytes();data=json.loads(dataRaw)
    receipt=json.loads((area/'evidence/solc-results.json').read_text())
    for doc in [data,receipt]:
        assert doc['manifest_sha256']==sha(raw),'stale manifest'
        assert doc['phase']=='parsing'
        assert {k:doc['compiler'][k] for k in manifest['compiler']}==manifest['compiler']
        assert doc['compiler']['observed_version']==manifest['compiler']['version']
    assert receipt['type_cases_sha256']==sha(dataRaw),'case receipt mismatch'
    assert receipt['fixture_count']==29 and receipt['failures']==0
    assert {r['id'] for r in receipt['results']}=={f['id'] for f in fixtures}
    assert len(receipt['results'])==29
    byid={f['id']:f for f in fixtures}
    for r in receipt['results']:
        f=byid[r['id']]
        assert r['passed'] and r['phaseCorrect']
        assert r['file']==f['file'] and r['source_sha256']==f['sha256']
        assert r['expected_accept']==f['expect_accept']==r['accepted']
    assert all(receipt['all_node_kinds'].get(k,0)>0 for k in manifest['expected_type_nodes'])
    validate_case_membership(manifest,data)
    return manifest,data
if __name__=='__main__':
    validate()
    print('PASS: current pinned solc receipt, all 29 source identities and exact 13218 positive/23 negative type cases')
