#!/usr/bin/env python3
"""Attach exact frozen source signatures to the selected H70 manual classifications.
This external consistency check cannot verify any Lean witness. Bulk output is off Git.
"""
import argparse
import json
import pathlib
import subprocess
import census
from surface_classification import classify, groups


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=pathlib.Path, required=True)
    a=ap.parse_args()
    root=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
    output=a.output.resolve()
    if output==root or root in output.parents: ap.error('output must be outside checkout')
    metadata=json.loads((root/'tests/h62/item2/audit-v10-storage/candidate-bundles.json').read_text())
    inventory=census.collect(root)
    assert metadata['base']==inventory['base']
    assert len(metadata['bundles'])==metadata['expected_bundle_count']
    assert len({r['theorem'] for r in metadata['bundles']})==metadata['expected_bundle_count']
    for row in metadata['bundles']:
        namespace,name=row['theorem'].rsplit('.',1)
        frozen_text=census.frozen(root,row['path']).decode()
        assert ('namespace '+namespace+'\n') in frozen_text, row['theorem']
        matches=[d for d in inventory['declarations'] if d['path']==row['path'] and d['source_name']==name]
        assert len(matches)==1, row['theorem']
        declaration=matches[0]
        assert row['binder_order_scope'] in {'initial-forall','declaration-prefix'}, row['theorem']
        syntax=classify(declaration['signature'])
        names=[n for b in syntax['declaration_binders'] for n in b['names']]
        if row['binder_order_scope']=='initial-forall':
            assert not syntax['declaration_binders'], row['theorem']
            assert syntax['leading_forall_source'] is not None, row['theorem']
            raw=syntax['leading_forall_source']
            quantifiers,unknown=groups(raw,census.mask(raw))
            assert not unknown, row['theorem']
            names += [n for b in quantifiers for n in b['names']]
        if row['binder_order_scope']=='declaration-prefix' and syntax['leading_forall_source'] is not None:
            assert row.get('universal_conclusion_retained') is True, row['theorem']
        assert names==row['binder_order'], (row['theorem'],names,row['binder_order'])
        assert not row['counts_as_verified_witness']
        hypotheses=[h['name'] for h in row['hypotheses']]
        data=[n for n in row['binder_order'] if n not in hypotheses]
        assert len(set(row['binder_order']))==len(row['binder_order'])
        assert set(data)==set(row['shared_inputs'])
        assert all(n in row['binder_order'] for n in hypotheses)
        assert not row['global_premise_structures']
        row['frozen_source']=dict(id=declaration['id'],line=declaration['line'],signature=declaration['signature'],signature_sha256=declaration['signature_sha256'],owner=declaration['owner'])
    metadata['counts']=dict(source_classified_bundles=len(metadata['bundles']),verified_witnesses=0,uncovered_rows=inventory['counts']['uncovered'])
    output.mkdir(parents=True,exist_ok=True)
    (output/'candidate-classification.json').write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(metadata['counts'],sort_keys=True))

if __name__=='__main__': main()
