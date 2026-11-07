#!/usr/bin/env python3
"""Compare exact source headers without accepting semantic or kernel fidelity.

Guarded regression: changed files with stable headers are not automatically
proof-only, and an added mapFree argument is not an equivalence proof. Preserve
both inventories and the original pending statuses; emit bulk detail off Git.
"""
import argparse
import hashlib
import json
from pathlib import Path


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def mapfree_text_pattern(old, new):
    token=' E.mapFree'
    return (new.count(token)==old.count(token)+1 and
            ' '.join(new.replace(token,'',1).split())==' '.join(old.split()))


def compare(repo, frozen, current):
    receipt=json.loads((repo/'tests/h62/item2/audit-v07-lowering/frozen-reproduction.json').read_text())
    if sha(frozen.read_bytes())!=receipt['artifacts']['source-inventory.json']:
        raise ValueError('frozen inventory substitution')
    a=json.loads(frozen.read_text());b=json.loads(current.read_text())
    old={r['source_qualified_name']:r for r in a['theorems']}
    new={r['source_qualified_name']:r for r in b['theorems']}
    if len(old)!=len(a['theorems']) or len(new)!=len(b['theorems']):
        raise ValueError('duplicate source identities')
    if set(old)!=set(new):
        raise ValueError('source identity set changed; explicit reconciliation required')
    old_modules={r['path']:r['sha256'] for r in a['modules']}
    new_modules={r['path']:r['sha256'] for r in b['modules']}
    if set(old_modules)!=set(new_modules):
        raise ValueError('module set changed')
    if sha((repo/b['scope']).read_bytes())!=b['map_sha256']:
        raise ValueError('current map changed')
    texts={}
    for path,expected in new_modules.items():
        raw=(repo/path).read_bytes()
        if sha(raw)!=expected:raise ValueError('current source changed')
        texts[path]=raw.decode()
    rows=[]
    for name in sorted(old):
        before,after=old[name],new[name]
        if before['path']!=after['path']:
            raise ValueError('source declaration moved; explicit reconciliation required')
        header=texts[after['path']][after['start']:after['end']]
        if header!=after['signature_source'] or sha(header.encode())!=after['signature_sha256']:
            raise ValueError('current header is not its exact source slice')
        same=before['signature_sha256']==after['signature_sha256']
        drift=old_modules[before['path']]!=new_modules[after['path']]
        row=dict(name=name,path=before['path'],module_bytes_changed=drift,
                 header_bytes_equal=same,frozen_header_sha256=before['signature_sha256'],
                 current_header_sha256=after['signature_sha256'],semantic_fidelity='pending')
        if not same:
            row.update(frozen_header=before['signature_source'],current_header=header,
                       added_mapfree_text_pattern=mapfree_text_pattern(before['signature_source'],header))
        rows.append(row)
    return dict(schema_version=1,boundary='Exact source comparison only; no old/new statement equivalence or proof-only classification.',
                frozen_inventory_sha256=sha(frozen.read_bytes()),current_inventory_sha256=sha(current.read_bytes()),
                source_candidate_count=len(rows),changed_modules=sum(old_modules[p]!=new_modules[p] for p in old_modules),
                changed_headers=sum(not r['header_bytes_equal'] for r in rows),
                stable_headers_in_changed_modules=sum(r['header_bytes_equal'] and r['module_bytes_changed'] for r in rows),
                changed_headers_matching_mapfree_text=sum(r.get('added_mapfree_text_pattern',False) for r in rows),rows=rows)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['repo','frozen','current','output']:p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args()
    if a.output.resolve().is_relative_to(a.repo.resolve()) or a.output.exists():
        raise ValueError('new external output required')
    result=compare(a.repo,a.frozen,a.current)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
