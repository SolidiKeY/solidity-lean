#!/usr/bin/env python3
"""Compare immutable source signatures; an integration merge is not fidelity."""
import argparse
import hashlib
import json
import pathlib
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--frozen',type=pathlib.Path,required=True)
p.add_argument('--current',type=pathlib.Path,required=True)
p.add_argument('--output',type=pathlib.Path,required=True)
a=p.parse_args()
old=json.loads(a.frozen.read_text());new=json.loads(a.current.read_text())
left={r['source_qualified_name']:r for r in old['theorems']}
right={r['source_qualified_name']:r for r in new['theorems']}
assert len(left)==len(old['theorems']) and len(right)==len(new['theorems'])
rows=[]
for name in sorted(left.keys()|right.keys()):
    before=left.get(name);after=right.get(name)
    status='added' if before is None else 'missing' if after is None else 'unchanged-source-signature' if before['signature_sha256']==after['signature_sha256'] else 'changed-source-signature'
    rows.append(dict(name=name,path=(before or after)['path'],owner=(before or after)['owner'],status=status,frozen_signature=before['signature_source'] if before else None,current_signature=after['signature_source'] if after else None,frozen_signature_sha256=before['signature_sha256'] if before else None,current_signature_sha256=after['signature_sha256'] if after else None,meaning='pending elaboration and dependent-definition fidelity'))
result=dict(boundary='Source comparison only. Changed signature is not asserted weaker or vacuous; H57 version fidelity remains pending.',frozen_inventory_sha256=hashlib.sha256(a.frozen.read_bytes()).hexdigest(),current_inventory_sha256=hashlib.sha256(a.current.read_bytes()).hexdigest(),statements=rows,counts={status:sum(r['status']==status for r in rows) for status in sorted({r['status'] for r in rows})})
a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result['counts']))
