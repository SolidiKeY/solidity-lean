#!/usr/bin/env python3
"""Static frozen-scope/incoming-tree ledger; no Lean or API-compatibility claim."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
SCOPE=ROOT/'tests/h62/item6/migrate-backend/retirement/ORIGINAL-SCOPE.txt'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)


def backend_tree(commit):
    result={}
    for row in git('ls-tree','-rz',commit,'--','Solidity/Backend').split(b'\0'):
        if not row: continue
        metadata,path=row.split(b'\t',1)
        mode,kind,digest=metadata.decode().split()
        name=path.decode()
        if name.endswith('.lean'):
            if kind!='blob' or mode not in ('100644','100755'): raise ValueError('unexpected source entry')
            result[name]=digest
    return result


def inventory(integration):
    integration=git('rev-parse',integration).decode().strip()
    git('merge-base','--is-ancestor',BASE,integration)
    scope={line for line in SCOPE.read_text().splitlines() if line.startswith('Solidity/Backend/')}
    before,after=backend_tree(BASE),backend_tree(integration)
    if scope!=set(before): raise ValueError('frozen manifest differs from frozen Backend tree')
    missing=sorted(scope-set(after))
    changed=[{'path':path,'base_blob':before[path],'integration_blob':after[path]} for path in sorted(scope & set(after)) if before[path]!=after[path]]
    incoming=[{'path':path,'blob':after[path],'ownership':'incoming/read-only; no assignment expansion inferred'} for path in sorted(set(after)-scope)]
    return {'schema':1,'base':BASE,'integration_head':integration,
            'scope_sha256':hashlib.sha256(SCOPE.read_bytes()).hexdigest(),
            'original_assigned_count':len(scope),'present_backend_count':len(after),
            'unchanged_original_count':sum(before[path]==after.get(path) for path in scope),
            'missing_original':missing,'changed_original':changed,'incoming_not_originally_assigned':incoming,
            'boundary':'Immutable Git blob ledger only; not exported public visibility/type/axiom compatibility, semantic equivalence, proof acceptance or scope transfer.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--integration',required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();output=args.output.resolve()
    if not output.is_relative_to(Path('/workspace/migrate-backend-evidence')) or output.exists():
        raise RuntimeError('output must be a new owned off-git evidence file')
    result=inventory(args.integration)
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({key:result[key] for key in ('integration_head','original_assigned_count','present_backend_count','unchanged_original_count')}))
