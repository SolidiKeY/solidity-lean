#!/usr/bin/env python3
"""Hash kernel inventory output; fail closed on type or executable-body drift.

Proof-expression changes are reported separately: proof irrelevance does not
permit changing statement types or introducing forbidden axiom dependencies.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

MODULES = {'Solidity.Solkey.'+name for name in ['ComputedRevert','Constructors','QuantifiedDiamond','ScopedFlip','TestSuite']}
THEOREMS = {'counterDeploy','Solkey.EtherWallet.constructor.proved','Solkey.ScopedFlip.additionStorageWrite.proved'}
ALLOWED_AXIOMS = {'propext','Classical.choice','Quot.sound'}


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def normalize(text):
    arrays = []
    for line in text.splitlines():
        if line.startswith('['):
            try: value = json.loads(line)
            except json.JSONDecodeError: continue
            if isinstance(value,list): arrays.append(value)
    if len(arrays) != 1 or not arrays[0]: raise ValueError('expected one nonempty declaration inventory')
    entries = arrays[0]
    if {e['module'] for e in entries} != MODULES: raise ValueError('module coverage mismatch')
    if len({e['name'] for e in entries}) != len(entries): raise ValueError('duplicate declaration')
    if not THEOREMS <= {e['name'] for e in entries}: raise ValueError('missing frozen theorem')
    axioms = {}
    for name in sorted(THEOREMS):
        if f"'{name}' does not depend on any axioms" in text: axioms[name] = []
        else:
            match = re.search(re.escape("'"+name+"' depends on axioms:")+r'\s*\[([^]]*)\]',text)
            if not match: raise ValueError('missing axiom output for '+name)
            axioms[name] = sorted(x.strip() for x in match[1].split(',') if x.strip())
        if not set(axioms[name]) <= ALLOWED_AXIOMS: raise ValueError('forbidden axiom dependency for '+name)
    result = {}
    for e in entries:
        if not isinstance(e['isTheorem'],bool) or e['kind'] not in {'definition','theorem','opaque','quotient','inductive','constructor','recursor'}:
            raise ValueError('invalid or forbidden declaration kind')
        if e['isTheorem'] != (e['kind'] == 'theorem'): raise ValueError('inconsistent theorem kind')
        result[e['name']] = {'module':e['module'], 'isTheorem':e['isTheorem'], 'kind':e['kind'],
            'type_sha256':digest([e['levelParams'],e['typeExpr']]),
            'value_sha256':digest(e['valueExpr'])}
    return {'declarations':dict(sorted(result.items())), 'public_theorem_axioms':axioms}


def compare(old,new):
    before, after = old['declarations'], new['declarations']
    added, removed = sorted(after.keys()-before.keys()), sorted(before.keys()-after.keys())
    types, values, proofs = [], [], []
    for name in sorted(before.keys() & after.keys()):
        b,a = before[name],after[name]
        if any(b[k] != a[k] for k in ['module','kind','isTheorem','type_sha256']): types.append(name)
        if b['value_sha256'] != a['value_sha256']:
            (proofs if b['isTheorem'] and a['isTheorem'] else values).append(name)
    return {'status':'INTERFACE_DRIFT' if added or removed or types or values else 'FROZEN_INTERFACES_PASS',
        'added':added,'removed':removed,'changed_types':types,'changed_definition_bodies':values,
        'changed_proof_expressions':proofs,'old_public_axioms':old['public_theorem_axioms'],
        'new_public_axioms':new['public_theorem_axioms']}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('old_log',type=Path)
    p.add_argument('new_log',type=Path,nargs='?')
    a=p.parse_args()
    old=normalize(a.old_log.read_text())
    result=compare(old,normalize(a.new_log.read_text())) if a.new_log else old
    print(json.dumps(result,indent=2,sort_keys=True))
    if result.get('status') == 'INTERFACE_DRIFT': raise SystemExit(1)

if __name__ == '__main__': main()
