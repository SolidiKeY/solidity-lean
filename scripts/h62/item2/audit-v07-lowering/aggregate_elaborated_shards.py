#!/usr/bin/env python3
"""Revalidate disjoint live shards and account for every frozen module.

Guarded regression: duplicate, omitted, drifted or failed shards cannot inflate
coverage. Unchanged-source inspection is not original semantic fidelity or a
simultaneous witness. Original pending ledgers are never rewritten.
"""
import argparse
import hashlib
import json
from pathlib import Path
from read_elaborated_subset import inspect


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def partition(repo, ledger, plan):
    original = {r['path'][:-5].replace('/', '.'):r for r in ledger['modules']}
    selected = set()
    for entry in plan:
        pins = json.loads((Path(entry['folder'])/'pins.json').read_text())
        for module in pins['modules']:
            if module not in original or module in selected:
                raise ValueError('unknown or duplicate selected module')
            selected.add(module)
    unchanged, drifted = set(), []
    for module, row in original.items():
        current = sha(repo/row['path'])
        if current == row['sha256']:
            unchanged.add(module)
        else:
            drifted.append(dict(path=row['path'], frozen_sha256=row['sha256'],
                                current_sha256=current, source_candidate_count=row['candidate_count']))
    if selected != unchanged:
        raise ValueError('unchanged-module coverage mismatch')
    return unchanged, drifted


def aggregate(repo, inventory, plan):
    receipt = json.loads((repo/'tests/h62/item2/audit-v07-lowering/frozen-reproduction.json').read_text())
    if sha(inventory) != receipt['artifacts']['source-inventory.json']:
        raise ValueError('frozen inventory hash mismatch')
    ledger = json.loads(inventory.read_text())
    selected, drifted = partition(repo, ledger, plan)
    results, statements = [], {}
    for entry in plan:
        result = inspect(repo, Path(entry['folder']), Path(entry['log']), inventory, Path(entry['gate']))
        saved = json.loads(Path(entry['report']).read_text())
        if result != saved:
            raise ValueError('saved report differs from current strict revalidation')
        for row in result['statements']:
            if row['name'] in statements:
                raise ValueError('duplicate source theorem identity')
            statements[row['name']] = row
        results.append(dict(folder=entry['folder'], report_sha256=sha(Path(entry['report'])),
                            gate_sha256=sha(Path(entry['gate'])),
                            selected_modules=result['selected_modules'],
                            matched_source_theorems=result['matched_source_theorems'],
                            total_exported_constants=result['total_exported_constants']))
    expected = {r['source_qualified_name'] for r in ledger['theorems']
                if r['path'][:-5].replace('/', '.') in selected}
    if set(statements) != expected:
        raise ValueError('source theorem identity coverage mismatch')
    return dict(schema_version=1,
                boundary='Successful live unchanged-source shards; not original semantic fidelity, interface membership, feasibility or full acceptance.',
                frozen_inventory_sha256=sha(inventory), frozen_module_count=ledger['module_count'],
                frozen_candidate_count=ledger['theorem_count'], selected_module_count=len(selected),
                matched_source_theorems=len(statements),
                binder_count=sum(len(r['binders']) for r in statements.values()),
                proof_binder_count=sum(b['proof_binder'] for r in statements.values() for b in r['binders']),
                total_exported_constants=sum(r['total_exported_constants'] for r in results),
                drifted_module_count=len(drifted), drifted_source_candidates=sum(r['source_candidate_count'] for r in drifted),
                drifted_sources=drifted, shards=results,
                statements=[statements[name] for name in sorted(statements)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['repo','inventory','plan','output']:
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    repo=args.repo.resolve()
    if args.output.resolve().is_relative_to(repo) or args.output.exists():
        raise ValueError('new external output file required')
    result=aggregate(repo,args.inventory,json.loads(args.plan.read_text()))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['statements','shards','drifted_sources']},indent=2))
