#!/usr/bin/env python3
"""Index component receipts without promoting them to statement acceptance.

Saved kernel snapshots remain snapshot-qualified. Matching names/type hashes
is accounting evidence, not a fresh kernel run or semantic fidelity proof.
"""
import argparse
import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def build(repo, frozen, snapshots, manifests):
    lexical = json.loads(frozen.read_text())['declarations']
    captures = [(p, row) for p in snapshots
                for row in json.loads(p.read_text())['declarations']]
    rows = []
    seen = set()
    for manifest in manifests:
        receipt = json.loads(manifest.read_text())
        for name, expected in receipt['source_bindings'].items():
            path = (repo / name).resolve()
            require(path.is_relative_to(repo.resolve()), 'source outside repository')
            require(digest(path) == expected, 'source binding mismatch: ' + name)
        for evidence in receipt['evidence']:
            path = Path(evidence['path'])
            require(path.stat().st_size == evidence['bytes'], 'evidence size mismatch')
            require(digest(path) == evidence['sha256'], 'evidence hash mismatch')
        targets = receipt.get('original_targets', [])
        if 'original_target' in receipt:
            require(not targets, 'mixed target fields')
            targets = [receipt['original_target']]
        require(targets, 'empty target receipt')
        for target in targets:
            require(target not in seen, 'duplicate target: ' + target)
            seen.add(target)
            matches = [r for r in lexical if r['name_candidate'] == target]
            require(len(matches) == 1, 'nonunique or absent frozen target: ' + target)
            candidates = [(p, r) for p, r in captures if r['name'] == target]
            require(len(candidates) == 1, 'nonunique or absent captured target: ' + target)
            snapshot, kernel = candidates[0]
            module = matches[0]['file'][:-5].replace('/', '.')
            require(kernel['module'] == module, 'captured module mismatch')
            require(kernel['is_theorem'], 'target is not a captured theorem')
            require(hashlib.sha256(kernel['type_expr'].encode()).hexdigest() ==
                    kernel['type_sha256'], 'kernel type hash mismatch')
            rows.append(dict(target=target, lexical_id=matches[0]['id'],
                             lexical_signature_sha256=matches[0]['signature_sha256'],
                             kernel_snapshot=str(snapshot),
                             kernel_type_sha256=kernel['type_sha256'],
                             proof_manifest=str(manifest), proof_manifest_sha256=digest(manifest),
                             status='COMPONENT_RECEIPT_LINKED_FIDELITY_PENDING'))
    inputs = [frozen, *snapshots, *manifests]
    return dict(status='ACCOUNTING_ONLY', indexed_targets=len(rows),
                new_joint_witnesses=0, full_statement_fidelity_acceptances=0,
                fresh_kernel_checks=0, targets=rows,
                inputs=[dict(path=str(p), sha256=digest(p)) for p in inputs])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--frozen', type=Path, required=True)
    parser.add_argument('--kernel', type=Path, action='append', required=True)
    parser.add_argument('--manifest', type=Path, action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = build(args.repo, args.frozen, args.kernel, args.manifest)
    with args.output.open('x') as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
