#!/usr/bin/env python3
"""Account for saved lexical/kernel name candidates without claiming fidelity."""
import argparse
import collections
import gzip
import hashlib
import json
from pathlib import Path
import re
from generate_calldata_census import MODULES


def normalize(row):
    name, module = row['name'], row['module']
    if not name.startswith('_private.'):
        return name, False
    match = re.fullmatch(r'_private\.' + re.escape(module) + r'\.[0-9]+\.(.+)', name)
    return (match.group(1), True) if match else (None, True)


def reconcile(lexical, kernel, modules=MODULES):
    source = lexical['declarations']
    rows = kernel['declarations']
    if len({r['id'] for r in source}) != len(source):
        raise ValueError('Duplicate lexical declaration IDs')
    if not rows or len({r['name'] for r in rows}) != len(rows):
        raise ValueError('Empty or duplicate kernel declaration names')
    if {r['module'] for r in rows} != set(modules):
        raise ValueError('Kernel snapshot module set differs from this scope')
    for row in rows:
        if not row['type_expr'] or hashlib.sha256(row['type_expr'].encode()).hexdigest() != row['type_sha256']:
            raise ValueError('Kernel type digest mismatch')
    paths = {module.replace('.', '/') + '.lean' for module in modules}
    candidates = collections.defaultdict(list)
    kernel_entries = {}
    for row in rows:
        name, private = normalize(row)
        entry = {'name': row['name'], 'module': row['module'], 'private': private,
                 'normalized_name_candidate': name, 'type_sha256': row['type_sha256'],
                 'lexical_ids': [], 'audit_status': 'PENDING', 'owner_status': 'UNCONFIRMED',
                 'source_role': row.get('source_role', row.get('kind', 'UNKNOWN'))}
        kernel_entries[row['name']] = entry
        if name is not None:
            candidates[(row['module'].replace('.', '/') + '.lean', name)].append(entry)
    output = []
    for row in source:
        if row['file'] not in paths:
            continue
        matches = candidates[(row['file'], row['name_candidate'])]
        status = ('NO_NAME_MATCH' if not matches else 'AMBIGUOUS_NAME' if len(matches) > 1
                  else 'PRIVATE_NAME_CANDIDATE' if matches[0]['private'] else 'PUBLIC_NAME_CANDIDATE')
        for candidate in matches:
            candidate['lexical_ids'].append(row['id'])
        output.append({'id': row['id'], 'file': row['file'], 'name_candidate': row['name_candidate'],
                       'name_status': status, 'kernel_candidates': [r['name'] for r in matches],
                       'lexical_signature_unresolved': row['signature_source'] is None,
                       'statement_fidelity': 'PENDING', 'witness_status': 'PENDING',
                       'owner_status': 'UNCONFIRMED',
                       'snapshot_owner_status': row.get('owner_status'),
                       'snapshot_owner_relay': row.get('owner_relay')})
    return {'status': 'NAME_RECONCILIATION_ONLY', 'complete_interface_inventory': False,
            'new_witnesses': 0, 'statement_fidelity_verified': 0,
            'kernel_scope_total': len(rows),
            'kernel_role_counts': dict(collections.Counter(r['source_role'] for r in kernel_entries.values())),
            'lexical_input_total': len(source), 'lexical_scope_total': len(output),
            'lexical_outside_scope': len(source) - len(output),
            'name_status_counts': dict(collections.Counter(r['name_status'] for r in output)),
            'lexical': output, 'kernel': list(kernel_entries.values()),
            'kernel_only_pending': [r['name'] for r in kernel_entries.values() if not r['lexical_ids']],
            'boundary': 'Name/provenance candidates only. No parsed-type equivalence, feasible joint premises, owner acceptance or current-source validation follows.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ('lexical', 'kernel', 'out'):
        parser.add_argument('--' + key, type=Path, required=True)
    args = parser.parse_args()
    with gzip.open(args.kernel, 'rt', encoding='utf-8') as source:
        kernel = json.load(source)
    output = reconcile(json.loads(args.lexical.read_text()), kernel)
    output['inputs'] = {key: {'path': str(path.resolve()), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                        for key, path in [('lexical', args.lexical), ('kernel', args.kernel)]}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open('x') as sink:
        json.dump(output, sink, ensure_ascii=False, indent=2)
        sink.write('\n')
    print(json.dumps({key: output[key] for key in ('status', 'lexical_scope_total', 'name_status_counts', 'new_witnesses', 'statement_fidelity_verified')}))


if __name__ == '__main__':
    main()
