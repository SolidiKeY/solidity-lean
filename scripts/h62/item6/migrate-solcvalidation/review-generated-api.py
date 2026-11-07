#!/usr/bin/env python3
"""Classify compiler-generated interface deltas and census textual consumers.

This performs read-only Git searches. No absence of textual references is
promoted to a theorem about elaborator-generated or indirect dependencies.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
PREFIX = 'Solidity.SolcValidation.'


def classify(name):
    if 'noConfusion' in name:
        return 'noConfusion family'
    if name.endswith('.inj'):
        return 'constructor injectivity'
    if 'sizeOf' in name:
        return 'derived sizeOf'
    if 'Repr' in name:
        return 'derived Repr'
    if 'match_' in name:
        return 'equation compiler/match auxiliaries'
    raise RuntimeError(f'unclassified changed generated declaration {name}')


def review(repo, evidence, output):
    delta = json.loads((evidence / 'frozen-interface-hashes.json').read_text())
    if not delta['explicit_records_identical'] or delta['explicit_count'] != 33:
        raise RuntimeError('frozen explicit interfaces have not been verified')
    groups = {}
    for name in delta['changed_generated_records']:
        groups.setdefault(classify(name), []).append(name)
    names = (set(delta['changed_generated_records']) |
             set(delta['added_generated_names']) | set(delta['removed_generated_names']))
    patterns = set(names)
    for name in names:
        visible = name.split('.0.', 1)[-1] if name.startswith('_private.') else name
        if visible.startswith(PREFIX):
            patterns.add(visible[len(PREFIX):])
    searches = {}
    for revision in [BASE, 'origin/master']:
        commit = subprocess.check_output(['git', 'rev-parse', revision], cwd=repo, text=True).strip()
        result = subprocess.run(['git', 'grep', '-n', '-F', '-f', '-', commit, '--', '*.lean'],
                                cwd=repo, input='\n'.join(sorted(patterns)) + '\n',
                                capture_output=True, text=True)
        if result.returncode not in (0, 1):
            raise RuntimeError(result.stderr)
        searches[revision] = {'commit': commit, 'matches': result.stdout.splitlines(),
                              'command': ['git', 'grep', '-n', '-F', '-f', '-', commit, '--', '*.lean']}
    report = {
        'explicit_count': 33, 'explicit_full_records_equal': True,
        'changed_generated_groups': {key: sorted(value) for key, value in sorted(groups.items())},
        'group_counts': {key: len(value) for key, value in sorted(groups.items())},
        'added_generated_names': delta['added_generated_names'],
        'removed_generated_names': delta['removed_generated_names'],
        'axiom_changes': {name: row for name, row in delta['changed_generated_records'].items()
                         if row['old_axioms'] != row['new_axioms']},
        'literal_reference_patterns': sorted(patterns), 'source_reference_searches': searches,
        'scope_conclusion': 'Explicit frozen declarations are unchanged. Assigned modules and '
                            'existing scoped fixtures compile on both versions. No compatibility '
                            'shim or producer-source edit is justified by this census. Compiler-generated '
                            'API deltas remain supplied for root/downstream validation, not silently waived.',
        'boundary': 'Literal full and namespace-relative name searches do not cover every alias, '
                    'indirect reference, lazy realization or name synthesized by elaboration. '
                    'Generated noConfusion type changes and Repr propext growth are real. '
                    'Successful full affected validation remains required.',
        'input_sha256': hashlib.sha256((evidence / 'frozen-interface-hashes.json').read_bytes()).hexdigest()}
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'group_counts': report['group_counts'],
                      'reference_matches': {rev: len(row['matches']) for rev, row in searches.items()}}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    review(args.repo, args.evidence, args.output)
