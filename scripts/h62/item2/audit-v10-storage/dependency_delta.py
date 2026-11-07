#!/usr/bin/env python3
"""Exact Git-tree import/source delta; never transfers a kernel validation claim."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import census

MODULE = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.PIPE)


def commit(root, ref):
    return git(root, 'rev-parse', '--verify', '--end-of-options', ref + '^{commit}').decode().strip()


def imports(data):
    code = census.mask(data.decode('utf-8'))
    result = []
    for line in code.splitlines():
        words = line.split()
        if words and words[0] in ('public', 'private', 'meta') and 'import' in words:
            raise ValueError('unsupported qualified import syntax')
        if not words or words[0] != 'import':
            continue
        if len(words) < 2 or any(not MODULE.fullmatch(w) for w in words[1:]):
            raise ValueError('unsupported import syntax')
        result.extend(words[1:])
    return sorted(set(result))


def closure(root, revision, source):
    if not source.endswith('.lean') or source.startswith('/') or '..' in Path(source).parts:
        raise ValueError('invalid source path')
    pending = [source]
    hashes = {}
    external = set()
    while pending:
        path = pending.pop()
        if path in hashes:
            continue
        try:
            data = git(root, 'show', revision + ':' + path)
        except subprocess.CalledProcessError as error:
            raise ValueError('missing committed source: ' + revision + ':' + path) from error
        hashes[path] = hashlib.sha256(data).hexdigest()
        for module in imports(data):
            if module == 'Solidity' or module.startswith('Solidity.'):
                pending.append(module.replace('.', '/') + '.lean')
            else:
                external.add(module)
    return dict(sources=dict(sorted(hashes.items())), external_imports=sorted(external))


def compare(root, baseline, candidate, sources):
    baseline = commit(root, baseline)
    candidate = commit(root, candidate)
    if len(sources) != len(set(sources)):
        raise ValueError('duplicate witness source')
    rows = []
    for source in sorted(sources):
        old = closure(root, baseline, source)
        new = closure(root, candidate, source)
        a, b = old['sources'], new['sources']
        rows.append(dict(source=source, baseline=old, candidate=new,
                         changed_sources=sorted(p for p in a.keys() & b.keys() if a[p] != b[p]),
                         added_sources=sorted(b.keys() - a.keys()),
                         removed_sources=sorted(a.keys() - b.keys()),
                         external_import_list_changed=old['external_imports'] != new['external_imports'],
                         kernel_status='not-run; historical receipts unchanged'))
    return dict(schema_version=1, baseline=baseline, candidate=candidate,
                boundary='Lexical one-line import routing over exact committed source bytes only; not an elaborated Lean dependency certificate. External toolchain/package objects and generated artifacts are not compared. Equal source bytes do not transfer kernel, axiom, resource or performance acceptance.',
                rows=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', required=True)
    parser.add_argument('--candidate', default='HEAD')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(git(Path.cwd(), 'rev-parse', '--show-toplevel').decode().strip())
    output = args.output.resolve()
    if output == root or root in output.parents:
        parser.error('bulk output must be outside checkout')
    pins = json.loads((root / 'tests/h62/item2/audit-v10-storage/kernel-source-pins.json').read_text())
    result = compare(root, args.baseline, args.candidate, list(pins['sources']))
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps([dict(source=r['source'], changed=r['changed_sources'], added=r['added_sources'], removed=r['removed_sources']) for r in result['rows']], indent=2))


if __name__ == '__main__':
    main()
