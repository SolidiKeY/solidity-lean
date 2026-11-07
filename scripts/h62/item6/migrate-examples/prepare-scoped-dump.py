#!/usr/bin/env python3
"""Generate an off-Git audit fixture importing exactly the frozen assigned scope.

No project root, registration or model declaration changes. Extra example modules
reachable from an original root fail rather than being silently filtered out.
"""
import argparse
import hashlib
import json
import pathlib
from census import BASE
from dependencies import Tree, closure


def render(template, scope, report):
    expected = {row['module'] for row in scope['modules']}
    if scope['base'] != BASE or len(expected) != len(scope['modules']):
        raise ValueError('wrong base or duplicate original module')
    if report['base'] != BASE or report['unresolved_imports']:
        raise ValueError('wrong base or unresolved imports')
    actual = {row['module'] for row in report['modules']
              if row['module'].startswith('Solidity.Examples.')}
    if actual != expected:
        raise ValueError('missing original or additional transitive example module')
    if template.count('import SolidityExamples\n') != 1:
        raise ValueError('unexpected audit template import shape')
    if any(not name.startswith('Solidity.Examples.') or any(c.isspace() for c in name) for name in expected):
        raise ValueError('invalid original module name')
    return template.replace('import SolidityExamples\n', ''.join('import ' + name + '\n' for name in sorted(expected)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument('--census', type=pathlib.Path, required=True)
    parser.add_argument('--stdlib', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    parser.add_argument('--manifest', type=pathlib.Path, required=True)
    args = parser.parse_args()
    scope = json.loads(args.census.read_text())
    base = Tree(args.root, BASE)
    original = sorted(path for path in base.blobs if path.startswith('Solidity/Examples/') and path.endswith('.lean'))
    if len(original) != 354 or sorted(row['path'] for row in scope['modules']) != original:
        raise ValueError('census must contain all 354 original files exactly')
    for row in scope['modules']:
        if row['module'] != row['path'][:-5].replace('/', '.') or row['source_sha256'] != hashlib.sha256(base.read(row['path'])).hexdigest():
            raise ValueError('census differs from frozen Git blobs')
    report = closure(args.root, 'HEAD', args.stdlib)
    template_path = args.root / 'tests/h62/item6/migrate-examples/InterfaceDump.lean'
    template = template_path.read_text()
    rendered = render(template, scope, report)
    for path in (args.output, args.manifest):
        if path.resolve().is_relative_to(args.root.resolve()):
            raise ValueError('output and manifest must be outside the checkout')
    if args.output.resolve() == args.manifest.resolve():
        raise ValueError('output and manifest must differ')
    args.output.write_text(rendered)
    manifest = {'schema_version': 1, 'base': BASE, 'source_commit': report['source_commit'],
                'original_scope_modules': len(scope['modules']), 'local_closure': report['local_closure'],
                'additional_transitive_examples': [],
                'template_sha256': hashlib.sha256(template.encode()).hexdigest(),
                'census_sha256': hashlib.sha256(args.census.read_bytes()).hexdigest(),
                'output': str(args.output.resolve()),
                'output_sha256': hashlib.sha256(rendered.encode()).hexdigest(),
                'boundary': 'Exact original imports; no filtering of declarations; successful compilation, complete footer validation and imported-private visibility assessment still required.'}
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps(manifest))


if __name__ == '__main__':
    main()
