#!/usr/bin/env python3
"""Reproducible explicit-import closure from committed Git blobs, not a Lean proof.

Scope always comes from the frozen base. New files in an integration tree are
reported separately; no original module can disappear silently. Implicit Init
imports and imports produced by arbitrary commands are outside this scanner.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tomllib

from census import BASE, strip_comments

IDENT = r'(?:«[^»]+»|[^\W\d]\w*)(?:\.(?:«[^»]+»|[^\W\d]\w*))*'
HEADER_IMPORT = re.compile(r'(?:(?:public)\s+)?(?:(?:meta)\s+)?import\s+(?:all\s+)?(?P<module>' + IDENT + r')')


def header_imports(source):
    """Read one name per import, as in both pinned Parser.Module versions.

    This inventories already valid sources; it is not a replacement for Lean's
    parser. Stop at the first non-header command, including punctuation-led
    commands, without interpreting the body as imports.
    """
    clean = strip_comments(source)
    pos = 0
    for keyword in ('module', 'prelude'):
        pos += len(clean[pos:]) - len(clean[pos:].lstrip())
        match = re.match(keyword + r'\b', clean[pos:])
        if match:
            pos += match.end()
    result = []
    while True:
        pos += len(clean[pos:]) - len(clean[pos:].lstrip())
        match = HEADER_IMPORT.match(clean, pos)
        if match is None:
            if re.match(r'(?:(?:public)\s+)?(?:(?:meta)\s+)?import\b', clean[pos:]):
                raise ValueError('incomplete import directive')
            break
        result.append(match.group('module'))
        pos = match.end()
        if pos < len(clean) and not clean[pos].isspace():
            raise ValueError('unsupported punctuation in import directive')
    return result


def module_path(module):
    # Name components may contain literal dots when quoted, e.g. «a.b».C.
    parts = re.findall(r'«[^»]+»|[^.]+', module)
    return '/'.join(p.removeprefix('«').removesuffix('»') for p in parts) + '.lean'


class Tree:
    def __init__(self, root, ref):
        self.root = root
        self.commit = self.git('rev-parse', '--verify', ref + '^{commit}').decode().strip()
        entries = self.git('ls-tree', '-rz', '--full-tree', self.commit).split(b'\0')
        self.blobs = {}
        for entry in entries:
            if not entry:
                continue
            metadata, path = entry.split(b'\t', 1)
            mode, kind, oid = metadata.split()
            if kind == b'blob':
                self.blobs[path.decode()] = oid.decode()
        self.cached = {}

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root)

    def read(self, path):
        oid = self.blobs[path]
        if oid not in self.cached:
            self.cached[oid] = self.git('cat-file', 'blob', oid)
        return self.cached[oid]

    def dirs(self):
        config = tomllib.loads(self.read('lakefile.toml').decode())
        return sorted({'.'} | {x.get('srcDir', '.') for x in config.get('lean_lib', [])})

    def resolve(self, module, dirs):
        relative = module_path(module)
        matches = [str(pathlib.PurePosixPath(d) / relative) for d in dirs
                   if str(pathlib.PurePosixPath(d) / relative) in self.blobs]
        if len(matches) > 1:
            raise ValueError(f'ambiguous module {module}: {matches}')
        return matches[0] if matches else None


def closure(root, ref, stdlib):
    base = Tree(root, BASE)
    tree = Tree(root, ref)
    scope = sorted(p for p in base.blobs if p.startswith('Solidity/Examples/') and p.endswith('.lean'))
    missing = sorted(set(scope) - set(tree.blobs))
    if missing:
        raise ValueError(f'missing original scope: {missing}')
    dirs = tree.dirs()
    scope_modules = {p[:-5].replace('/', '.') for p in scope}
    pending = list(sorted(scope_modules, reverse=True))
    seen, rows, std, unresolved = set(), [], set(), set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = tree.resolve(module, dirs)
        if path is None:
            artifact = stdlib / (module_path(module)[:-5] + '.olean')
            if artifact.is_file():
                std.add(module)
            else:
                unresolved.add(module)
            continue
        raw = tree.read(path)
        imports = header_imports(raw.decode())
        rows.append({'module': module, 'path': path,
                     'source_sha256': hashlib.sha256(raw).hexdigest(),
                     'in_original_scope': module in scope_modules, 'imports': imports})
        pending.extend(sorted(set(imports) - seen, reverse=True))
    rows.sort(key=lambda x: x['module'])
    changed = [p for p in scope if base.blobs[p] != tree.blobs[p]]
    added = sorted(p for p in tree.blobs if p.startswith('Solidity/Examples/') and p.endswith('.lean') and p not in scope)
    return {'schema_version': 1, 'base': BASE, 'source_commit': tree.commit,
            'boundary': 'Explicit source-header imports of already-valid sources only; stdlib leaf classification checks artifact presence, not validity; no elaborated API, implicit Init closure, axiom or semantic proof.',
            'scope_modules': len(scope), 'local_closure': len(rows),
            'external_local_modules': sum(not r['in_original_scope'] for r in rows),
            'source_dirs': dirs, 'changed_original_examples': changed,
            'additional_examples_outside_original_scope': added,
            'stdlib_artifact_root': str(stdlib.resolve()),
            'stdlib_leaves': sorted(std), 'unresolved_imports': sorted(unresolved), 'modules': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument('--ref', default=BASE)
    parser.add_argument('--stdlib', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    if not (args.stdlib / 'Init.olean').is_file():
        parser.error('--stdlib must name an installed Lean lib/lean directory')
    data = closure(args.root, args.ref, args.stdlib)
    args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: data[k] for k in ('source_commit', 'scope_modules', 'local_closure', 'external_local_modules', 'unresolved_imports')}))
    if data['unresolved_imports']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
