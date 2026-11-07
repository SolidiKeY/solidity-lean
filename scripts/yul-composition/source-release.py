#!/usr/bin/env python3
"""Inventory committed Source dependencies; this is not kernel validation."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile


def required(selection, imports, changed):
    return sorted((reachable(selection, imports) & set(changed)) - set(selection))


def reachable(selection, imports):
    pending, seen = list(selection), set(selection)
    while pending:
        for dependency in imports.get(pending.pop(), []):
            if dependency not in seen:
                seen.add(dependency)
                pending.append(dependency)
    return seen


def import_header(source):
    """Mask nested comments; reject unsupported header import spellings."""
    text, depth, i = [], 0, 0
    while i < len(source):
        if not depth and source[i] == '"':
            text.append(' ')
            i += 1
            while i < len(source):
                char = source[i]
                text.append('\n' if char == '\n' else ' ')
                i += 1
                if char == '"':
                    break
                if char == '\\' and i < len(source):
                    text.append('\n' if source[i] == '\n' else ' ')
                    i += 1
        elif source.startswith('/-', i):
            depth += 1
            text.extend('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            text.extend('  ')
            i += 2
        elif not depth and source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0:
                end = len(source)
            text.extend(' ' * (end - i))
            i = end
        else:
            text.append('\n' if source[i] == '\n' else (' ' if depth else source[i]))
            i += 1
    if depth:
        raise ValueError('unclosed block comment')
    imports = []
    for line in ''.join(text).splitlines():
        line = line.strip()
        if not line or line == 'prelude':
            continue
        if not re.match(r'^(?:public\s+)?import\b', line):
            break
        body = re.sub(r'^(?:public\s+)?import\b', '', line).strip()
        names = body.split()
        if not names or any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\'.]*', n) for n in names):
            raise ValueError('unsupported import header: ' + line)
        imports.extend(names)
    return imports


def inventory(base, selection=None):
    git = lambda *words: subprocess.check_output(['git', *words], text=True).strip()
    base, head = git('rev-parse', base), git('rev-parse', 'HEAD')
    # Disable rename detection: renamed destinations are additions, never omitted.
    paths = git('diff', '--no-renames', '--name-only', '--diff-filter=AM', base, head,
                '--', 'Solidity', 'Solidity.lean').splitlines()
    changed = {p[:-5].replace('/', '.'): p for p in paths if p.endswith('.lean')}
    archive = subprocess.check_output(['git', 'archive', head, 'Solidity', 'Solidity.lean'])
    sources, imports = {}, {}
    with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
        for member in tree:
            if member.isfile() and member.name.endswith('.lean'):
                module = member.name[:-5].replace('/', '.')
                sources[module] = (member.name, tree.extractfile(member).read())
    for module, (_, body) in sources.items():
        imports[module] = import_header(body.decode())
    selection = sorted(changed) if selection is None else selection
    if not isinstance(selection, list) or not all(isinstance(x, str) for x in selection):
        raise ValueError('selection must be a JSON list of module names')
    visited = reachable(selection, imports)
    unknown = sorted(set(selection) - set(sources))
    missing_local = sorted(m for m in visited if (m == 'Solidity' or m.startswith('Solidity.'))
                           and m not in sources)
    stale = []
    # Check unchanged intermediates too: dirty imports cannot hide dependencies.
    for module in visited | set(changed):
        if module in sources:
            path, body = sources[module]
            if not Path(path).is_file() or Path(path).read_bytes() != body:
                stale.append(path)
    missing = required(selection, imports, changed)
    records = [dict(module=m, path=p, sha256=hashlib.sha256(sources[m][1]).hexdigest(),
                    changedDependencies=required([m], imports, changed),
                    ownerHeldSource=p.startswith('Solidity/Source/'))
               for m, p in sorted(changed.items())]
    return dict(base=base, head=head, boundary='Git HEAD dependency inventory only; no kernel or adequacy pass.',
                sourceModules=[r['module'] for r in records if r['ownerHeldSource']],
                changedModules=records, selection=selection, missingChangedDependencies=missing,
                unknownModules=unknown, missingLocalImports=missing_local, staleSources=sorted(stale),
                selectionComplete=not (missing or unknown or missing_local or stale))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', default='origin/master')
    parser.add_argument('--output', required=True)
    parser.add_argument('--selection', help='JSON list of modules proposed for standalone import')
    args = parser.parse_args()
    selection = json.loads(Path(args.selection).read_text()) if args.selection else None
    report = inventory(args.base, selection)
    Path(args.output).write_text(json.dumps(report, indent=2) + '\n')
    print(('PASS: changed import closure inventoried; not kernel validation' if report['selectionComplete']
           else 'FAIL: incomplete/stale standalone selection; see ' + args.output))
    return 0 if report['selectionComplete'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
