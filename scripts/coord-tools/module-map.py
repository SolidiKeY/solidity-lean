#!/usr/bin/env python3
"""module-map.py [BASE]: rows of the per-area module map for the modules added since BASE.

Every Lean file added under `Solidity/` or `Bridge/SolidityBridge/` between
the merge-base of BASE (default `origin/master`) and the working tree needs a
row in one of `docs/module-map/*.md` (or in its fragments,
`docs/module-map/<area>.d/`). For each added module without one, this
prints the fragment of the current lane (named after the branch) in the area
whose existing rows share the longest directory prefix with it and a draft row
from its `/-!` docstring's first sentence, e.g.

    docs/module-map/v10-storage.d/<lane>.md: | `<path of the module>` | ... |

Append the row to that fragment and run `scripts/coord-tools/fragments.sh`.

A row names a module by its path under Solidity/ (with or without `.lean`),
in a brace group (`A/{B,C}`), by a glob (`A/*`, `A/**`, `A/B*.lean`) or by
its directory (`A/`); Bridge modules with or without `Bridge/SolidityBridge/`. Exit 0 = every added module has a row,
1 = rows missing (listed), 2 = usage or setup error.
"""
import fnmatch, pathlib, re, subprocess, sys


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, text=True, check=True).stdout


def stem(path):
    rel = path[len('Solidity/'):] if path.startswith('Solidity/') else path
    return rel[:-len('.lean')]


def named(text):
    """The module stems, globs and directory prefixes a file's rows name."""
    out = set()
    for code in re.findall(r'`([^`]+)`', text):
        code = code.replace('Solidity/', '', 1) if code.startswith('Solidity/') else code
        m = re.fullmatch(r'([\w/.*]*)\{([\w,/.*]+)\}([\w/.*]*)', code)
        names = [m.group(1) + x + m.group(3) for x in m.group(2).split(',')] if m else [code]
        for n in names:
            if not re.fullmatch(r'[\w/.*]+', n): continue
            out.add(n[:-len('.lean')] if n.endswith('.lean') else n)
    return out


def covered(stem, names):
    for s in (stem, stem.removeprefix('Bridge/'), stem.removeprefix('Bridge/SolidityBridge/')):
        if s in names: return True
        for n in names:
            # A directory or glob row covers its subtree; a bare `*` or `Bridge/`
            # in prose names no module.
            if n.endswith('/') and n.strip('/') not in ('', 'Bridge', 'Bridge/SolidityBridge') and s.startswith(n): return True
            if '*' in n and '/' in n.split('*')[0] and fnmatch.fnmatchcase(s, n.replace('**', '*')): return True
    return False


def main():
    if len(sys.argv) > 2:
        print(__doc__, file=sys.stderr); return 2
    root = pathlib.Path(git('rev-parse', '--show-toplevel').strip())
    base = git('merge-base', sys.argv[1] if len(sys.argv) > 1 else 'origin/master', 'HEAD').strip()
    import os; os.chdir(root)
    added = set(git('diff', '--name-only', '--diff-filter=A', '--no-renames', base, '--', 'Solidity', 'Bridge/SolidityBridge').split())
    added |= set(git('ls-files', '--others', '--exclude-standard', '--', 'Solidity', 'Bridge/SolidityBridge').split())
    added = sorted(p for p in added if p.endswith('.lean') and not p.startswith('Solidity/Scratch/') and pathlib.Path(p).is_file())
    areas = {f: named(f.read_text() + ''.join(g.read_text() for g in sorted(f.with_suffix('.d').rglob('*.md'))))
             for f in sorted(pathlib.Path('docs/module-map').glob('*.md'))}
    branch = subprocess.run(['git', 'symbolic-ref', '-q', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()
    lane = re.sub(r'[^a-z0-9-]+', '-', branch.split('/')[-1].lower()).strip('-') or 'LANE'
    lane = lane if lane[:1].isalpha() else 'lane-' + lane
    if not areas:
        print('module-map: no docs/module-map/*.md', file=sys.stderr); return 2
    have = set().union(*areas.values())
    missing = 0
    for p in added:
        s = stem(p)
        if covered(s, have):
            continue
        missing += 1
        parts = s.removeprefix('Bridge/').split('/')
        def score(names):
            # the longest shared directory prefix, then how many rows share it
            best, count = 0, 0
            for n in names:
                k = 0
                for x, y in zip(parts[:-1], n.split('/')[:-1]):
                    if x != y: break
                    k += 1
                if k > best: best, count = k, 1
                elif k == best and k: count += 1
            return best, count
        area = max(areas, key=lambda f: score(areas[f]))
        doc = re.search(r'/-!(.*?)-/', pathlib.Path(p).read_text(), re.S)
        text = ' '.join(doc.group(1).split()) if doc else ''
        text = re.sub(r'^#+ [^.]*?(?=[A-Z][a-z])', '', text).strip()
        first = re.split(r'(?<=\.)\s', text)[0] if text else 'TODO: what it defines.'
        print(f'{area.with_suffix(".d")}/{lane}.md: | `{s}.lean` | {first} |')
    return 1 if missing else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as e:
        print('module-map: ' + (e.stderr or str(e)).strip(), file=sys.stderr); sys.exit(2)
