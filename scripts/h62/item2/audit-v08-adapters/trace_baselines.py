#!/usr/bin/env python3
"""Git per-hunk provenance only; never semantic or kernel equivalence evidence.

Follow an actual parent path from the frozen commit to the reviewed snapshot.
Track original-line deletions and surviving-line introductions across its exact
Git hunks; also retain the requested per-file log and target blame attribution.
Every cited commit must be an ancestor of the pinned master observation.
"""
import argparse, hashlib, json, re, subprocess
from pathlib import Path

HUNK = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', re.M)

def hunks(patch):
    return [(int(m[1]), int(m[2] or 1), int(m[3]), int(m[4] or 1))
            for m in HUNK.finditer(patch)]

def offset(start, count):
    return start - 1 if count else start

def advance(atoms, new_lines, changes, commit, removed):
    result, cursor = [], 0
    for old_start, old_count, new_start, new_count in changes:
        old_at, new_at = offset(old_start, old_count), offset(new_start, new_count)
        if old_at < cursor or old_at + old_count > len(atoms):
            raise ValueError('invalid/overlapping Git hunk range')
        result.extend(atoms[cursor:old_at])
        for atom in atoms[old_at:old_at + old_count]:
            if atom['base_line'] is not None:
                removed.setdefault(atom['base_line'], commit)
        result.extend(dict(text=line, introduced=commit, base_line=None)
                      for line in new_lines[new_at:new_at + new_count])
        cursor = old_at + old_count
    result.extend(atoms[cursor:])
    if [a['text'] for a in result] != new_lines:
        raise ValueError('Git hunk replay differs from committed file')
    return result

def trace(repo, base, target, master, paths):
    def git(*args):
        return subprocess.check_output(['git', '-C', str(repo), *args], text=True)
    def ancestor(a, b):
        result = subprocess.run(['git', '-C', str(repo), 'merge-base', '--is-ancestor', a, b],
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if result.returncode not in (0, 1):
            raise ValueError('Git ancestry check failed')
        return result.returncode == 0
    base, target, master = [git('rev-parse', x + '^{commit}').strip() for x in (base, target, master)]
    if not ancestor(base, target) or not ancestor(target, master):
        raise ValueError('reviewed snapshot is not on the required ancestry')
    if len(paths) != len(set(paths)):
        raise ValueError('duplicate path')
    for path in paths:
        p = Path(path)
        if p.is_absolute() or '..' in p.parts or not path.endswith('.lean') or p.parts[0] not in ('Solidity', 'Bridge'):
            raise ValueError('unsupported committed source path')
    edges, current, ancestry = [], target, {}
    while current != base:
        parents = git('rev-list', '--parents', '-n', '1', current).split()[1:]
        chosen = None
        for parent in parents:
            if parent not in ancestry: ancestry[parent] = ancestor(base, parent)
            if ancestry[parent]: chosen = parent; break
        if chosen is None: raise ValueError('cannot find a real parent path to frozen base')
        edges.append((chosen, current)); current = chosen
    edges.reverse()
    changed = {}
    for parent, child in edges:
        changed[child] = set(git('diff', '--no-ext-diff', '--no-renames', '--name-only', parent, child, '--', *paths).splitlines())
    checked = {}
    def check(commit):
        if commit not in checked: checked[commit] = ancestor(commit, master)
        if not checked[commit]: raise ValueError('cited introducing commit is not on master: ' + commit)
    rows = []
    for path in paths:
        short_log = git('log', '--format=%h', base + '..' + target, '--', path).splitlines()
        history = git('log', '--format=%H', base + '..' + target, '--', path).splitlines()
        for commit in history: check(commit)
        old = git('show', base + ':' + path).splitlines(keepends=True)
        atoms = [dict(text=line, introduced=base, base_line=i) for i, line in enumerate(old, 1)]
        removed = {}
        for parent, child in edges:
            if path not in changed[child]: continue
            new = git('show', child + ':' + path).splitlines(keepends=True)
            patch = git('diff', '--no-ext-diff', '--no-renames', '--unified=0', parent, child, '--', path)
            atoms = advance(atoms, new, hunks(patch), child, removed)
        patch = git('diff', '--no-ext-diff', '--no-renames', '--unified=0', base, target, '--', path)
        traces = []
        for old_start, old_count, new_start, new_count in hunks(patch):
            deleted = [removed.get(i) for i in range(old_start, old_start + old_count)]
            added = [a['introduced'] for a in atoms[offset(new_start, new_count):offset(new_start, new_count) + new_count]]
            # An unresolved line identity is not silently accepted.
            traced = all(c is not None and c != base for c in deleted + added) and bool(deleted + added)
            if traced:
                for commit in deleted + added: check(commit)
            blame = []
            if new_count:
                text = git('blame', '--line-porcelain', '-L', str(new_start) + ',+' + str(new_count), target, '--', path)
                blame = sorted(set(re.findall(r'^([0-9a-f]{40}) \d+ \d+', text, re.M)))
                for commit in blame: check(commit)
            traces.append(dict(old_start=old_start, old_count=old_count, new_start=new_start, new_count=new_count,
                               deletion_edge_commits=sorted(set(c for c in deleted if c)),
                               surviving_introduction_edge_commits=sorted(set(added)),
                               target_blame_commits=blame, traced=traced))
        citations = sorted(set(history + [c for h in traces for key in ('deletion_edge_commits', 'surviving_introduction_edge_commits', 'target_blame_commits') for c in h[key]]))
        rows.append(dict(file=path, log_short=short_log, history_commits=history, hunks=traces,
                         all_hunks_traced=bool(traces) and all(h['traced'] for h in traces),
                         citations=citations, target_blob=git('rev-parse', target + ':' + path).strip(),
                         patch_sha256=hashlib.sha256(patch.encode()).hexdigest()))
    return dict(base=base, target=target, master_observed=master, parent_path=edges, files=rows,
                all_traced=all(r['all_hunks_traced'] for r in rows),
                claim='Master-history provenance only; no semantic equivalence, premise inhabitance or kernel acceptance.')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ('repo', 'paths', 'out'): ap.add_argument('--' + key, type=Path, required=True)
    ap.add_argument('--base', required=True); ap.add_argument('--target', required=True)
    ap.add_argument('--master', default='origin/master')
    a = ap.parse_args(); repo, out = a.repo.resolve(), a.out.resolve()
    if out == repo or repo in out.parents: raise SystemExit('Bulk trace output must stay off Git')
    result = trace(repo, a.base, a.target, a.master, json.loads(a.paths.read_text()))
    out.parent.mkdir(parents=True, exist_ok=True); out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(files=len(result['files']), all_traced=result['all_traced'])))
    if not result['all_traced']: raise SystemExit(1)

if __name__ == '__main__': main()
