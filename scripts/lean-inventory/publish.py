#!/usr/bin/env python3
"""Publish the accepted family classification of a census (plan step k1r-lean-inventory-revalidate).

    python3 -B scripts/lean-inventory/publish.py --census scripts/lean-inventory.json \
        --baseline OLD.json --output scripts/lean-inventory/classification.json [--check]

The census (`inventory.py` output, about 1.3 MB) is over the repository's 200 KB blob cap
(scripts/hygiene/check.py), so it stays out of Git (H145/H44) and this file binds it by
size and sha256. The published file is derived from the census bytes alone: the family
verdicts under the unchanged criteria of `classify.py`, the recovery pin, the orphan
families with their members and deletion dependents, the scope of the standing orphan
deletion authorization (H721), and a re-validation against a baseline census (verdict
changes per family). `--check` regenerates it in memory and fails on any difference;
`consistent()` checks the published file alone (no census needed).
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import classify as CL  # noqa: E402

SCHEMA = 'solidity-lean/lean-inventory-classification'
VERSION = 1
CENSUS_SCHEMA = 'solidity-lean/lean-inventory'
CAP_BYTES = 200 * 1024  # scripts/hygiene/check.py LIMIT_BYTES
FAMILY_FIELDS = ['family', 'area', 'verdict', 'lines', 'decls', 'keep', 'ownerNeeded',
                 'orphan', 'unresolved']
AUTHORIZATION = {
    'decision': 'H721',
    'grant': 'Deleting certified orphan families is authorized (blanket) with recovery pins and '
             'unchanged gates.',
    'steps': ['c1', 'c2', 'c3', 'y2', 'd1', 'd2'],
    'covers': 'exactly the families in `orphans` below, at their recovery pin',
    'conditions': [
        'Delete a whole family: its member modules (and controls/pins) together.',
        'A family whose dependents are not empty cannot be deleted alone: in the same change '
        'remove or refactor each dependent (Lean importers and name mentions, and non-Lean '
        'files outside docs/ naming its paths or modules); standalone families have none.',
        'Re-check against the census at the step\'s own merge base: a family whose verdict is '
        'no longer orphan there is not covered.',
        'keep, ownerNeeded and unresolved families are not covered; unresolved stays excluded '
        'until its gaps are closed.',
        'No statement, budget, gate or criterion changes; gates must pass unchanged.',
        'Certified orphan means a deletion candidate under the recorded facts, not deletion '
        'evidence: the kernel theorem certifies only the abstract certificate reasoning.',
    ],
}


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def binding(raw, census, path):
    return {'path': path, 'bytes': len(raw), 'sha256': sha256_bytes(raw),
            'schema': census['schema'], 'version': census['version'],
            'revision': census['revision'], 'lean_tree_id': census['lean_tree_id'],
            'toolchain': census['toolchain'],
            'extractor_blob': census['extraction']['extractor_blob'],
            'graph_sha256': census['extraction']['graph_sha256'],
            'options': census.get('options')}


def family_row(f):
    return [f['family'], f['area'], f['verdict'], f['lines'], f['decls']] + \
        [f['counts'][v] for v in CL.VERDICTS]


def revalidation(old, new):
    """Family-level comparison of a baseline census with the current one."""
    a = {f['family']: f for f in old['families']}
    b = {f['family']: f for f in new['families']}
    changed = [[n, a[n]['verdict'], b[n]['verdict']] for n in sorted(a.keys() & b.keys())
               if a[n]['verdict'] != b[n]['verdict']]
    resized = sum(1 for n in a.keys() & b.keys() if a[n]['verdict'] == b[n]['verdict']
                  and (a[n]['lines'], a[n]['decls']) != (b[n]['lines'], b[n]['decls']))
    oa, ob = set(old['certified_orphan_families']), set(new['certified_orphan_families'])
    return {
        'baseline_revision': old['revision'],
        'drifted': old['lean_tree_id'] != new['lean_tree_id'],
        'families': {'baseline': len(a), 'current': len(b),
                     'unchanged_verdict': len(a.keys() & b.keys()) - len(changed),
                     'same_verdict_resized': resized},
        'verdict_changes': changed,
        'removed_families': [[n, a[n]['verdict']] for n in sorted(a.keys() - b.keys())],
        'added_families': [[n, b[n]['verdict']] for n in sorted(b.keys() - a.keys())],
        'orphans': {'kept': sorted(oa & ob), 'no_longer_orphan': sorted(oa - ob),
                    'new': sorted(ob - oa)},
        'totals': {'baseline': old['totals']['verdicts'], 'current': new['totals']['verdicts'],
                   'baseline_decls': old['totals']['decl_verdicts'],
                   'current_decls': new['totals']['decl_verdicts']},
    }


def publish(raw, census_path, base_raw=None, base_path=None):
    census = json.loads(raw)
    if census.get('schema') != CENSUS_SCHEMA:
        raise SystemExit('publish: not a lean-inventory census: ' + census_path)
    fams = census['families']
    orphans = []
    for f in fams:
        if f['verdict'] != 'orphan':
            continue
        orphans.append({'family': f['family'], 'area': f['area'], 'lines': f['lines'],
                        'decls': f['decls'], 'pseudo': f['pseudo'],
                        'members': [[m[0], m[1], m[2]] for m in f['members']],
                        'dependents': f['dependents'],
                        'recovery': census['recovery']['revision']})
    out = {
        'schema': SCHEMA, 'version': VERSION,
        'census': binding(raw, census, census_path) | {
            'storage': f'out of Git: over the {CAP_BYTES}-byte blob cap of scripts/hygiene/check.py '
                       '(H145/H44); bound here by size and sha256',
            'regenerate': census['regenerate']},
        'baseline': (binding(base_raw, json.loads(base_raw), base_path)
                     if base_raw is not None else None),
        'criteria': {
            'rule': 'H490 declaration-level verdicts (keep, ownerNeeded, orphan, unresolved) '
                    'of Solidity.Goals.Inventory, family verdict = classify.family_verdict '
                    '(keep, else unresolved, else ownerNeeded, else orphan); unchanged',
            'proof': census['goal'],
            'scope': census['scope'],
            'limitations': census['limitations'],
        },
        'recovery': census['recovery'],
        'authorization': dict(AUTHORIZATION, census_options=census.get('options')),
        'totals': census['totals'],
        'areas': census['areas'],
        'revalidation': (revalidation(json.loads(base_raw), census)
                         if base_raw is not None else None),
        'orphans': orphans,
        'family_fields': FAMILY_FIELDS,
        'families': [family_row(f) for f in fams],
    }
    return render(out)


def render(out):
    """JSON with one family row per line, so diffs stay per family."""
    rows = out['families']
    body = json.dumps(dict(out, families='@ROWS@'), indent=1)
    lines = ',\n'.join('  ' + json.dumps(r) for r in rows)
    return body.replace('"@ROWS@"', '[\n' + lines + '\n ]') + '\n'


def consistent(pub):
    """Problems in a published file, checked without the census. It cannot see a coordinated
    rewrite of a whole entry (rows, totals and dependents together): that needs `--check`
    against the census bytes, or `--verify-pins` against Git."""
    try:
        return _consistent(pub)
    except (KeyError, TypeError, ValueError, AttributeError) as e:
        return [f'malformed classification: {type(e).__name__}: {e}']


def _consistent(pub):
    p = []
    fields = pub['family_fields']
    rows = [dict(zip(fields, r)) for r in pub['families']]
    names = [r['family'] for r in rows]
    if names != sorted(names) or len(set(names)) != len(names):
        p.append('families not sorted and unique')
    tv = {v: 0 for v in CL.VERDICTS}
    td = {v: 0 for v in CL.VERDICTS}
    for r in rows:
        counts = [r[v] for v in CL.VERDICTS]
        want = CL.family_verdict([v for v, n in zip(CL.VERDICTS, counts) for _ in range(n)])
        if r['verdict'] != want:
            p.append(f"{r['family']}: verdict {r['verdict']} but declaration counts give {want}")
        tv[r['verdict']] += 1
        for v in CL.VERDICTS:
            td[v] += r[v]
    t = pub['totals']
    if t['verdicts'] != tv or t['decl_verdicts'] != td or t['families'] != len(rows) \
            or t['lines'] != sum(r['lines'] for r in rows) \
            or t['decls'] != sum(r['decls'] for r in rows):
        p.append('totals disagree with the family rows')
    orphan_rows = {r['family']: r for r in rows if r['verdict'] == 'orphan'}
    if [o['family'] for o in pub['orphans']] != sorted(orphan_rows):
        p.append('orphans list differs from the orphan family rows')
    for o in pub['orphans']:
        r = orphan_rows.get(o['family'])
        if r and (r['lines'], r['decls']) != (o['lines'], o['decls']):
            p.append(f"{o['family']}: orphan entry disagrees with its row")
        if sum(m[2] for m in o['members']) != o['lines']:
            p.append(f"{o['family']}: member lines do not add up")
        d = o['dependents']
        if d['standalone'] != (not d['lean'] and not d['files']):
            p.append(f"{o['family']}: standalone flag disagrees with its dependents")
        if o['recovery'] != pub['recovery']['revision']:
            p.append(f"{o['family']}: recovery pin differs from the census revision")
    opts = pub['census']['options']
    if opts is not None and not isinstance(opts, dict):
        p.append('census options is not an object')
    if pub['authorization'].get('census_options') != opts:
        p.append('authorization does not state the census options it relies on')
    if pub['recovery']['revision'] != pub['census']['revision']:
        p.append('recovery pin is not the census revision')
    rv = pub.get('revalidation')
    if rv is not None and pub['baseline'] is not None and \
            rv['baseline_revision'] != pub['baseline']['revision']:
        p.append('revalidation names another baseline')
    return p


def verify_pins(repo, pub):
    """Problems with the recovery pin, from Git objects only: the pin resolves, its Lean tree is
    the census's, each orphan's members are exactly its family at the pin (grouping rule of
    sources.family_of) with their recorded line counts, and every Lean file outside the family
    whose header imports a member is listed among its Lean dependents."""
    import sources as S
    rev = pub['recovery']['revision']
    try:
        if S.resolve(repo, rev) != rev:
            return [f'recovery pin {rev} does not resolve to itself']
    except Exception as e:  # noqa: BLE001 - any Git failure means the pin cannot be read
        return [f'recovery pin {rev} cannot be read ({type(e).__name__}); fetch it']
    files = S.tracked(repo, rev)
    p = []
    if S.lean_tree_id(files) != pub['census']['lean_tree_id']:
        p.append('Lean tree at the recovery pin differs from the census')
    blob = dict(files)
    lean_paths = [x for x, _ in files if x.endswith('.lean')]
    in_scope = {x for x in lean_paths if S.area_of(x)}
    texts = S.blobs(repo, [blob[x] for x in lean_paths])
    importers = {}
    for x in lean_paths:
        for m in S.header_imports(texts[blob[x]]):
            importers.setdefault(m, set()).add(x)
    for o in pub['orphans']:
        listed = [m[0] for m in o['members']]
        actual = sorted(x for x in in_scope if S.family_of(x, in_scope)[0] == o['family'])
        if sorted(listed) != actual:
            p.append(f"{o['family']}: members differ from the family at the pin "
                     f"(missing {sorted(set(actual) - set(listed))}, "
                     f"extra {sorted(set(listed) - set(actual))})")
        for path, _, lines in o['members']:
            if path not in blob:
                p.append(f'{path}: absent at the recovery pin')
            elif S.line_count(texts[blob[path]]) != lines:
                p.append(f'{path}: {lines} lines recorded, not the pinned blob')
        dep = {row[0] for row in o['dependents']['lean']}
        for path in listed:
            for imp in sorted(importers.get(S.module_name(path), set()) - set(listed)):
                if imp not in dep and imp not in S.GENERATED_ROOTS:
                    p.append(f"{o['family']}: {imp} imports {path} but is not a listed dependent")
    return p


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--census', default='scripts/lean-inventory.json')
    ap.add_argument('--baseline')
    ap.add_argument('--baseline-label', help='how to recover the baseline bytes (default: its path)')
    ap.add_argument('--output', default=str(HERE / 'classification.json'))
    ap.add_argument('--check', action='store_true',
                    help='regenerate from the census files and fail on any difference')
    ap.add_argument('--consistent', action='store_true',
                    help='check the published file alone (no census needed)')
    ap.add_argument('--verify-pins', metavar='REPO',
                    help='with --consistent: also check the recovery pin from Git objects')
    a = ap.parse_args(argv)
    if a.verify_pins and not a.consistent:
        ap.error('--verify-pins requires --consistent')
    if a.consistent:
        pub = json.loads(Path(a.output).read_text())
        problems = consistent(pub) + (verify_pins(a.verify_pins, pub) if a.verify_pins else [])
        for q in problems:
            print('publish: inconsistent:', q)
        print('publish: consistent' if not problems else f'publish: {len(problems)} problem(s)')
        return 1 if problems else 0
    raw = Path(a.census).read_bytes()
    base = Path(a.baseline).read_bytes() if a.baseline else None
    text = publish(raw, a.census, base, a.baseline_label or a.baseline)
    problems = consistent(json.loads(text))
    if problems:
        for q in problems:
            print('publish: inconsistent:', q)
        return 1
    if len(text.encode()) > CAP_BYTES:
        print(f'publish: output {len(text.encode())} bytes is over the {CAP_BYTES}-byte cap')
        return 1
    if a.check:
        old = Path(a.output).read_text() if Path(a.output).exists() else None
        if old != text:
            print('publish: drift: regenerated classification differs from ' + a.output)
            return 1
        print('publish: check passed for census', sha256_bytes(raw))
        return 0
    Path(a.output).write_text(text)
    print('publish: wrote', a.output, len(text.encode()), 'bytes')
    return 0


if __name__ == '__main__':
    sys.exit(main())
