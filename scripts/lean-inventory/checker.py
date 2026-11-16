"""Independent checker of scripts/lean-inventory.json.

It shares only Git plumbing and lexical parsing with `sources.py`; it does not import
`classify.py` or `inventory.build`. From the revision's Git objects and the extraction
cache it recomputes coverage, grouping, roles, line counts, recovery pins, consumer
roots, gap targets, the three closed sets, every declaration's verdict, the family
verdicts (Census.FamilyOk) and the timing records, then checks each family witness
against the raw edges. It returns a list of problems (empty when the inventory holds).
"""
import gzip
import hashlib
import json
from pathlib import Path
import re

import sources as S

PRIMARY = {'goalProof', 'test', 'runner', 'cli'}


def _sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def _digest(items):
    h = hashlib.sha256()
    for x in sorted(items):
        h.update((x + '\n').encode())
    return h.hexdigest()


def _grow(edges, start):
    """Fixpoint of `start` under `edges` (set iteration, no parent tracking)."""
    out = set(start)
    frontier = set(start)
    while frontier:
        nxt = set()
        for x in frontier:
            nxt |= edges.get(x, set())
        frontier = nxt - out
        out |= frontier
    return out


def _group(path, in_scope):
    """The grouping rule, written independently of `sources.family_of`."""
    directory, file = path.rsplit('/', 1)
    stem = file[:-5]
    if stem in ('Controls', 'Pins'):
        return 'dir:%s/' % directory, stem.lower()
    for suf in ('Controls', 'Pins'):
        if stem.endswith(suf) and stem != suf:
            return 'triple:%s/%s' % (directory, stem[:-len(suf)]), suf.lower()
    if any('%s/%s%s.lean' % (directory, stem, suf) in in_scope for suf in ('Controls', 'Pins')):
        return 'triple:%s/%s' % (directory, stem), 'member'
    return 'dir:%s/' % directory, 'member'


def check(repo, inv):
    problems = []

    def bad(msg):
        problems.append(msg)

    if inv.get('schema') != 'solidity-lean/lean-inventory' or inv.get('version') != 1:
        return ['unknown schema or version']
    rev = inv.get('revision', '')
    if not re.fullmatch(r'[0-9a-f]{40}', rev):
        return ['revision is not a full commit id']
    try:
        if S.resolve(repo, rev) != rev:
            return ['revision does not resolve to itself']
    except Exception:
        return ['revision unknown to the repository']
    files = S.tracked(repo, rev)
    blob = dict(files)
    if S.lean_tree_id(files) != inv.get('lean_tree_id'):
        bad('lean_tree_id differs from the revision')
    texts = S.blobs(repo, [b for p, b in files if p.endswith('.lean')] + [blob['lean-toolchain']])
    if texts[blob['lean-toolchain']].strip() != inv.get('toolchain'):
        bad('toolchain differs from lean-toolchain at the revision')

    # Extraction identity.
    cdir = Path(repo) / '.lake/lean-inventory' / rev
    try:
        ident = json.loads((cdir / 'identity.json').read_text())
    except OSError:
        return problems + ['extraction cache absent for the revision']
    for k, v in inv.get('extraction', {}).items():
        if ident.get(k) != v:
            bad('extraction field %s differs from the cache identity' % k)
    for name, key in (('graph.jsonl.gz', 'graph_sha256'), ('anon.json', 'anon_sha256'),
                      ('build.log', 'build_log_sha256'), ('xrefs.json', 'xrefs_sha256')):
        if not (cdir / name).exists() or _sha(cdir / name) != ident.get(key):
            bad('cache file %s altered' % name)
    if ident.get('revision') != rev or ident.get('lean_tree_id') != S.lean_tree_id(files):
        bad('cache identity is for other sources')
    if problems:
        return problems

    # Coverage, grouping, roles, lines, pins.
    lean_paths = sorted(p for p, _ in files if p.endswith('.lean'))
    in_scope = {p for p in lean_paths
                if p.startswith('Solidity/') and p.count('/') >= 2 and p.split('/')[1] in S.AREAS}
    seen = {}
    fam_of_path = {}
    for f in inv['families']:
        areas = set()
        for path, role, lines, *_ in f['members']:
            if path in seen:
                bad('module %s listed twice' % path)
            seen[path] = f['family']
            if path not in in_scope:
                bad('listed module %s is not an in-scope tracked module' % path)
                continue
            g, r = _group(path, in_scope)
            if g != f['family'] or r != role:
                bad('module %s grouped as %s/%s, expected %s/%s' % (path, f['family'], role, g, r))
            if S.line_count(texts[blob[path]]) != lines:
                bad('line count of %s' % path)
            areas.add(path.split('/')[1])
            fam_of_path[path] = f['family']
        if areas != {f['area']}:
            bad('family %s spans areas %s' % (f['family'], sorted(areas)))
        if f['lines'] != sum(m[2] for m in f['members']):
            bad('family %s line total' % f['family'])
    missing = in_scope - set(seen)
    if missing:
        bad('%d tracked in-scope modules missing, e.g. %s' % (len(missing), sorted(missing)[0]))
    rec = inv.get('recovery', {})
    if rec.get('revision') != rev:
        bad('recovery revision differs')

    # Raw graph.
    mod_of_path = {p: S.module_name(p) for p in lean_paths}
    path_of_mod = {m: p for p, m in mod_of_path.items()}
    scope_mods = {mod_of_path[p] for p in in_scope}
    consts, goals, exe, loaded = {}, [], {}, set()
    with gzip.open(cdir / 'graph.jsonl.gz', 'rt') as fh:
        for line in fh:
            r = json.loads(line)
            if r['r'] == 'module' and r['g'] == 'lib':
                loaded.add(r['m'])
            if r['r'] == 'const':
                if r['g'] == 'lib':
                    c = consts.setdefault(r['n'], {'m': r['m'], 'uses': set(), 'flags': set()})
                    c['uses'] |= set(r['refs']) | set(r.get('lits', [])) | (
                        {r['impl']} if 'impl' in r else set())
                    c['flags'] |= {k for k in ('inst', 'simp', 'meta') if r.get(k)}
                    if 'range' in r:
                        c['range'], c['m'], c['k'] = r['range'], r['m'], r['k']
                elif r['g'].startswith('exe:'):
                    exe.setdefault(r['g'], {})[r['n']] = r
            elif r['r'] == 'goal' and r['g'] == 'lib':
                goals.append(r)
    ranged = {n for n, c in consts.items() if 'range' in c}

    def fold(n):
        p = n
        if p in ranged:
            return p
        while '.' in p:
            p = p.rsplit('.', 1)[0]
            if p in ranged:
                return p
        return n

    owner = {}
    for n, c in consts.items():
        f = fold(n)
        owner.setdefault(f, consts[f]['m'] if f in consts else c['m'])
    edges = {}
    for n, c in consts.items():
        a = fold(n)
        for t in c['uses']:
            if t in consts and fold(t) != a:
                edges.setdefault(a, set()).add(fold(t))

    # Anonymous references.
    anon = json.loads((cdir / 'anon.json').read_text())
    imports = {mod_of_path[p]: S.header_imports(texts[blob[p]]) for p in lean_paths}
    test_mods = S.closure(imports, list(S.TEST_ROOTS)) - S.closure(imports, ['Solidity'])
    decl_mod = {d: m for d, m in owner.items() if m in scope_mods}
    roots = {}
    kinds = {}
    unclassified = set()
    for m, uses in anon.items():
        if m not in path_of_mod:
            continue
        starts = S.command_starts(texts[blob[path_of_mod[m]]])
        for line, name in uses:
            if name not in consts:
                continue
            t = fold(name)
            st = max((s for s in starts if s <= line), default=None)
            cls = S.classify_command(starts[st]) if st else 'unclassified'
            if cls == 'declaration-or-scope':
                continue
            if cls == 'unclassified':
                unclassified.add(t)
            elif m in scope_mods:
                d = '%s@%d' % (m, st)
                decl_mod[d] = m
                if d != t:
                    edges.setdefault(d, set()).add(t)
            else:
                cid = ('test:' if m in test_mods else 'check:') + path_of_mod[m]
                roots.setdefault(cid, set()).add(t)
                kinds[cid] = 'test'
    for n, c in consts.items():
        if fold(n) == n and c['m'] in test_mods and c.get('k') == 'theorem' and 'range' in c:
            cid = 'test:' + path_of_mod[c['m']]
            roots.setdefault(cid, set()).add(n)
            kinds[cid] = 'test'
    for g in goals:
        if g['proof'] in consts:
            roots['goal:' + g['decl']] = {fold(g['proof'])}
            kinds['goal:' + g['decl']] = 'goalProof'
    for g, cs in exe.items():
        root_mod = {'exe:' + e: m for m, e in S.EXE_ROOTS.items()}[g]
        local = {n: set(r['refs']) | set(r.get('lits', [])) for n, r in cs.items() if r['m'] == root_mod}
        reach = _grow({n: v & set(local) for n, v in local.items()}, {'main'} & set(local))
        roots[g] = {fold(t) for n in reach for t in local[n] if t in consts}
        kinds[g] = 'cli' if g in ('exe:solkeycheck', 'exe:solidity-lean') else 'runner'
    listed = {c['id']: c for c in inv['roots']['consumers']}
    if set(listed) != set(roots):
        bad('consumer roster differs: %d listed, %d recomputed' % (len(listed), len(roots)))
    for cid, rs in roots.items():
        c = listed.get(cid)
        if c and (c['kind'] != kinds[cid] or c['roots'] != len(rs) or
                  c['in_scope_roots'] != len([r for r in rs if r in decl_mod])):
            bad('consumer %s kind or roots differ' % cid)

    # Gap targets.
    nodes = set(owner)
    meta = {fold(n) for n, c in consts.items() if 'meta' in c['flags']}
    implicit = {fold(n) for n, c in consts.items() if c['flags'] & {'inst', 'simp'}}
    attributed = set()
    heads = {}
    for n in nodes:
        c = consts.get(n)
        if not c or 'range' not in c or owner[n] not in path_of_mod:
            continue
        m = owner[n]
        if m not in heads:
            heads[m] = S.attributed_heads(texts[blob[path_of_mod[m]]])
        if any(c['range'][0] <= h <= c['range'][1] for h in heads[m]):
            attributed.add(n)
    tokens = set()
    for p in lean_paths:
        tokens |= S.attribute_commands(texts[blob[p]])
    last_tokens = {}
    for t in tokens:
        last_tokens.setdefault(t.rsplit('.', 1)[-1], set()).add(t)
    for n in nodes:
        for t in last_tokens.get(n.rsplit('.', 1)[-1], ()):
            if n == t or n.endswith('.' + t):
                attributed.add(n)
    built = S.closure(imports, list(S.LIB_ROOTS) + list(S.EXE_ROOTS))
    blanket = {b['path'] for b in inv['roots']['blanket']}
    reached = set()
    for p in lean_paths:
        m = mod_of_path[p]
        if m in built or p in in_scope or p in blanket:
            continue
        cl = S.closure(imports, imports.get(m, []))
        if cl & scope_mods:
            reached |= cl
    runner = set()
    scripts = [(p, b) for p, b in files if not p.endswith('.lean') and not p.startswith('docs/')
               and p.endswith(('.py', '.mjs', '.js', '.cjs', '.sh', '.ts'))]
    stexts = S.blobs(repo, [b for _, b in scripts])
    mods = set(mod_of_path.values())
    for p, b in scripts:
        if not S.LEAN_INVOCATION.search(stexts[b]):
            continue
        named = set()
        for nm in S.template_imports(stexts[b]):
            named |= ({m for m in mods if m.startswith(nm[:-1] + '.')} if nm.endswith('*')
                      else ({nm} & mods))
        runner |= S.closure(imports, sorted(named))
    targets = (meta | (implicit | attributed) | set(unclassified) |
               {n for n in nodes if owner[n] in reached or owner[n] in runner}) & nodes
    gap_counts = {
        'elaborator-time': len(meta & nodes), 'elaborator-time-anonymous': len(meta & nodes),
        'implicit-use': len((implicit | attributed) - meta & nodes),
        'implicit-use-anonymous': len((implicit | attributed) - meta & nodes),
        'unclassified-command': len(unclassified & nodes),
        'unextracted-lean-file': len({n for n in nodes if owner[n] in reached}),
        'runner-template': len({n for n in nodes if owner[n] in runner})}
    claimed = {g['class']: g['targets'] for g in inv['gaps'] if g['targets'] is not None}
    for k, v in gap_counts.items():
        if claimed.get(k, 0) != v:
            bad('gap class %s targets %s, recomputed %d' % (k, claimed.get(k), v))
    untargeted = any(g['targets'] is None for g in inv['gaps'])
    unloaded = (set(scope_mods) - loaded) | set(ident.get('missing_compiled', [])) & scope_mods
    if bool(unloaded) and not untargeted:
        bad('modules without compiled metadata but no untargeted gap')

    # Closed sets and verdicts.
    prim_roots = set().union(*[rs for c, rs in roots.items() if kinds[c] in PRIMARY]) \
        if roots else set()
    s_keep = _grow(edges, prim_roots)
    s_primary = None if untargeted else _grow(edges, prim_roots | targets)
    seeds = {d for d, m in decl_mod.items() if _group(path_of_mod[m], in_scope)[1] != 'member'}
    s_dem_reach = _grow(edges, seeds)
    s_demand = None if untargeted else _grow(edges, prim_roots | seeds | targets)
    for name, s in (('S_keep', s_keep), ('S_primary', s_primary), ('S_demand', s_demand)):
        want = inv['sets'].get(name)
        got = None if s is None else {'size': len(s), 'sha256': _digest(s)}
        if want != got:
            bad('closed set %s differs' % name)

    def verdict(d):
        if d in s_keep:
            return 'keep'
        if s_primary is not None and d not in s_primary and d in s_dem_reach:
            return 'ownerNeeded'
        if s_demand is not None and d not in s_demand:
            return 'orphan'
        return 'unresolved'

    fam_decls = {}
    for d, m in decl_mod.items():
        fam_decls.setdefault(_group(path_of_mod[m], in_scope)[0], []).append(d)

    def chain(a, path, b):
        x = a
        for y in path:
            if y not in edges.get(x, ()):
                return False
            x = y
        return x == b

    orphans = []
    for f in inv['families']:
        ds = fam_decls.get(f['family'], [])
        vs = [verdict(d) for d in ds]
        counts = {v: vs.count(v) for v in ('keep', 'ownerNeeded', 'orphan', 'unresolved')}
        if counts != f['counts']:
            bad('family %s verdict counts differ' % f['family'])
        if 'keep' in vs:
            fv = 'keep'
        elif not vs or 'unresolved' in vs:
            fv = 'unresolved'
        elif 'ownerNeeded' in vs:
            fv = 'ownerNeeded'
        else:
            fv = 'orphan'
        if fv != f['verdict']:
            bad('family %s verdict %s, recomputed %s' % (f['family'], f['verdict'], fv))
        if fv == 'orphan':
            orphans.append(f['family'])
        if f['decls'] != sum(1 for d in ds if '@' not in d) or \
                f['pseudo'] != sum(1 for d in ds if '@' in d):
            bad('family %s declaration denominators' % f['family'])
        w = f['witness'] or {}
        if f['verdict'] == 'keep':
            d = w.get('decl')
            if d not in ds or w.get('consumer') not in roots or \
                    kinds.get(w.get('consumer')) not in PRIMARY or \
                    w.get('root') not in roots[w['consumer']] or \
                    not chain(w.get('root'), w.get('path', []), d):
                bad('family %s keep witness does not check' % f['family'])
            elif w.get('kind') != kinds[w['consumer']]:
                bad('family %s keep witness kind' % f['family'])
        elif f['verdict'] == 'ownerNeeded':
            d, s = w.get('decl'), w.get('seed')
            if d not in ds or s not in seeds or \
                    _group(path_of_mod[decl_mod[s]], in_scope)[0] != w.get('owner') or \
                    not chain(s, w.get('path', []), d) or (s_primary is None or d in s_primary) or \
                    w.get('cross_family') != (w.get('owner') != f['family']):
                bad('family %s owner-needed witness does not check' % f['family'])
        elif f['verdict'] == 'unresolved' and ds:
            d, t = w.get('decl'), w.get('target')
            if d not in ds or d in s_keep or w.get('gap_class') not in claimed and not untargeted \
                    or (t is not None and (t not in targets or not chain(t, w.get('path', []), d))):
                bad('family %s unresolved witness does not check' % f['family'])
    if sorted(orphans) != sorted(inv.get('certified_orphan_families', [])):
        bad('certified orphan list differs')

    # Dependents of orphan families: importers, .ilean name mentions, kernel edges, and
    # non-Lean files outside docs/ naming a member path or module.
    xrefs = json.loads((cdir / 'xrefs.json').read_text())
    orphan_fams = [f for f in inv['families'] if f['verdict'] == 'orphan']
    if orphan_fams:
        excl = ('docs/', 'scripts/lean-inventory/', 'scripts/lean-inventory.json')
        other = [(p, b) for p, b in files if not p.endswith('.lean') and not p.startswith(excl)]
        otexts = S.blobs(repo, sorted({b for _, b in other}))
    for f in orphan_fams:
        ms = {mod_of_path[path] for path, *_ in f['members']}
        own_nodes = {n for n, m in owner.items() if m in ms}
        named = {n for n in consts if fold(n) in own_nodes}
        kern_of = {}
        for x, ys in edges.items():
            if ys & own_nodes and x in owner:
                kern_of[owner[x]] = kern_of.get(owner[x], 0) + 1
        rows = []
        for p in lean_paths:
            m = mod_of_path[p]
            if m in ms or p in S.GENERATED_ROOTS:
                continue
            imp = any(i in ms for i in imports.get(m, []))
            refs = len(named.intersection(xrefs.get(m, [])))
            kern = kern_of.get(m, 0)
            if imp or refs or kern:
                rows.append([p, imp, refs, kern])
        needles = [path_of_mod[m] for m in ms] + list(ms)
        hits = sorted(p for p, b in other if any(n in otexts[b] for n in needles))
        want = {'lean': sorted(rows), 'files': hits, 'standalone': not rows and not hits}
        if f.get('dependents') != want:
            bad('family %s dependents differ' % f['family'])

    # Timing records.
    log = (cdir / 'build.log').read_text()
    built_ms = {}
    for m in re.finditer(r'Built (\S+) \((\d+(?:\.\d+)?)(ms|s)\)', log):
        v = float(m.group(2))
        built_ms[m.group(1)] = int(round(v if m.group(3) == 'ms' else v * 1000))
    prov = inv['timing']['provenance']
    if any(not prov.get(k) for k in ('source', 'toolchain', 'command', 'context', 'outcome')):
        bad('timing provenance incomplete')
    if not inv['timing'].get('unavailable_reason'):
        bad('unavailable timing reason empty')
    for f in inv['families']:
        for path, _, _, _, _, ms in f['members']:
            if built_ms.get(mod_of_path[path]) != ms:
                bad('timing of %s differs from the build log' % path)
    if not inv.get('line_basis') or not inv.get('limitations'):
        bad('line basis or limitations missing')
    return problems
