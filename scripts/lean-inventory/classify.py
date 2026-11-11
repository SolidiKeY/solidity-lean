"""Certificate construction over extracted facts, following `Solidity.Goals.Inventory`.

The classifier only applies the contract's rules to recorded facts; it never decides
what counts as a use. Facts:

* `decls`: in-scope declaration identities, each with a module (`decl_module`).
* `module_info[m]`: `family`, `role` (member/controls/pins), `area`.
* `edges[x]`: recorded uses of `x` (declarations inside and outside the seven areas).
* `consumers[c]`: `kind` (goalProof/test/runner/cli/blanket/ownControls) and `roots`.
* `gaps`: dicts with `source` = ('use', None|x) or ('root', None|c), `targets` (a list of
  declarations, or None for any declaration) and `reason`.
"""
from collections import deque

PRIMARY = ('goalProof', 'test', 'runner', 'cli')
DEMANDING = PRIMARY + ('ownControls',)
VERDICTS = ('keep', 'ownerNeeded', 'orphan', 'unresolved')


def bfs(edges, seeds):
    """Reachable set with a parent map (node -> predecessor, None for seeds)."""
    parent = {}
    queue = deque()
    for s in seeds:
        if s not in parent:
            parent[s] = None
            queue.append(s)
    while queue:
        x = queue.popleft()
        for y in sorted(edges.get(x, ())):
            if y not in parent:
                parent[y] = x
                queue.append(y)
    return parent


def path_to(parent, d):
    """`(seed, path)` with `Chain edge seed path d` (path excludes the seed)."""
    out = [d]
    while parent[out[-1]] is not None:
        out.append(parent[out[-1]])
    out.reverse()
    return out[0], out[1:]


def gap_live_always(gap):
    """Whether a gap's source is live for every closed set (unknown source)."""
    return gap['source'][1] is None


class Facts:
    def __init__(self, decls, decl_module, module_info, edges, consumers, gaps):
        self.decls = decls
        self.decl_module = decl_module
        self.module_info = module_info
        self.edges = edges
        self.consumers = consumers
        self.gaps = gaps

    def family(self, d):
        return self.module_info[self.decl_module[d]]['family']

    def role(self, d):
        return self.module_info[self.decl_module[d]]['role']


def closed_set(facts, kinds, extra_seeds=()):
    """Least set holding the roots of consumers whose kind is in `kinds`, `extra_seeds`,
    and closed under recorded edges and live gaps. Returns (set or None, parent map).
    None when an untargeted live gap blocks every absence conclusion."""
    seeds = set(extra_seeds)
    for c in sorted(facts.consumers):
        info = facts.consumers[c]
        if info['kind'] in kinds:
            seeds.update(info['roots'])
    parent = bfs(facts.edges, sorted(seeds))
    while True:
        added = []
        for g in facts.gaps:
            kind, src = g['source']
            if kind == 'use':
                live = src is None or src in parent
            else:
                live = src is None or facts.consumers[src]['kind'] in kinds
            if not live:
                continue
            if g['targets'] is None:
                return None, parent
            added.extend(t for t in g['targets'] if t not in parent)
        if not added:
            return set(parent), parent
        more = bfs(facts.edges, sorted(set(added)))
        for k, v in more.items():
            parent.setdefault(k, v)


def classify(facts):
    """Per-declaration rows and per-family verdicts."""
    keep_parent = {}
    keep_root = {}
    for c in sorted(facts.consumers):
        info = facts.consumers[c]
        if info['kind'] not in PRIMARY:
            continue
        for r in sorted(info['roots']):
            if r in keep_parent:
                continue
            for k, v in bfs(facts.edges, [r]).items():
                if k not in keep_parent:
                    keep_parent[k] = v
                    keep_root[k] = (c, r)
    indep, _ = closed_set(facts, PRIMARY)
    seeds = sorted(d for d in facts.decls if facts.role(d) != 'member')
    for c in sorted(facts.consumers):
        if facts.consumers[c]['kind'] == 'ownControls':
            seeds.extend(r for r in facts.consumers[c]['roots']
                         if r in facts.decl_module)
    demand_parent = bfs(facts.edges, sorted(set(seeds)))
    demand, _ = closed_set(facts, DEMANDING, seeds)
    # Gap reach for unresolved witnesses: from each live gap target along possible steps.
    gap_parent, gap_of = {}, {}
    for i, g in enumerate(facts.gaps):
        if g['targets'] is None:
            continue
        for t in g['targets']:
            if t not in gap_parent:
                gap_parent[t] = None
                gap_of[t] = i
    gp = bfs(facts.edges, sorted(gap_parent))
    for k, v in gp.items():
        gap_parent.setdefault(k, v)
    untargeted = [i for i, g in enumerate(facts.gaps) if g['targets'] is None]
    rows = {}
    for d in sorted(facts.decls):
        if d in keep_parent:
            root, path = path_to(keep_parent, d)
            rows[d] = {'verdict': 'keep', 'consumer': keep_root[d][0], 'root': root, 'path': path}
        elif indep is not None and d not in indep and d in demand_parent:
            seed, path = path_to(demand_parent, d)
            rows[d] = {'verdict': 'ownerNeeded', 'owner': facts.family(seed), 'seed': seed,
                       'path': path, 'indep': 'S_primary'}
        elif demand is not None and d not in demand:
            rows[d] = {'verdict': 'orphan', 'live': 'S_demand'}
        else:
            if d in gap_parent:
                start, path = path_to(gap_parent, d)
                rows[d] = {'verdict': 'unresolved', 'gap': gap_of[start], 'target': start,
                           'path': path, 'recorded': 'S_keep'}
            elif untargeted:
                rows[d] = {'verdict': 'unresolved', 'gap': untargeted[0], 'target': None,
                           'path': [], 'recorded': 'S_keep'}
            else:
                raise AssertionError('no verdict for ' + d)
    families = {}
    for d, row in rows.items():
        families.setdefault(facts.family(d), []).append(row['verdict'])
    return rows, families, {'S_keep': set(keep_parent), 'S_primary': indep, 'S_demand': demand}


def family_verdict(verdicts):
    """`Census.FamilyOk`: keep, else unresolved (also when empty), else owner-needed, else orphan."""
    if 'keep' in verdicts:
        return 'keep'
    if not verdicts or 'unresolved' in verdicts:
        return 'unresolved'
    if 'ownerNeeded' in verdicts:
        return 'ownerNeeded'
    return 'orphan'
