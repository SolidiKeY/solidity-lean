#!/usr/bin/env python3
"""Census of theorem declarations: per top-level area, how many are
closed (no binder before the first top-level ':'), ground (closed and
no ∀/∃/→/↔/fun in the conclusion: a fact about fixed values), and how many have a
`True` conclusion.  Heuristic, source-level; run from the repository root:
  python3 -I docs/audits/proof-coverage-tools/theorem_census.py"""
import os, re, collections, sys
root = '.'
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|example)\b\s*([^\s:({\[⦃]*)')
ground = collections.Counter(); stats = collections.Counter(); closed = collections.Counter(); true_c = collections.Counter()
for dp, dn, fn in os.walk(root):
    if any(p in dp for p in ('.lake', 'vendor', 'node_modules', '/.git')): continue
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f)
        parts = p[2:].split('/')
        area = '/'.join(parts[:2]) if parts[0] in ('Solidity', 'Bridge') and len(parts) > 2 else parts[0]
        try: lines = open(p, encoding='utf-8').read().split('\n')
        except Exception: continue
        for i, l in enumerate(lines):
            m = decl.match(l)
            if not m: continue
            # gather the header up to ':=' or 'where' (max 30 lines)
            hdr = ' '.join(lines[i:i+30]); hdr = hdr.split(':=')[0]
            body = hdr[m.end():]
            # strip leading name already consumed; first top-level ':' at depth 0
            depth = 0; j = None
            for k, ch in enumerate(body):
                if ch in '([{⦃': depth += 1
                elif ch in ')]}⦄': depth -= 1
                elif ch == ':' and depth == 0: j = k; break
            if j is None: continue
            binders = body[:j].strip()
            concl = body[j+1:].strip()
            stats[area] += 1
            if binders == '': closed[area] += 1
            if binders == '' and not re.search(r'[∀∃→↔]|\bfun\b|\bforall\b', concl): ground[area] += 1
            if re.fullmatch(r'True', concl.strip()): true_c[area] += 1
tot = sum(stats.values())
print(f'total {tot} closed {sum(closed.values())} ground {sum(ground.values())} trueConcl {sum(true_c.values())}')
for a, n in stats.most_common(40):
    print(f'{a:40s} {n:7d} closed {closed[a]:6d} ({100*closed[a]//n:3d}%) ground {ground[a]:6d} ({100*ground[a]//n:3d}%) True {true_c[a]}')
