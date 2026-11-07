#!/usr/bin/env python3
"""Is `CORE` (scripts/check-layers.mjs) closed under imports, as
docs/parallelism.md P1 states?  Prints each core module's direct import that is
not core, the size of the transitive core closure, and the count of CORE
patterns.  Usage (repo root): python3 -I docs/audits/architecture-tools/core_closure.py
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from imports import G, PATH, SIZE  # noqa: E402

src = open("scripts/check-layers.mjs").read()
core_block = src[src.index("const CORE = ["): src.index("];", src.index("const CORE = ["))]
elab_block = src[src.index("const ELABORATOR = ["): src.index("];", src.index("const ELABORATOR = ["))]
pat = re.compile(r"^\s*/(.+)/,", re.M)
CORE = [re.compile(p) for p in pat.findall(core_block)]
ELAB = [re.compile(p) for p in pat.findall(elab_block)]


def is_core(m):
    return any(r.search(m) for r in CORE) and not any(r.search(m) for r in ELAB)


core = sorted(m for m in G if is_core(m))
print(f"CORE patterns: {len(CORE)}; modules matched: {len(core)}")
leaks = collections.Counter()
rows = []
for m in core:
    for i in G[m]:
        if i in G and not is_core(i):
            rows.append((m, i))
            leaks[i.split(".")[1] if i.count(".") else i] += 1
print(f"direct core -> non-core imports: {len(rows)}")
for a, n in leaks.most_common():
    print(f"  into {a}: {n}")
seen, st = set(), list(core)
while st:
    x = st.pop()
    if x in seen or x not in G:
        continue
    seen.add(x)
    st += G[x]
extra = sorted(seen - set(core))
print(f"transitive closure of core: {len(seen)} modules; {len(extra)} non-core, "
      f"{sum(SIZE[x] for x in extra)} lines")
by = collections.Counter(x.split(".")[1] for x in extra if x.count("."))
print("  non-core in closure by area:", dict(by.most_common()))
if "-v" in sys.argv:
    for a, b in rows:
        print(a, "->", b)
