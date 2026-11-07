#!/usr/bin/env python3
"""Duplicate *general* lemmas: theorem groups (dup_decls.py) whose statement
opens with a binder, excluding files named *Controls/*Examples (where equal
text usually reads different local constants).  Prints the file pairs that
share the most such lemmas.  Usage: python3 -I .../dup_general.py"""
import os, sys, re, hashlib, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dup_decls import scan
ds = [d for d in scan() if d[3] in ("theorem", "lemma") and d[4][:1] in "{(⦃["
      and not re.search(r"(Controls|Examples|Checks?)\.lean$", d[0]) and "/Checks/" not in d[0]]
g = collections.defaultdict(list)
for d in ds: g[hashlib.sha1(d[4].encode()).hexdigest()].append(d)
multi = [v for v in g.values() if len({x[0] for x in v}) > 1]
print(f"general theorems: {len(ds)}; duplicated groups: {len(multi)}; redundant copies: {sum(len(v)-1 for v in multi)}; private among copies: {sum(1 for v in multi for x in v if x[2])}")
pairs = collections.Counter()
for v in multi:
    fs = sorted({x[0] for x in v})
    for i in range(len(fs)):
        for j in range(i+1, len(fs)): pairs[(fs[i], fs[j])] += 1
print("file pairs sharing most duplicated general lemmas:")
for (a, b), n in pairs.most_common(25): print(f"  {n}\t{a}\t{b}")
fam = collections.Counter()
for v in multi: fam[os.path.dirname(v[0][0])] += len(v)-1
print("redundant copies by directory:")
for k, n in fam.most_common(12): print(f"  {n}\t{k}")
