#!/usr/bin/env python3
"""Per-area .olean bytes, from each module's Lake trace (.lake/build/lib/lean/**.trace,
field outputs.o) resolved in Lake's artifact cache.  Run after a cached build.
Usage (repo root): python3 -I docs/audits/architecture-tools/olean_sizes.py CACHE_DIR"""
import os, sys, json, glob, collections, re
cache = sys.argv[1]
by, n, ctl = collections.Counter(), collections.Counter(), collections.Counter()
tot = 0
for tr in glob.glob(".lake/build/lib/lean/Solidity/**/*.trace", recursive=True):
    try: o = json.load(open(tr))["outputs"]["o"][0]
    except Exception: continue
    hits = glob.glob(os.path.join(cache, "artifacts", o + "*.olean"))
    if not hits: continue
    sz = os.path.getsize(hits[0])
    mod = tr[len(".lake/build/lib/lean/"):-6]
    area = mod.split("/")[1] if mod.count("/") else mod
    by[area] += sz; n[area] += 1; tot += sz
    if re.search(r"Controls$", mod): ctl["Controls"] += sz; ctl["n"] += 1
print(f"modules resolved: {sum(n.values())}; olean bytes: {tot/1e9:.2f} GB")
print(f"*Controls modules: {ctl['n']}, {ctl['Controls']/1e9:.2f} GB ({100*ctl['Controls']/tot:.0f}%)")
for a, s in by.most_common(14): print(f"  {a:16} {n[a]:5} modules {s/1e9:6.2f} GB")
