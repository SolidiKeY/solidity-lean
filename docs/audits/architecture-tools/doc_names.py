#!/usr/bin/env python3
"""Backticked dotted Lean names in docs/*.md (top level, not generated maps)
whose last component occurs in no .lean file.  Usage: python3 -I .../doc_names.py [-v]"""
import os, re, sys, collections
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
lean = collections.Counter()
for top in ["Solidity", "Bridge", "."]:
    for dp, dns, fs in os.walk(top):
        if top == "." and dp != ".": continue
        dns[:] = [d for d in dns if d not in (".lake", "node_modules")]
        for f in fs:
            if f.endswith(".lean"):
                lean.update(TOK.findall(open(os.path.join(dp, f), errors="replace").read()))
NAME = re.compile(r"`([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+)`")
miss, tot = collections.defaultdict(list), 0
for f in sorted(os.listdir("docs")):
    if not f.endswith(".md"): continue
    t = open(os.path.join("docs", f), errors="replace").read()
    for n in set(NAME.findall(t)):
        if n.endswith((".lean", ".md", ".json", ".mjs", ".py", ".sh", ".sol", ".toml")): continue
        tot += 1
        last = n.split(".")[-1]
        if lean[last] == 0: miss[f].append(n)
print(f"dotted names cited in docs/*.md: {tot}; last component in no .lean file: {sum(map(len, miss.values()))}")
for f, ns in sorted(miss.items(), key=lambda x: -len(x[1]))[:15]:
    print(f"  {len(ns):4} {f}: {', '.join(sorted(ns)[:5])}")
