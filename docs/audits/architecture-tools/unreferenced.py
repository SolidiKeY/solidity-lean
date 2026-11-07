#!/usr/bin/env python3
"""Declarations whose name is never mentioned anywhere else.

A declaration's last name component (`foo` of `A.B.foo`) is counted as a
token in every .lean file of Solidity/, Bridge/ and the top-level roots, and in
docs/ and scripts/ (a printer or a pin may name it).  A declaration whose last
component occurs exactly once in all of them (its own declaration) is
"unreferenced".  Upper bound on dead code: `simp` sets via attributes, `@[simp]`
lemmas used implicitly, instances, `#guard`-style checks and controls whose
point is to elaborate are not dead; the table splits by kind and file role.

Usage (repo root): python3 -I docs/audits/architecture-tools/unreferenced.py
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dup_decls import DECL  # noqa: E402

TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
count = collections.Counter()
decls = []
for top in ["Solidity", "Bridge", "docs", "scripts", "site", "web", "tests"]:
    for dp, dns, fs in os.walk(top):
        dns[:] = [d for d in dns if d not in (".lake", "node_modules", "vendor")]
        for f in fs:
            if not f.endswith((".lean", ".md", ".mjs", ".py", ".sh", ".json", ".js")):
                continue
            p = os.path.join(dp, f)
            try:
                t = open(p, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            if f.endswith(".json") and len(t) > 5_000_000:
                continue
            # count components: `A.B.foo` contributes A, B, foo
            count.update(TOK.findall(t))
            if top == "Solidity" and f.endswith(".lean"):
                for m in DECL.finditer(t + "\nEND"):
                    mods = m.group("mods")
                    if "instance" in mods:
                        continue
                    attrs = re.findall(r"@\[([^\]]*)\]", mods)
                    decls.append((p, m.group("name").split(".")[-1], m.group("kw"),
                                  any(re.search(r"\bsimp\b|\bext\b|grind|reducible|implemented_by|csimp|macro|elab", a) for a in attrs)))
for f in [x for x in os.listdir(".") if x.endswith(".lean")]:
    count.update(TOK.findall(open(f).read()))


def role(p):
    b = os.path.basename(p)
    if re.search(r"(Controls|Examples|Checks?|Pins|Coverage)\.lean$", b) or "/Checks/" in p or "/Examples/" in p:
        return "control/example"
    return "library"


tab = collections.Counter()
lines = collections.Counter()
area_dead = collections.Counter()
for p, n, kw, attr in decls:
    dead = count[n] <= 1 and not attr
    tab[(role(p), kw, dead)] += 1
    if dead and role(p) == "library":
        area_dead[p.split("/")[1]] += 1
print(f"declarations: {len(decls)}")
for r in ("library", "control/example"):
    for kw in ("theorem", "lemma", "def", "abbrev"):
        tot = tab[(r, kw, True)] + tab[(r, kw, False)]
        if tot:
            print(f"  {r:16} {kw:8} {tot:6} unreferenced {tab[(r, kw, True)]:6} ({100*tab[(r, kw, True)]/tot:.0f}%)")
print("unreferenced library declarations by area:", dict(area_dead.most_common()))
if "-v" in sys.argv:
    for p, n, kw, attr in decls:
        if count[n] <= 1 and not attr and role(p) == "library":
            print(p, kw, n)
