#!/usr/bin/env python3
"""Classify `#guard_msgs in #print axioms` pins (docstring form) and weigh them by churn.
Usage: pins.py GRAPH_JSON  (reads GRAPH_JSON.churn.json and .fp.churn.json from churn.py)"""
import re, json, sys, collections
g = json.load(open(sys.argv[1]))
R = json.load(open(sys.argv[1] + ".churn.json"))["rebuild"]
RF = json.load(open(sys.argv[1] + ".fp.churn.json"))["rebuild"]
pin = re.compile(r"/-- info: [^\n]*?(depends on axioms: \[(.*?)\]|does not depend on any axioms).*?-/\s*#guard_msgs(?:\s*\([^)]*\))?\s*in\s*#print axioms", re.S)
STD = {"propext", "Classical.choice", "Quot.sound"}
kinds, per, parsed = collections.Counter(), {}, 0
for m in g["lines"]:
    if not m.startswith("Solidity."): continue
    s = open(m.replace(".", "/") + ".lean", errors="replace").read()
    per[m] = s.count("#print axioms")
    for full, axs in pin.findall(s):
        parsed += 1
        ax = {a.strip() for a in axs.split(",")} if axs else set()
        kinds["none" if not ax else "std-all3" if ax == STD else "std-subset" if ax <= STD else "other"] += 1
leafctl = {m for m in per if m.split(".")[-1].endswith("Controls") and g["fanin"].get(m, 1) == 0}
print(f"#print axioms: {sum(per.values())} in {sum(1 for v in per.values() if v)} modules; parsed pins {parsed}: {dict(kinds)}")
for lab, RR in (("first-parent", RF), ("per-commit", R)):
    ev = sum(per[m] * RR.get(m, 0) for m in per); lc = sum(per[m] * RR.get(m, 0) for m in leafctl)
    print(f"{lab}: pin-rebuilds/wk {ev} (leaf controls {lc}); h/wk at 0.10 s {ev*0.10/3600:.1f}, at 0.34 s {ev*0.34/3600:.1f}")
