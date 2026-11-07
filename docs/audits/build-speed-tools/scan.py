#!/usr/bin/env python3
"""Count cost-relevant constructs per module (static; no Lean).
Usage: scan.py GRAPH_JSON [MODULE...]  -> TSV per module, then area totals."""
import json, re, sys, collections
g = json.load(open(sys.argv[1]))
pats = {
  "decide": r"\bdecide\b", "native_decide": r"\bnative_decide\b", "guard": r"#guard\b",
  "guard_msgs": r"#guard_msgs\b", "eval": r"#eval\b", "simp": r"\bsimp\b", "simp_all": r"\bsimp_all\b",
  "rfl": r"\brfl\b", "omega": r"\bomega\b", "theorem": r"^\s*(?:private\s+|protected\s+)?(?:theorem|lemma|example)\b",
  "def": r"^\s*(?:private\s+|protected\s+|@\[[^\]]*\]\s*)*(?:def|abbrev|instance)\b",
  "maxHeartbeats": r"maxHeartbeats", "maxRecDepth": r"maxRecDepth", "print_axioms": r"#print axioms",
}
rx = {k: re.compile(v, re.M) for k, v in pats.items()}
mods = sys.argv[2:] or [m for m in g["lines"] if m.startswith("Solidity.")]
def path(m): return m.replace(".", "/") + ".lean"
rows = {}
for m in mods:
    try: s = open(path(m), encoding="utf-8", errors="replace").read()
    except FileNotFoundError: continue
    rows[m] = {k: len(r.findall(s)) for k, r in rx.items()}
keys = list(pats)
print("module\tlines\t" + "\t".join(keys))
for m in (sys.argv[2:] and mods or []):
    if m in rows: print(m + "\t" + str(g["lines"][m]) + "\t" + "\t".join(str(rows[m][k]) for k in keys))
tot = collections.defaultdict(collections.Counter)
for m, r in rows.items():
    a = ".".join(m.split(".")[:2]); tot[a].update(r); tot[a]["lines"] += g["lines"][m]
    if m.split(".")[-1].endswith("Controls"): tot["*Controls"].update(r); tot["*Controls"]["lines"] += g["lines"][m]
    tot["ALL"].update(r); tot["ALL"]["lines"] += g["lines"][m]
print("\narea\tlines\t" + "\t".join(keys))
for a, c in sorted(tot.items(), key=lambda x: -x[1]["lines"])[:16]:
    print(a + "\t" + str(c["lines"]) + "\t" + "\t".join(str(c[k]) for k in keys))
