#!/usr/bin/env python3
"""controls-classify.py [--list reachable|unreachable|edges] [--check]

Classifies every `*Controls` module of the `Solidity` library (the modules
`register.sh` puts in `Solidity.lean` or `SolidityControls`) as
LIBRARY-REACHABLE or UNREACHABLE (t2-controls-off-path, step 1).

A Controls module is reachable when a library module that is neither a
Controls module nor check-like imports it, directly or transitively (through
any chain of modules). Check-like means the module name's last component ends
in `Controls`, `Checks`, `Check`, `Tests` or `Test`. Only unreachable Controls
may leave the `Solidity` root: Lake builds a reachable one anyway.

The default output is the counts. `--list` prints one class, or the direct
non-Controls library importers of each Controls module (`edges`). `--check` is
the scope-complete acceptance check: every `*Controls` module of the tree is
classified exactly once, the classes are disjoint, and no unreachable module
is imported (transitively) by any library module outside the unreachable set
and the check-like modules. Exit 0 = ok, 1 = a check failed, 2 = error.
"""
import pathlib, re, subprocess, sys

EXCLUDED = ["Solidity.Scratch", "Solidity.Corpus", "Solidity.TestSuite",
            "Solidity.Solkey.TestSuite", "Solidity.Examples"]
CHECKLIKE = re.compile(r"(Controls|Checks|Check|Tests|Test)$")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)

def under(m, p): return m == p or m.startswith(p + ".")
def is_controls(m): return m.rsplit(".", 1)[-1].endswith("Controls")
def checklike(m): return bool(CHECKLIKE.search(m.rsplit(".", 1)[-1]))

def tree():
    files = subprocess.run(["git", "ls-files", "-co", "--exclude-standard", "--", "Solidity"],
                           capture_output=True, text=True, check=True).stdout.split("\n")
    mods = {}
    for f in files:
        if not f.endswith(".lean") or not pathlib.Path(f).is_file(): continue
        m = f[:-5].replace("/", ".")
        if any(under(m, x) for x in EXCLUDED): continue
        src = pathlib.Path(f).read_text(errors="replace")
        # imports precede the first non-header command; stop at the first declaration keyword
        head = re.split(r"^(?:namespace|section|open|def|theorem|set_option|variable|noncomputable|@\[)", src, maxsplit=1, flags=re.M)[0]
        head = re.sub(r"/-.*?-/", "", head, flags=re.S)
        mods[m] = [i for i in IMPORT.findall(head) if i.startswith("Solidity")]
    return mods

def classify(mods):
    controls = sorted(m for m in mods if is_controls(m))
    seeds = [m for m in mods if not checklike(m)]
    reach, stack = set(), list(seeds)
    while stack:
        m = stack.pop()
        for i in mods.get(m, []):
            if i not in reach and i in mods:
                reach.add(i); stack.append(i)
    reachable = [c for c in controls if c in reach]
    return controls, reachable, [c for c in controls if c not in reach]

def edges(mods, controls):
    cs = set(controls)
    return sorted((m, i) for m in mods if not is_controls(m) for i in mods[m] if i in cs)

def main():
    a = sys.argv[1:]
    mods = tree()
    controls, reachable, unreachable = classify(mods)
    if a[:1] == ["--list"] and len(a) == 2:
        rows = {"reachable": reachable, "unreachable": unreachable,
                "edges": [f"{m} -> {i}" for m, i in edges(mods, controls)]}.get(a[1])
        if rows is None: raise ValueError("unknown list " + a[1])
        print("\n".join(rows)); return 0
    if a == ["--check"]:
        bad = 0
        if set(reachable) & set(unreachable) or sorted(reachable + unreachable) != controls:
            print("controls-classify: classes not a partition"); bad = 1
        un = set(unreachable)
        # independent pass: one closure from all non-check-like modules
        seen, st = set(), [m for m in mods if not checklike(m)]
        while st:
            for i in mods.get(st.pop(), []):
                if i in mods and i not in seen: seen.add(i); st.append(i)
        for m in sorted(seen & un): print(f"controls-classify: {m} is library-reachable"); bad = 1
        return bad
    if a: raise ValueError("usage: controls-classify.py [--list reachable|unreachable|edges] [--check]")
    print(f"controls={len(controls)} reachable={len(reachable)} unreachable={len(unreachable)} "
          f"edges={len(edges(mods, controls))}")
    return 0

if __name__ != "__main__": pass
else:
  try: sys.exit(main())
  except Exception as e: print("controls-classify: " + str(e), file=sys.stderr); sys.exit(2)
