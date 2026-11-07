#!/usr/bin/env python3
"""Import-graph inventory for docs/audits/build-speed.md.

Parses `import` lines of every module reachable from the default targets
(Solidity, SolidityExamples) plus SolkeyTestSuite and SolidityCorpus, and prints
area counts, depth, the critical path (by line count and, when a times file is
given, by measured seconds), the top transitive fan-in, the largest files and,
with --churn, rebuild exposure (#commits touching a module or anything it
imports in the last 7 days).

Usage: import_graph.py [--times TSV(module\tseconds)] [--json OUT]
"""
import json, os, re, subprocess, sys, collections, pathlib

ROOTS = ["Solidity", "SolidityExamples", "SolkeyTestSuite", "SolidityCorpus"]
SRC_DIRS = {"LeanTeX": "vendor/LeanTeX"}

def path_of(mod):
    top = mod.split(".")[0]
    base = SRC_DIRS.get(top, ".")
    return os.path.join(base, *mod.split(".")) + ".lean"

IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(.+)$")

def imports_of(p):
    out = []
    try:
        lines = open(p, encoding="utf-8", errors="replace").read().splitlines()
    except FileNotFoundError:
        return None
    in_comment = 0
    for ln in lines:
        s = ln.strip()
        if s.startswith("/-"):
            in_comment += 1
        if in_comment:
            if "-/" in s:
                in_comment -= 1
            continue
        m = IMPORT.match(ln)
        if m:
            out += [w for w in m.group(1).split() if not w.startswith("--")]
        elif s and not s.startswith("--") and not s.startswith("prelude") and not s.startswith("module"):
            break
    return out

def main():
    args = sys.argv[1:]
    times = {}
    if "--times" in args:
        for ln in open(args[args.index("--times") + 1]):
            parts = ln.split("\t")
            if len(parts) >= 2:
                try: times[parts[0]] = float(parts[1])
                except ValueError: pass
    graph, lines, lib = {}, {}, {}
    stack = []
    for r in reversed(ROOTS):  # first root to reach a module owns it
        stack.append((r, r))
    pending = list(stack); stack = []
    while pending or stack:
        if not stack: stack.append(pending.pop())
        m, root = stack.pop()
        if m in graph: continue
        p = path_of(m)
        imps = imports_of(p)
        if imps is None:  # Lean / Init / Std
            continue
        graph[m] = imps
        lib[m] = root
        lines[m] = sum(1 for _ in open(p, encoding="utf-8", errors="replace"))
        for d in imps:
            stack.append((d, root))
    for m in graph:
        graph[m] = [d for d in graph[m] if d in graph]
    mods = [m for m in graph if m not in ROOTS]
    print(f"modules (excluding library roots): {len(mods)}; total lines {sum(lines[m] for m in mods)}")
    area = collections.Counter(".".join(m.split(".")[:2]) for m in mods)
    print("\n## modules per area (top 30)")
    for a, c in area.most_common(30):
        print(f"{c:6d}  {sum(lines[m] for m in mods if '.'.join(m.split('.')[:2])==a):8d} lines  {a}")
    # topological order
    order, seen = [], set()
    sys.setrecursionlimit(100000)
    def visit(m):
        if m in seen: return
        seen.add(m)
        for d in graph[m]: visit(d)
        order.append(m)
    for m in graph: visit(m)
    depth, best_lines, best_t, prev_l, prev_t = {}, {}, {}, {}, {}
    for m in order:
        ds = graph[m]
        depth[m] = 1 + max((depth[d] for d in ds), default=0)
        dl = max(ds, key=lambda d: best_lines[d], default=None)
        best_lines[m] = lines[m] + (best_lines[dl] if dl else 0); prev_l[m] = dl
        dt = max(ds, key=lambda d: best_t[d], default=None)
        best_t[m] = times.get(m, 0.0) + (best_t[dt] if dt else 0); prev_t[m] = dt
    dm = max(mods, key=lambda m: depth[m])
    print(f"\n## max import depth: {depth[dm]} (at {dm})")
    hist = collections.Counter(depth[m] for m in mods)
    print("depth histogram:", dict(sorted(hist.items())))
    def chain(end, prev):
        c = []
        while end: c.append(end); end = prev[end]
        return c[::-1]
    end = max(mods, key=lambda m: best_lines[m])
    c = chain(end, prev_l)
    print(f"\n## critical path by lines: {best_lines[end]} lines over {len(c)} modules")
    for m in c: print(f"   {lines[m]:6d}  {m}")
    if times:
        end = max(mods, key=lambda m: best_t[m])
        c = chain(end, prev_t)
        print(f"\n## critical path by measured seconds (unmeasured = 0): {best_t[end]:.0f}s over {len(c)} modules")
        for m in c: print(f"   {times.get(m,0):7.1f}s  {lines[m]:6d}  {m}")
    rev = collections.defaultdict(set)
    for m, ds in graph.items():
        for d in ds: rev[d].add(m)
    fanin = {}
    for m in mods:
        out, st = set(), [m]
        while st:
            for r in rev[st.pop()]:
                if r not in out: out.add(r); st.append(r)
        fanin[m] = len(out - set(ROOTS))
    print("\n## top 20 transitive fan-in (modules rebuilt by a change)")
    for m in sorted(mods, key=lambda m: -fanin[m])[:20]:
        print(f"{fanin[m]:6d}  {lines[m]:6d} lines  {m}")
    print("\n## top 20 largest files")
    for m in sorted(mods, key=lambda m: -lines[m])[:20]:
        print(f"{lines[m]:6d}  fanin {fanin[m]:5d}  {lib[m]:16s} {m}")
    if "--json" in args:
        json.dump({"graph": graph, "lines": lines, "fanin": fanin, "depth": depth, "lib": lib},
                  open(args[args.index("--json") + 1], "w"))

main()
