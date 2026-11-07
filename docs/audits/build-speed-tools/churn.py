#!/usr/bin/env python3
"""Rebuild exposure from `git log --since=7.days --name-only`.

For each module: `touch` = commits editing its file; `rebuild` = commits editing
its file or any file in its transitive import closure (each such commit makes
Lake re-elaborate it). With --times, also seconds/week = rebuild * seconds.
Usage: churn.py GRAPH_JSON [--times TSV] [--since 7.days] [--first-parent]
"""
import json, subprocess, sys, collections
g = json.load(open(sys.argv[1]))
args = sys.argv[2:]
since = args[args.index("--since") + 1] if "--since" in args else "7.days"
times = {}
if "--times" in args:
    for ln in open(args[args.index("--times") + 1]):
        p = ln.rstrip("\n").split("\t")
        try: times[p[0]] = float(p[1])
        except (IndexError, ValueError): pass
graph = g["graph"]
# default: every non-merge commit (each lane commit that changes a closure);
# --first-parent: master's own history, merges diffed against their first
# parent (each integration build of master).
mode = ["--first-parent", "-m", "--diff-merges=first-parent"] if "--first-parent" in args else ["--no-merges"]
log = subprocess.check_output(["git", "log", "origin/master" if "--first-parent" in args else "HEAD", f"--since={since}", *mode, "--name-only", "--format=@@%H"], text=True)
commits, cur = [], None
for ln in log.splitlines():
    if ln.startswith("@@"): cur = set(); commits.append(cur)
    elif ln.endswith(".lean") and cur is not None:
        cur.add(ln[:-5].replace("/", "."))
commits = [c for c in commits if c & graph.keys()]
touch = collections.Counter(m for c in commits for m in c if m in graph)
# closure per module, memoised
closure = {}
sys.setrecursionlimit(100000)
def clo(m):
    if m in closure: return closure[m]
    s = {m}
    for d in graph[m]: s |= clo(d)
    closure[m] = frozenset(s); return closure[m]
rebuild = collections.Counter()
for c in commits:
    for m in graph:
        if c & clo(m): rebuild[m] += 1
print(f"lean-touching non-merge commits since {since}: {len(commits)}")
print(f"total module rebuilds implied: {sum(rebuild.values())}")
print("\n## most-touched modules")
for m, n in touch.most_common(20): print(f"{n:4d} touch {rebuild[m]:5d} rebuild  {m}")
print("\n## highest rebuild count")
for m, n in rebuild.most_common(15): print(f"{n:5d}  {m}")
if times:
    cost = {m: rebuild[m] * t for m, t in times.items() if m in graph}
    print(f"\n## seconds/week = rebuild x measured seconds (measured {len(cost)} modules)")
    for m, s in sorted(cost.items(), key=lambda x: -x[1])[:40]:
        print(f"{s/3600:7.2f} h/wk  {rebuild[m]:5d} x {times[m]:7.1f}s  touch {touch[m]:3d}  {m}")
json.dump({"touch": touch, "rebuild": rebuild}, open(sys.argv[1] + (".fp" if "--first-parent" in args else "") + ".churn.json", "w"))
