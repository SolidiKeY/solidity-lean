#!/usr/bin/env python3
"""Lean size budget ratchet (plan step lb-lean-budget).

Compares the `*.lean` files of HEAD with a base revision and fails when, outside the
globs of steps named by a `Lean-Budget: <step-id>` commit trailer in base..head,
  (a) any frozen area of allow.json grows (net lines over the area), or
  (b) the net Lean lines over all counted files exceed allow.json's `cap`.
Counts come from tree contents (per-file line totals at base vs head), not diff hunks:
a rename into a frozen area grows it, a move out shrinks it. Generated library roots
(read from scripts/coord-tools/register.sh and fragments.py) are not counted.

Base (computed, never committed):
  --base REV                   explicit (CI: github.event.before on a push to master,
                               the PR base's merge base on a pull request)
  $LEAN_BUDGET_BASE            the same, from the environment
  default                      merge-base(HEAD, origin/master) (lane gate); on master
                               that is HEAD itself, so CI passes --base there
Usage:
  check.py [--base REV] [--head REV]      run the check (exit 0 pass, 1 fail, 2 error)
  check.py measure [--days N] [--ref R]   per first-parent merge on R: net lines, p50/p75/p90
  check.py replay [--count N] [--ref R]   run the check on the last N first-parent merges of R
"""
import argparse, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ALLOW = os.path.join(HERE, "allow.json")
TRAILER = "Lean-Budget"


def git(*args, check=True):
    r = subprocess.run(["git", *args], capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def glob_re(g):
    out, i = [], 0
    while i < len(g):
        if g.startswith("**/", i): out.append("(?:.*/)?"); i += 3
        elif g.startswith("**", i): out.append(".*"); i += 2
        elif g[i] == "*": out.append("[^/]*"); i += 1
        elif g[i] == "?": out.append("[^/]"); i += 1
        else: out.append(re.escape(g[i])); i += 1
    return re.compile("".join(out) + r"\Z")


def matches(path, globs): return any(glob_re(g).match(path) for g in globs)


def generated_roots(rev):
    """The generated roots, read from the generators at `rev` (not a hand list)."""
    roots = set()
    for f in ("scripts/coord-tools/register.sh", "scripts/coord-tools/fragments.py"):
        r = subprocess.run(["git", "show", f"{rev}:{f}"], capture_output=True, text=True)
        if r.returncode != 0: continue
        roots |= set(re.findall(r'\(\s*"([^"\s]+\.lean)"', r.stdout))  # ("Root.lean", ... tuples
        for m in re.finditer(r"ROOTS\s*=\s*\[([^\]]*)\]", r.stdout):  # ROOTS = ["a.lean", ...]
            roots |= set(re.findall(r'"([^"\s]+\.lean)"', m.group(1)))
    return roots


class Lines:
    """Line counts of blobs, read in one `git cat-file --batch` stream."""
    def __init__(self): self.cache = {}

    def count(self, shas):
        todo = [s for s in set(shas) if s and s not in self.cache]
        if todo:
            p = subprocess.run(["git", "cat-file", "--batch"], input="\n".join(todo).encode() + b"\n",
                               capture_output=True, check=True)
            data, pos = p.stdout, 0
            for s in todo:
                nl = data.index(b"\n", pos); hdr = data[pos:nl].split()
                if len(hdr) < 3: raise RuntimeError(f"blob {s} missing (shallow clone? fetch full history)")
                size = int(hdr[2])
                body = data[nl + 1: nl + 1 + size]; pos = nl + 2 + size
                self.cache[s] = body.count(b"\n") + (1 if body and not body.endswith(b"\n") else 0)
        return {s: self.cache.get(s, 0) for s in shas}


LINES = Lines()
ZERO = "0" * 40


def deltas(base, head, roots):
    """{path: head_lines - base_lines} for every changed *.lean path but generated roots."""
    out = git("diff-tree", "-r", "--no-renames", "-z", base, head)
    toks = out.split("\0"); rows = []
    for i in range(0, len(toks) - 1, 2):
        meta, path = toks[i].split(), toks[i + 1]
        if not path.endswith(".lean") or path in roots: continue
        a, b = meta[2], meta[3]
        rows.append((path, None if a == ZERO else a, None if b == ZERO else b))
    n = LINES.count([s for _, a, b in rows for s in (a, b) if s])
    return {p: (n[b] if b else 0) - (n[a] if a else 0) for p, a, b in rows}


def load_allow(path=ALLOW):
    with open(path) as f: cfg = json.load(f)
    if not isinstance(cfg.get("cap"), int) or cfg["cap"] <= 0: raise ValueError("allow.json: cap must be a positive int")
    return cfg


def trailers(base, head):
    out = git("log", "--format=%(trailers:key=" + TRAILER + ",valueonly,separator=%x00)%x01", f"{base}..{head}")
    ids = set()
    for rec in out.split("\x01"):
        for v in rec.split("\0"):
            for w in v.replace(",", " ").split():
                ids.add(w.strip())
    return ids


def evaluate(base, head, cfg, roots=None):
    """Returns (ok, report lines)."""
    roots = generated_roots(head) | generated_roots(base) if roots is None else roots
    d = deltas(base, head, roots)
    steps = trailers(base, head)
    rep, ok = [], True
    unknown = sorted(steps - set(cfg["steps"]))
    if unknown:
        ok = False; rep.append(f"FAIL unknown {TRAILER} step id(s): {', '.join(unknown)} (known: see scripts/lean-budget/allow.json)")
    exempt_globs = [g for s in steps if s in cfg["steps"] for g in cfg["steps"][s]]
    counted = {p: v for p, v in d.items() if not matches(p, exempt_globs)}
    exempt = {p: v for p, v in d.items() if p not in counted}
    if steps: rep.append(f"trailers: {', '.join(sorted(steps))}; exempt net {sum(exempt.values()):+d} over {len(exempt)} file(s)")
    for area in cfg["frozen"]:
        files = {p: v for p, v in counted.items() if matches(p, area["globs"]) and not matches(p, area["except"])}
        net = sum(files.values())
        if net > 0:
            ok = False
            rep.append(f"FAIL frozen area {area['name']} ({', '.join(area['globs'])}) grew by {net} line(s); it is shrink-only.")
            for p, v in sorted(files.items(), key=lambda x: -x[1])[:10]:
                if v: rep.append(f"  {v:+d} {p}")
            rep.append(f"  to allow: a commit trailer `{TRAILER}: <step-id>` for a step in allow.json whose globs cover "
                       f"these files ({hint(cfg, files)})")
        elif files: rep.append(f"ok frozen area {area['name']}: net {net:+d}")
    total, cap = sum(counted.values()), cfg["cap"]
    if total > cap:
        ok = False
        rep.append(f"FAIL net Lean lines {total:+d} exceed the per-merge cap {cap} by {total - cap} line(s).")
        for p, v in sorted(counted.items(), key=lambda x: -x[1])[:10]:
            if v > 0: rep.append(f"  {v:+d} {p}")
        rep.append(f"  to allow: a commit trailer `{TRAILER}: <step-id>` for a step in allow.json whose globs cover "
                   f"the growth ({hint(cfg, counted)})")
    else: rep.append(f"ok net Lean lines {total:+d} (cap {cap}) over {len(counted)} changed file(s)")
    return ok, rep


def hint(cfg, files):
    grown = [p for p, v in files.items() if v > 0]
    ids = [s for s, gs in cfg["steps"].items() if grown and any(matches(p, gs) for p in grown)]
    return "candidates: " + ", ".join(ids) if ids else "no listed step covers them; shrink, or ESCALATE for a new step"


def default_base(head):
    env = os.environ.get("LEAN_BUDGET_BASE")
    if env: return env
    if subprocess.run(["git", "rev-parse", "-q", "--verify", "origin/master"], capture_output=True).returncode != 0:
        raise RuntimeError("no origin/master; pass --base")
    # On master itself this is HEAD and checks nothing; CI passes --base there.
    return git("merge-base", head, "origin/master").strip()


def pct(xs, q):
    xs = sorted(xs)
    if not xs: return 0
    k = (len(xs) - 1) * q; lo = int(k); hi = min(lo + 1, len(xs) - 1)
    return round(xs[lo] + (xs[hi] - xs[lo]) * (k - lo))


def merges(ref, days=None, count=None):
    args = ["log", "--first-parent", "--merges", "--format=%H %cI %s"]
    if days: args.append(f"--since={days}.days.ago")
    if count: args.append(f"-{count}")
    return [l.split(" ", 2) for l in git(*args, ref).splitlines() if l]


def area_of(p):
    parts = p.split("/")
    if parts[0] != "Solidity": return parts[0] if len(parts) > 1 else "(top)"
    return "Solidity/" + (parts[1] if len(parts) > 2 else "(root)")


def cmd_measure(a):
    ms = merges(a.ref, days=a.days)
    totals, per = [], {}
    roots = generated_roots(a.ref)
    for h, date, subj in ms:
        d = deltas(f"{h}^1", h, roots)
        totals.append(sum(d.values()))
        acc = {}
        for p, v in d.items(): acc[area_of(p)] = acc.get(area_of(p), 0) + v
        for k in set(per) | set(acc): per.setdefault(k, []).append(acc.get(k, 0))
        if a.verbose: print(f"{h[:9]} {date[:10]} {sum(d.values()):+8d} {subj[:60]}")
    n = len(ms)
    for k in per: per[k] = [0] * (n - len(per[k])) + per[k] if len(per[k]) < n else per[k]
    print(f"{n} first-parent merges on {a.ref} in the last {a.days} days (generated roots excluded)")
    print(f"{'area':40} {'p50':>7} {'p75':>7} {'p90':>7} {'sum':>9} {'touched':>7} {'p75 touched':>11}")
    t = [x for x in totals if x]
    print(f"{'ALL *.lean':40} {pct(totals,.5):7d} {pct(totals,.75):7d} {pct(totals,.9):7d} {sum(totals):9d} {len(t):7d} {pct(t,.75):11d}")
    for k in sorted(per, key=lambda k: -sum(per[k])):
        xs = per[k]
        if sum(abs(x) for x in xs) == 0: continue
        t = [x for x in xs if x]
        print(f"{k:40} {pct(xs,.5):7d} {pct(xs,.75):7d} {pct(xs,.9):7d} {sum(xs):9d} {len(t):7d} {pct(t,.75):11d}")
    p75 = pct(totals, .75)
    print(f"cap = p75 {p75} rounded up to a multiple of 500 = {max(500, -(-p75 // 500) * 500)}")


def cmd_replay(a):
    cfg = load_allow(a.allow); failed = 0
    for h, date, subj in merges(a.ref, count=a.count):
        ok, rep = evaluate(f"{h}^1", h, cfg)
        failed += not ok
        print(f"{'PASS' if ok else 'FAIL'} {h[:9]} {date[:10]} {subj[:60]}")
        for l in rep:
            if not ok and (l.startswith("FAIL") or l.startswith("trailers")): print("   ", l)
    print(f"{failed} of {a.count} would have failed")


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("mode", nargs="?", default="check", choices=["check", "measure", "replay"])
    ap.add_argument("--base"); ap.add_argument("--head", default="HEAD")
    ap.add_argument("--allow", default=ALLOW)
    ap.add_argument("--ref", default="origin/master"); ap.add_argument("--days", type=int, default=14)
    ap.add_argument("--count", type=int, default=20); ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args(argv)
    try:
        if a.mode == "measure": return cmd_measure(a) or 0
        if a.mode == "replay": return cmd_replay(a) or 0
        cfg = load_allow(a.allow)
        base = a.base or default_base(a.head)
        base = git("rev-parse", base + "^{commit}").strip()
        print(f"lean-budget: base {base[:12]} head {git('rev-parse', a.head).strip()[:12]}")
        ok, rep = evaluate(base, a.head, cfg)
        print("\n".join(rep))
        print("lean-budget: PASS" if ok else "lean-budget: FAIL")
        return 0 if ok else 1
    except (RuntimeError, ValueError, OSError, subprocess.CalledProcessError) as e:
        print(f"lean-budget: error: {e}", file=sys.stderr); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
