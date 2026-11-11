#!/usr/bin/env python3
"""Repository hygiene ratchet (plan step q1-hygiene-gate): size and process-ID path rules.

Rules (tracked Git content of the head commit; the working tree is not read):
  size    every tracked non-.lean blob of head is at most LIMIT_BYTES = 200 KB, where
          1 KB = 1024 bytes, so 204800 bytes passes and 204801 fails. Binary blobs count too.
  lines   the non-.lean paths of base..head add at most LIMIT_LINES = 20000 lines in total.
          Added lines are summed per changed path and never netted: deletions (in the same or
          other files) do not cancel additions, and splitting a bulk addition over many files or
          directories does not help, because the limit is on the sum over the whole candidate
          tree. A text path counts the added lines of `git diff --numstat`; a binary blob that is
          added or changed counts every newline byte of its new content. An exact (100%) rename
          adds nothing. There are no exceptions to this rule.
  paths   no tracked path (Lean paths included) has a segment naming a process or batch ID.
          A segment is split into tokens at '-', '_', '.', '+' and spaces; it offends when a
          token is h<digits>, g<digits>, v<digits> or item<digits> (any case), when it starts
          with 'roadmap-' or 'roadmap_' (any case), or, for a directory segment only, when it
          contains '-2026' followed by four digits and no fifth digit (a dated directory).
          Ordinary words never match: 'h2o', 'ipv6', 'items5', 'vector', 'FrozenV1' are not IDs.

Legacy exceptions (allow.json) are seeded once from a historical tree and may only shrink:
  seed    the commit whose tree the exceptions were measured on (the merge base at seeding).
  paths   offending prefixes of the seed tree: the path up to and including its first offending
          segment. A prefix only covers paths that existed under it in the seed tree, so a new
          file inside a legacy directory, or a rename of a legacy path, still fails.
  bytes   {path: size} for seed blobs over the limit; head may keep the path at or below that size.
Every entry is re-derived from the seed tree on each run. The allowlist ratchet compares each
commit of base..head with every one of its parents (merge parents included) and base with head:
a commit may delete entries but never add, rewrite or broaden one, never change `seed`, never
delete allow.json, and may introduce allow.json only when no ancestor had one, with a seed that is
an ancestor of every parent and entries equal to the full seed of that tree.

Base (never committed): --base REV, else $HYGIENE_BASE, else merge-base(head, origin/master);
on master itself that merge base is head, and head's first parent is used instead.

Usage: check.py [--base REV] [--head REV]     exit 0 pass, 1 policy failure, 2 setup error
       check.py seed [--rev REV]              print the allow.json seeded from REV's tree
                                              (default origin/master: seed after merging it)
"""
import argparse, json, os, re, subprocess, sys

LIMIT_BYTES = 200 * 1024
LIMIT_LINES = 20000
ALLOW = "scripts/hygiene/allow.json"
ZERO = "0" * 40
TOKEN = re.compile(r"[-_.+ ]+")
ID_TOKEN = re.compile(r"(?:h|g|v|item)[0-9]+", re.I)
ROADMAP = re.compile(r"roadmap[-_]", re.I)
DATED_DIR = re.compile(r"-2026[0-9]{4}(?![0-9])")
REPAIR = ("Repair without growing scripts/hygiene/allow.json (it only shrinks): lane results go in the\n"
          "  lane result channel (CLOUD-RESULT), evidence, logs and receipts go to the private evidence\n"
          "  repository (scripts/coord-tools/coord-evidence), and reproducible bulk data comes from a\n"
          "  committed generator whose output stays outside Git. Name paths after their content.")


class SetupError(Exception):
    pass


def git(*args, inp=None, ok=(0,)):
    r = subprocess.run(["git", *args], input=inp, capture_output=True)
    if r.returncode not in ok:
        raise SetupError(f"git {' '.join(args)} failed: {r.stderr.decode(errors='replace').strip()}")
    return r.stdout


def rev(r):
    try:
        return git("rev-parse", "--verify", "-q", r + "^{commit}").decode().strip()
    except SetupError:
        raise SetupError(f"unknown commit {r!r}; fetch full history (git fetch --unshallow origin) or pass --base")


def offending_segment(path):
    """(prefix, segment) for the first offending segment of `path`, or None."""
    segs = path.split("/")
    for i, s in enumerate(segs):
        is_dir = i < len(segs) - 1
        if (any(ID_TOKEN.fullmatch(t) for t in TOKEN.split(s) if t) or ROADMAP.match(s)
                or (is_dir and DATED_DIR.search(s))):
            return "/".join(segs[:i + 1]), s
    return None


def tree(commit):
    """{path: (sha, size)} of the blobs of `commit` (submodules skipped)."""
    out, res = git("ls-tree", "-r", "-l", "-z", "--full-tree", commit), {}
    for rec in out.split(b"\0"):
        if not rec: continue
        meta, path = rec.split(b"\t", 1)
        _, typ, sha, size = meta.split()
        if typ == b"blob":
            res[path.decode("utf-8", "surrogateescape")] = (sha.decode(), int(size))
    return res


def seed_of(commit):
    t = tree(commit)
    paths = sorted({offending_segment(p)[0] for p in t if offending_segment(p)})
    sizes = {p: s for p, (_, s) in sorted(t.items()) if not p.endswith(".lean") and s > LIMIT_BYTES}
    return {"seed": commit, "paths": paths, "bytes": sizes}, t


def read_allow(commit):
    """The allow.json of `commit`, or None when absent. Malformed data is a SetupError."""
    r = subprocess.run(["git", "show", f"{commit}:{ALLOW}"], capture_output=True)
    if r.returncode != 0: return None
    try:
        a = json.loads(r.stdout)
    except ValueError as e:
        raise SetupError(f"{ALLOW} at {commit[:12]} is not JSON: {e}")
    if (not isinstance(a, dict) or set(a) - {"comment"} != {"seed", "paths", "bytes"}
            or not isinstance(a["seed"], str) or not re.fullmatch(r"[0-9a-f]{40}", a["seed"])
            or not isinstance(a["paths"], list) or not all(isinstance(p, str) for p in a["paths"])
            or a["paths"] != sorted(set(a["paths"]))
            or not isinstance(a["bytes"], dict)
            or not all(isinstance(v, int) and not isinstance(v, bool) for v in a["bytes"].values())):
        raise SetupError(f"{ALLOW} at {commit[:12]} is malformed: need keys seed (40-hex commit), "
                         "paths (sorted unique list of strings), bytes ({path: int}) and optional comment")
    return a


SEEDS = {}


def verify_entries(a, where):
    """Every entry of `a` must be derivable from its seed tree. Returns failure lines."""
    s = a["seed"]
    if s not in SEEDS:
        if subprocess.run(["git", "cat-file", "-e", s + "^{commit}"], capture_output=True).returncode:
            raise SetupError(f"{ALLOW} at {where}: seed {s} is not in this clone; fetch full history")
        SEEDS[s] = seed_of(s)[0]
    full, bad = SEEDS[s], []
    for p in a["paths"]:
        if p not in full["paths"]:
            bad.append(f"FAIL {ALLOW} at {where}: path entry {p!r} is not an offending prefix of seed {s[:12]}")
    for p, n in a["bytes"].items():
        if full["bytes"].get(p) != n:
            bad.append(f"FAIL {ALLOW} at {where}: bytes entry {p!r}: {n} is not the seed {s[:12]} size of an "
                       f"over-limit blob ({full['bytes'].get(p, 'absent or within the limit')})")
    return bad


def ratchet(child, parent, a_c, a_p, where):
    """Failure lines when `child`'s allowlist is not a shrink of `parent`'s."""
    if a_c is None:
        return [f"FAIL {where}: deletes {ALLOW}; delete its entries instead"] if a_p is not None else []
    if a_p is not None:
        bad = []
        if a_c["seed"] != a_p["seed"]:
            bad.append(f"FAIL {where}: changes the seed {a_p['seed'][:12]} -> {a_c['seed'][:12]}; the seed is fixed")
        for p in sorted(set(a_c["paths"]) - set(a_p["paths"])):
            bad.append(f"FAIL {where}: adds path exception {p!r}; exceptions may only be removed")
        for p, n in sorted(a_c["bytes"].items()):
            if p not in a_p["bytes"]:
                bad.append(f"FAIL {where}: adds bytes exception {p!r}; exceptions may only be removed")
            elif n != a_p["bytes"][p]:
                bad.append(f"FAIL {where}: rewrites bytes exception {p!r} {a_p['bytes'][p]} -> {n}")
        return bad
    # Introduction: once in history, never again, and bound to an ancestor tree.
    if git("rev-list", "-1", parent, "--", ALLOW).strip():
        return [f"FAIL {where}: reintroduces {ALLOW}, which an ancestor of {parent[:12]} already had"]
    if subprocess.run(["git", "merge-base", "--is-ancestor", a_c["seed"], parent], capture_output=True).returncode:
        return [f"FAIL {where}: introduces {ALLOW} with seed {a_c['seed'][:12]}, not an ancestor of {parent[:12]}"]
    full = SEEDS.get(a_c["seed"]) or seed_of(a_c["seed"])[0]
    if a_c["paths"] != full["paths"] or a_c["bytes"] != full["bytes"]:
        return [f"FAIL {where}: introduces {ALLOW} that differs from the seed of {a_c['seed'][:12]}; "
                f"regenerate it with `check.py seed --rev {a_c['seed'][:12]}`"]
    return []


def check_allow_history(base, head):
    bad = []
    commits = git("rev-list", "--parents", f"{base}..{head}").decode().split("\n")
    cache = {}

    def allow(c):
        if c not in cache: cache[c] = read_allow(c)
        return cache[c]
    blob = {}
    revs = {w for line in commits for w in line.split()}
    if revs:
        inp = "".join(f"{c}:{ALLOW}\n" for c in sorted(revs)).encode()
        for c, line in zip(sorted(revs), git("cat-file", "--batch-check", inp=inp).decode().splitlines()):
            blob[c] = None if line.endswith("missing") else line.split()[0]
    for line in commits:
        if not line: continue
        c, *parents = line.split()
        for p in parents:
            if blob.get(c) != blob.get(p):
                bad += ratchet(c, p, allow(c), allow(p), f"commit {c[:12]} (vs parent {p[:12]})")
    bad += ratchet(head, base, allow(head), allow(base), f"head {head[:12]} (vs base {base[:12]})")
    return bad


def line_additions(base, head):
    """{path: added lines} over non-.lean paths changed in base..head (see the module doc)."""
    opts = ["-M100%", "--diff-filter=d", "--no-ext-diff", "--no-textconv", "-z", base, head]
    out, added, binary = git("diff", "--numstat", *opts).split(b"\0"), {}, []
    i = 0
    while i < len(out) - 1:
        a, _, path = out[i].split(b"\t", 2)
        if path == b"":  # rename: old and new paths follow
            path = out[i + 2]; i += 3
        else:
            i += 1
        p = path.decode("utf-8", "surrogateescape")
        if p.endswith(".lean"): continue
        if a == b"-": binary.append(p)
        elif int(a): added[p] = int(a)
    if binary:
        t = tree(head)
        shas = [t[p][0] for p in binary]
        data = git("cat-file", "--batch", inp="".join(s + "\n" for s in shas).encode())
        pos = 0
        for p in binary:
            nl = data.index(b"\n", pos); size = int(data[pos:nl].split()[2])
            n = data[nl + 1: nl + 1 + size].count(b"\n"); pos = nl + 2 + size
            if n: added[p] = n
    return added


def evaluate(base, head):
    """(ok, report lines)."""
    rep = []
    allow = read_allow(head)
    if allow is None:
        raise SetupError(f"{ALLOW} is missing at {head[:12]}; restore it from the base commit")
    bad = verify_entries(allow, f"head {head[:12]}") + check_allow_history(base, head)
    seed_tree = tree(allow["seed"])
    seeded = {p for p in seed_tree if offending_segment(p)}
    t = tree(head)
    legacy = set(allow["paths"])
    for p in sorted(t):
        hit = offending_segment(p)
        if not hit: continue
        prefix, seg = hit
        if prefix in legacy and p in seeded: continue
        why = (f"is a new path under legacy prefix {prefix!r}; the exception covers only paths of seed "
               f"{allow['seed'][:12]}" if prefix in legacy else "is not a legacy exception")
        bad.append(f"FAIL path {p!r}: segment {seg!r} names a process or batch ID and {why}")
    for p, (_, size) in sorted(t.items()):
        if p.endswith(".lean") or size <= LIMIT_BYTES: continue
        cap = allow["bytes"].get(p)
        if cap is None:
            bad.append(f"FAIL size {p!r}: {size} bytes over the {LIMIT_BYTES}-byte (200 KB) limit")
        elif size > cap:
            bad.append(f"FAIL size {p!r}: {size} bytes; its legacy exception stops at {cap} bytes "
                       f"(limit {LIMIT_BYTES})")
    added = line_additions(base, head)
    total = sum(added.values())
    if total > LIMIT_LINES:
        by_dir = {}
        for p, n in added.items():
            d = "/".join(p.split("/")[:-1][:2]) + "/" if "/" in p else "(top level)"
            by_dir[d] = by_dir.get(d, 0) + n
        bad.append(f"FAIL lines: non-.lean paths add {total} lines over {len(added)} file(s), over the "
                   f"{LIMIT_LINES}-line limit by {total - LIMIT_LINES}")
        for d, n in sorted(by_dir.items(), key=lambda x: (-x[1], x[0]))[:10]:
            bad.append(f"  +{n} {d}")
    else:
        rep.append(f"ok lines: non-.lean paths add {total} lines (limit {LIMIT_LINES})")
    rep.append(f"ok legacy exceptions: {len(allow['paths'])} path prefix(es), {len(allow['bytes'])} size entr(ies) "
               f"of seed {allow['seed'][:12]}")
    if bad: rep = bad + [REPAIR]
    return not bad, rep


def default_base(head):
    env = os.environ.get("HYGIENE_BASE")
    if env: return rev(env)
    if subprocess.run(["git", "rev-parse", "-q", "--verify", "origin/master"], capture_output=True).returncode:
        raise SetupError("no origin/master to compare with; run `git fetch origin master` or pass --base REV")
    base = git("merge-base", head, "origin/master").decode().strip()
    if base == head:  # on master: check head against its first parent
        parents = git("rev-list", "--parents", "-1", head).decode().split()[1:]
        if not parents:
            raise SetupError("head is a root commit; pass --base REV")
        base = parents[0]
    return base


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", nargs="?", default="check", choices=["check", "seed"])
    ap.add_argument("--base"); ap.add_argument("--head", default="HEAD"); ap.add_argument("--rev")
    a = ap.parse_args(argv)
    try:
        if git("rev-parse", "--is-shallow-repository").strip() != b"false":
            raise SetupError("shallow clone: the ratchet needs full history (git fetch --unshallow origin)")
        if a.mode == "seed":
            r = rev(a.rev or "origin/master")
            s = seed_of(r)[0]
            print(json.dumps({"comment": "Legacy exceptions seeded by `check.py seed`; entries may only be removed.",
                              **s}, indent=1))
            return 0
        head = rev(a.head)
        base = rev(a.base) if a.base else default_base(head)
        print(f"hygiene: base {base[:12]} head {head[:12]}")
        ok, rep = evaluate(base, head)
        print("\n".join(rep))
        print("hygiene: PASS" if ok else "hygiene: FAIL")
        return 0 if ok else 1
    except (SetupError, OSError, ValueError, IndexError, KeyError) as e:
        print(f"hygiene: error: {e!s}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
