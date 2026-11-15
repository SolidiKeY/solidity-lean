#!/usr/bin/env python3
"""Tiny anti-unification compressor over Lean source.
Unit = indentation block (a line + deeper-indented lines). Tree = lines -> tokens.
Group units by shape, compute least general generalization (LGG) per group,
rank by MDL saving = (k-1)*const_tokens - k*holes.

Usage:
  au.py N FILE...                  top N clusters over FILEs (original mode)
  au.py --diff BASE HEAD [opts]    clusters that contain a unit made of lines added in
                                   BASE..HEAD and another unit of the tree at HEAD
    --min-save T     report clusters whose best pair saves >= T tokens (default 50)
    --exclude RE     ignore added units in paths matching RE (default: docs/, tests/,
                     scripts/hNN/ audit trees; '' keeps all)
    --scope full|near  corpus of other units: the whole tree (default) or the touched
                     files' grandparent directories
    --repo DIR       repository (default: cwd)    --json   JSON output
    --cache FILE     sqlite unit-key cache keyed by blob (default: <git-dir>/au-cache.sqlite)
  Pair saving (k=2 MDL) = const_tokens - 2*holes; holes <= 4 and const >= 15 as above.
  Lean, Python, shell and JS files (extensionless scripts by shebang).
  Exit 0: nothing >= T; 1: findings; 2: usage or git error.
"""
import re, sys, collections, os, subprocess, json, zlib, sqlite3, marshal

TOK = re.compile(r"[A-Za-z_Ͱ-Ͽᴀ-ᶿ'][\w'.!?Ͱ-Ͽ₀-ₜ]*|\d+|\S")

def blocks(path):
    lines = open(path, encoding="utf-8").read().split("\n")
    ind = [len(l) - len(l.lstrip()) if l.strip() else None for l in lines]
    out = []
    for i, l in enumerate(lines):
        if not l.strip() or l.strip().startswith("--") or l.strip().startswith("/-"):
            continue
        j = i + 1
        while j < len(lines) and (ind[j] is None or ind[j] > ind[i]):
            j += 1
        body = [TOK.findall(lines[k].strip()) for k in range(i, j) if lines[k].strip()]
        if 2 <= len(body) <= 40:
            out.append((path, i + 1, body))
    return out

def shape(body):
    return tuple(len(t) for t in body)

def lgg(bodies):
    """Token-wise LGG; consistent holes: same column tuple -> same hole var."""
    holes, pat = {}, []
    for li, line in enumerate(bodies[0]):
        row = []
        for ti in range(len(line)):
            col = tuple(b[li][ti] for b in bodies)
            if len(set(col)) == 1:
                row.append(col[0])
            else:
                row.append("?%d" % holes.setdefault(col, len(holes)))
        pat.append(row)
    return pat, len(holes)

def main(paths):
    units = [u for p in paths for u in blocks(p)]
    groups = collections.defaultdict(list)
    for u in units:
        groups[shape(u[2])].append(u)
    cands = []
    for g in groups.values():
        if len(g) < 2:
            continue
        # split group by first token of first line (head symbol) to stay meaningful
        by = collections.defaultdict(list)
        for u in g:
            by[u[2][0][0]].append(u)
        for sub in by.values():
            # dedupe nested: keep units whose start lines are distinct
            if len(sub) < 2:
                continue
            pat, h = lgg([u[2] for u in sub])
            const = sum(1 for r in pat for t in r if not t.startswith("?"))
            k = len(sub)
            if h > 4 or const < 15:
                continue
            save = (k - 1) * const - k * h
            if save > 0:
                cands.append((save, k, h, pat, [(p.split("/")[-1], l) for p, l, _ in sub]))
    cands.sort(key=lambda c: -c[0])
    # drop candidates whose instances are all contained in a better one's lines
    seen, shown = set(), 0
    for save, k, h, pat, locs in cands:
        key = frozenset(locs)
        if key <= seen:
            continue
        seen |= {(f, l + d) for f, l in locs for d in range(len(pat))}
        print(f"## save={save} instances={k} holes={h}  at {locs[:6]}{' ...' if k > 6 else ''}")
        for r in pat:
            print("   ", " ".join(r))
        shown += 1
        if shown >= int(sys.argv[1]):
            break

# ---------------------------------------------------------------- diff mode
MAXL, MAXH, MINC, CACHE_V = 60, 4, 15, 1
EXT = {".lean": "lean", ".py": "py", ".sh": "sh", ".mjs": "js", ".js": "js", ".cjs": "js", ".ts": "js"}
SKIP_DIRS = ("node_modules/", "vendor/", "third_party/", ".lake/")
LINE_COMMENT = {"lean": ("--", "/-", "-/"), "py": ("#",), "sh": ("#",), "js": ("//", "/*", "*")}
LEAN_BLOCK = re.compile(r"/-.*?-/", re.S)
PY_DOC = re.compile(r'"""[\s\S]*?"""|\'\'\'[\s\S]*?\'\'\'')


class GitError(Exception):
    pass


def git(repo, *args, inp=None, binary=False):
    r = subprocess.run(["git", "-C", repo, *args], input=inp, capture_output=True)
    if r.returncode != 0:
        raise GitError("git %s: %s" % (" ".join(args[:3]), r.stderr.decode(errors="replace").strip()))
    return r.stdout if binary else r.stdout.decode("utf-8", "replace")


def lang_of(path, head=None):
    if any(s in path for s in SKIP_DIRS):
        return None
    ext = os.path.splitext(path)[1]
    if ext in EXT:
        return EXT[ext]
    if ext == "" and head is not None and head.startswith(b"#!"):
        first = head.split(b"\n", 1)[0]
        if b"python" in first:
            return "py"
        if b"node" in first:
            return "js"
        if b"sh" in first:
            return "sh"
    return None


def clean(text, lang):
    """Blank comments (keeping line numbers) so they never form or join units."""
    keep_nl = lambda m: "\n" * m.group(0).count("\n")
    if lang == "lean":
        text = LEAN_BLOCK.sub(keep_nl, text)
    elif lang == "py":
        text = PY_DOC.sub(keep_nl, text)
    out = []
    for l in text.split("\n"):
        s = l.strip()
        out.append("" if any(s.startswith(c) for c in LINE_COMMENT[lang]) else l)
    return out


def units_of(text, lang, want=None):
    """Yield (key, start, end, body) for each indentation block of 2..MAXL code lines.
    key = crc of (lang, head token, shape). start/end are 1-based inclusive line numbers.
    With `want` (a set of starting lines) only those blocks are tokenized fully."""
    lines = clean(text, lang)
    n = len(lines)
    ind = [len(l) - len(l.lstrip()) if l.strip() else None for l in lines]
    toks = [None] * n
    for i in range(n):
        if ind[i] is None or (want is not None and (i + 1) not in want):
            continue
        j = i + 1
        while j < n and (ind[j] is None or ind[j] > ind[i]):
            j += 1
        idx = [k for k in range(i, j) if ind[k] is not None]
        if not (2 <= len(idx) <= MAXL):
            continue
        for k in idx:
            if toks[k] is None:
                toks[k] = TOK.findall(lines[k].strip())
        body = [toks[k] for k in idx]
        if not body[0]:
            continue
        key = zlib.crc32(repr((lang, body[0][0], shape(body))).encode())
        last = idx[-1] + 1
        yield key, i + 1, last, body


def index_blob(args):
    text, lang = args
    return [(k, s, e) for k, s, e, _ in units_of(text, lang)]


class Cache:
    def __init__(self, path):
        self.db = sqlite3.connect(path)
        self.db.execute("create table if not exists idx(blob text primary key, v int, data blob)")

    def get_many(self, blobs):
        got = {}
        blobs = list(blobs)
        for i in range(0, len(blobs), 500):
            chunk = blobs[i:i + 500]
            q = "select blob, data from idx where v=? and blob in (%s)" % ",".join("?" * len(chunk))
            for b, d in self.db.execute(q, [CACHE_V] + chunk):
                got[b] = marshal.loads(d)
        return got

    def put_many(self, items):
        self.db.executemany("insert or replace into idx values (?,?,?)",
                            [(b, CACHE_V, marshal.dumps(v)) for b, v in items])
        self.db.commit()


def cat_blobs(repo, shas):
    """Contents of blobs via one `git cat-file --batch`."""
    shas = list(dict.fromkeys(shas))
    if not shas:
        return {}
    raw = git(repo, "cat-file", "--batch", inp=("\n".join(shas) + "\n").encode(), binary=True)
    out, pos = {}, 0
    for sha in shas:
        nl = raw.index(b"\n", pos)
        hdr = raw[pos:nl].split()
        size = int(hdr[2])
        out[sha] = raw[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1
    return out


def added_lines(repo, base, head):
    """{path at HEAD: set of added line numbers}, rename-aware."""
    diff = git(repo, "diff", "-M", "-U0", "--no-color", "--no-ext-diff", base, head)
    out, path = collections.defaultdict(set), None
    for l in diff.split("\n"):
        if l.startswith("+++ "):
            path = None if l[4:] == "/dev/null" else l[6:]
        elif l.startswith("@@") and path:
            m = re.match(r"@@ -\S+ \+(\d+)(?:,(\d+))? @@", l)
            s, c = int(m.group(1)), int(m.group(2) or 1)
            out[path].update(range(s, s + c))
    return out


def tree(repo, head):
    out = {}
    for l in git(repo, "ls-tree", "-r", "-z", head).split("\0"):
        if not l:
            continue
        meta, path = l.split("\t", 1)
        mode, typ, sha = meta.split()
        if typ == "blob" and mode != "120000":
            out[path] = sha
    return out


def near(path, touched):
    roots = {os.path.dirname(os.path.dirname(t)) for t in touched}
    return any(r == "" or path.startswith(r + "/") for r in roots)


DEFAULT_EXCLUDE = r"^(?:docs/|tests/|scripts/h\d+/)"


def diff_mode(repo, base, head, min_save=50, scope="full", cache_path=None, jobs=None, frac=0.8, exclude=""):
    added = added_lines(repo, base, head)
    files = tree(repo, head)
    # language: by extension, or shebang for extensionless files (read only those)
    noext = [p for p in files if os.path.splitext(p)[1] == "" and not any(s in p for s in SKIP_DIRS)
             and (p.startswith("scripts/") or p in added)]
    heads = cat_blobs(repo, [files[p] for p in noext])
    langs = {}
    for p, sha in files.items():
        lg = lang_of(p, heads.get(sha))
        if lg:
            langs[p] = lg
    changed = [p for p in added if p in langs and not (exclude and re.search(exclude, p))]
    if not changed:
        return []
    # added units: blocks of a changed file whose code lines are >= frac added
    texts = cat_blobs(repo, [files[p] for p in changed])
    new_units, want_keys = [], set()
    for p in changed:
        text = texts[files[p]].decode("utf-8", "replace")
        add = added[p]
        lines = clean(text, langs[p])
        for key, s, e, body in units_of(text, langs[p]):
            code = [k for k in range(s, e + 1) if lines[k - 1].strip()]
            if sum(1 for k in code if k in add) >= frac * len(code):
                if sum(len(r) for r in body) >= MINC:
                    new_units.append((p, s, e, key, body))
                    want_keys.add(key)
    if not new_units:
        return []
    corpus = [p for p in langs if scope == "full" or p in added or near(p, changed)]
    if cache_path is None:
        gd = git(repo, "rev-parse", "--absolute-git-dir").strip()
        cache_path = os.path.join(gd, "au-cache.sqlite")
    cache = Cache(cache_path)
    shas = {files[p] for p in corpus}
    idx = cache.get_many(shas)
    miss = sorted(shas - set(idx))
    if miss:
        lang_by_sha = {files[p]: langs[p] for p in corpus}
        raw = cat_blobs(repo, miss)
        work = [(raw[s].decode("utf-8", "replace"), lang_by_sha[s]) for s in miss]
        if len(work) > 50:
            import multiprocessing
            with multiprocessing.Pool(jobs or os.cpu_count()) as pool:
                res = pool.map(index_blob, work, chunksize=16)
        else:
            res = [index_blob(w) for w in work]
        new = list(zip(miss, res))
        cache.put_many(new)
        idx.update(new)
    # candidate partners sharing a key with some added unit
    cand = collections.defaultdict(list)  # key -> [(path, start, end)]
    for p in corpus:
        for k, s, e in idx[files[p]]:
            if k in want_keys:
                cand[k].append((p, s, e))
    need = collections.defaultdict(set)
    for lst in cand.values():
        for p, s, e in lst:
            need[p].add(s)
    ptexts = cat_blobs(repo, [files[p] for p in need])
    bodies = {}
    for p, starts in need.items():
        for k, s, e, body in units_of(ptexts[files[p]].decode("utf-8", "replace"), langs[p], starts):
            bodies[(p, s)] = body
    pairs = []
    for p, s, e, key, body in new_units:
        for q, t, f in cand.get(key, ()):
            if (q, t) == (p, s) or (q, t) not in bodies:
                continue
            ob = bodies[(q, t)]
            if len(ob) != len(body) or ob[0][0] != body[0][0]:
                continue
            pat, h = lgg([body, ob])
            const = sum(1 for r in pat for x in r if not x.startswith("?"))
            if h > MAXH or const < MINC:
                continue
            pairs.append(dict(save=const - 2 * h, holes=h, const=const, added=[p, s, e],
                              other=[q, t, f], other_added=q in added and t in added[q],
                              pattern=[" ".join(r) for r in pat]))
    # keep maximal pairs: drop a pair nested inside a larger one between the same files
    pairs.sort(key=lambda d: (-(d["added"][2] - d["added"][1]), -d["save"]))
    kept = []
    for d in pairs:
        (p, s, e), (q, t, f) = d["added"], d["other"]
        if any(k["added"][0] == p and k["other"][0] == q and k["added"][1] <= s and e <= k["added"][2]
               and k["other"][1] <= t and f <= k["other"][2] for k in kept):
            continue
        kept.append(d)
    # cluster: an added unit with all its partners
    clusters = collections.OrderedDict()
    for d in sorted(kept, key=lambda d: -d["save"]):
        c = clusters.setdefault(tuple(d["added"]), dict(added=d["added"], save=d["save"], holes=d["holes"],
                                                         pattern=d["pattern"], others=[]))
        c["others"].append(d["other"])
    out = [c for c in clusters.values() if c["save"] >= min_save]
    out.sort(key=lambda c: -c["save"])
    return out


def diff_main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="au.py --diff")
    ap.add_argument("base")
    ap.add_argument("head")
    ap.add_argument("--min-save", type=int, default=50)
    ap.add_argument("--exclude", default=DEFAULT_EXCLUDE)
    ap.add_argument("--scope", choices=("full", "near"), default="full")
    ap.add_argument("--repo", default=".")
    ap.add_argument("--cache")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--limit", type=int, default=20)
    try:
        a = ap.parse_args(argv)
    except SystemExit:
        return 2
    try:
        res = diff_mode(a.repo, a.base, a.head, a.min_save, a.scope, a.cache, exclude=a.exclude)
    except (GitError, sqlite3.Error, OSError) as e:
        print("au.py: %s" % e, file=sys.stderr)
        return 2
    if a.json:
        print(json.dumps(res, indent=1))
    else:
        for c in res[:a.limit]:
            p, s, e = c["added"]
            others = ", ".join("%s:%d-%d" % tuple(o) for o in c["others"][:4])
            more = " (+%d more)" % (len(c["others"]) - 4) if len(c["others"]) > 4 else ""
            print("## save=%d holes=%d added %s:%d-%d duplicates %s%s" % (c["save"], c["holes"], p, s, e, others, more))
            for r in c["pattern"][:12]:
                print("   ", r)
            if len(c["pattern"]) > 12:
                print("    ...")
    return 1 if res else 0


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--diff":
        sys.exit(diff_main(sys.argv[2:]))
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    main(sys.argv[2:])
