#!/usr/bin/env python3
"""Declaration index: statement hashes of the built library, for checks a token scan cannot do.

DeclIndex.lean (next to this file) writes one JSON line per user-facing declaration with a
hash of its elaborated statement (binder names, binder info and universe names do not
matter). On that index:
  duplicates  theorems whose statements are equal (aliases `theorem a := b` and deprecated
              declarations are not counted); a group of k counts k-1 redundant theorems.
              Structure-field projections are not counted either.
  ratchet     the redundant count of a full index may not exceed scripts/decl-index/baseline.json
              (lower it with `ratchet --update` once duplicates are removed).
  compare     a head index of the touched modules against the master index: a new theorem
              whose statement equals an existing theorem's (a renamed copy, a requalified copy)
              fails; a changed or removed statement is listed, and fails with
              --statement-preserving. A rename (old name gone, same statement) passes.
              Deliberate cases pass with a Git trailer in base..head:
              `Review-Check: duplicates <reason>` or `Review-Check: statements <reason>`.
  gate        what scripts/coord-tools/gate.sh runs when GATE_DECL_INDEX=1:
              checkpoint|full: index Solidity at HEAD into the cache (incrementally from a
              cached first-parent ancestor: only changed modules are re-indexed; a full run
              after a toolchain or lakefile change or over 400 changed modules), then the ratchet;
              touched: index the touched modules, compare with the cached index of
              merge-base(GATE_BASE, HEAD) (written by a checkpoint gate on that commit, e.g.
              the factory's master check); with no cached index it says SKIP and passes.
              GATE_STATEMENT_PRESERVING=1 adds --statement-preserving.
Cache: $DECL_INDEX_CACHE, else <git common dir>/decl-index (shared by worktrees), one
<sha>.jsonl per indexed commit (about 45 MB), the newest 10 kept.

Usage: decl_index.py dump [--out FILE] [MODULE...]       (default module Solidity)
       decl_index.py duplicates INDEX [--top N]
       decl_index.py ratchet INDEX [--update]
       decl_index.py compare --base-index B --head-index H [--base REV] [--statement-preserving]
       decl_index.py gate touched|checkpoint|full
Exit 0 pass, 1 policy failure, 2 setup error.
"""
import argparse, json, os, pathlib, subprocess, sys, tempfile
from collections import defaultdict

sys.dont_write_bytecode = True
HERE = pathlib.Path(__file__).resolve().parent
SCRIPT = HERE / "DeclIndex.lean"
BASELINE = HERE / "baseline.json"
KEEP = 10
INCREMENTAL_DEPTH, INCREMENTAL_MODULES = 50, 400


class SetupError(Exception):
    pass


def git(*args, cwd=None):
    r = subprocess.run(["git", *args], capture_output=True, text=True, cwd=cwd)
    if r.returncode: raise SetupError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout.strip()


def root():
    return pathlib.Path(git("rev-parse", "--show-toplevel"))


# ---- Index ------------------------------------------------------------------------------------

def artifacts():
    """Every Lake artifact cache directory that may hold this toolchain's oleans. Lake's cache
    location depends on the host (LAKE_CACHE_DIR, the XDG cache, ~/.cache/lake or the elan
    toolchain), so all existing candidates are searched rather than one guess: on the
    coordinator host the guess missed the cache Lake had built into, nothing was linked for a
    module new on the lane, and Lean failed on the missing MemoryStructDefaultPlan.olean."""
    cands = []
    if os.environ.get("LAKE_CACHE_DIR"): cands.append(pathlib.Path(os.environ["LAKE_CACHE_DIR"]))
    xdg = os.environ.get("XDG_CACHE_HOME")
    if xdg: cands.append(pathlib.Path(xdg) / "lake")
    cands.append(pathlib.Path.home() / ".cache/lake")
    try: r = subprocess.run(["elan", "which", "lean"], capture_output=True, text=True)
    except OSError: r = None
    if r is not None and not r.returncode and r.stdout.strip():
        cands.append(pathlib.Path(r.stdout.strip()).parent.parent / "lake/cache")
    out = []
    for c in cands:
        a = (c / "artifacts").resolve()
        if a.is_dir() and a not in out: out.append(a)
    return out


def import_closure(top, modules):
    """`modules` and every module of this package they import, transitively, read from the
    `import` lines of the sources under `top` (modules without a source here, such as Lean's
    own, are left out). dc4: link_build checked only the touched modules, so a transitive
    import whose olean was not linked (MemoryStructDefaultPlan under b2) surfaced as Lean's
    missing object file instead of a setup error."""
    seen, todo = set(), list(modules)
    while todo:
        m = todo.pop()
        if m in seen: continue
        f = top / (m.replace(".", "/") + ".lean")
        if not f.is_file(): continue
        seen.add(m)
        try: text = f.read_text()
        except OSError: continue
        for line in text.splitlines():
            w = line.split()
            if not w or w[0] in ("module", "prelude") or w[0].startswith("--"): continue
            if w[0] == "public" and len(w) > 1 and w[1] == "import": w = w[1:]
            if w[0] == "meta" and len(w) > 1 and w[1] == "import": w = w[1:]
            if w[0] != "import": break
            todo.extend(x for x in w[1:] if x not in ("all",) and not x.startswith("--"))
    return seen


def trace_hashes(o):
    """Every artifact hash in a trace's `outputs`: a string, a list, or a dict of them, with
    any `.olean`-style extension dropped (Lake versions differ in the shape)."""
    if isinstance(o, str): return [o.split(".", 1)[0]]
    if isinstance(o, dict): o = list(o.values())
    if isinstance(o, list): return [h for x in o for h in trace_hashes(x)]
    return []


def link_build(top, lib, need=()):
    """A LEAN_PATH directory of the oleans the traces name. With enableArtifactCache a fetched
    module's olean is only in Lake's cache, and a stale .lake/build olean can outlive a later
    fetch (restore-lake-artifacts never overwrites), so the trace decides; a module whose
    artifact is not cached falls back to its .lake/build file. Only existing files are linked
    (a dangling link shadows Lake's own path), and a module of `need` left without an olean is a
    setup error naming the searched caches: an unlinked module under lib/Solidity is reported
    by Lean as a missing object file."""
    build = top / ".lake/build/lib/lean"
    if not build.is_dir(): raise SetupError(f"{build}: no build (run lake build first)")
    arts = artifacts() or []
    names = defaultdict(list)
    for art in arts:
        for n in os.listdir(art): names[n.split(".", 1)[0]].append((art, n))
    linked, done = 0, set()
    for t in build.rglob("*.trace"):
        stem = t.with_suffix("")
        if stem.suffix in (".olean", ".ilean", ".c"): stem = stem.with_suffix("")
        rel = stem.relative_to(build)
        if ".".join(rel.parts) in done: continue
        try:
            outs = json.loads(t.read_text()).get("outputs", {})
            o = outs.get("o", outs) if isinstance(outs, dict) else outs
        except (OSError, ValueError, AttributeError): o = None
        srcs, exts = [], set()
        for h in trace_hashes(o):
            for art, n in names.get(h, []):
                ext = n.split(".", 1)[1]
                if ext.startswith("olean") and ext not in exts and (art / n).is_file():
                    srcs.append((art / n, ext)); exts.add(ext)
        if "olean" not in exts:
            srcs += [(p, p.name[len(stem.name) + 1:]) for p in stem.parent.glob(stem.name + ".olean*")
                     if p.is_file() and p.name[len(stem.name) + 1:] not in exts]
        for src, ext in srcs:
            dst = lib / rel.parent / f"{stem.name}.{ext}"
            dst.parent.mkdir(parents=True, exist_ok=True)
            if os.path.lexists(dst): continue
            os.symlink(src, dst); linked += 1
        if any(e == "olean" for _, e in srcs): done.add(".".join(rel.parts))
    if not linked: raise SetupError(f"{build}: no oleans found")
    missing = sorted(import_closure(top, need) | set(need)) if need else []
    missing = [m for m in missing if m not in done]
    if missing:
        raise SetupError("no olean for %s in %s or caches %s (set LAKE_CACHE_DIR to Lake's cache)"
                         % (", ".join(missing), build, [str(a) for a in arts] or "none found"))


def lake_build(top, modules):
    """Build `modules` and their import closure at the checked-out tree, so the traces
    link_build reads name the oleans of this commit. Without it a touched module's index came
    from whatever an earlier build or a coordinator overlay left, and a declaration new on the
    lane (MemoryStructDefaultPlan at b2) was missing."""
    r = subprocess.run(["lake", "build", *modules], cwd=top, capture_output=True, text=True)
    if r.returncode:
        raise SetupError("lake build %s failed (exit %d): %s"
                         % (" ".join(modules), r.returncode, (r.stdout + r.stderr).strip()[-1500:]))


def dump(out, modules):
    """Index `modules` (imported together) into `out`; SetupError unless Lake built them and
    Lean finished."""
    top = root()
    text = SCRIPT.read_text()
    if text.count("\nimport Solidity\n") != 1: raise SetupError(f"{SCRIPT}: no single `import Solidity` line")
    text = text.replace("\nimport Solidity\n", "\n" + "".join(f"import {m}\n" for m in modules), 1)
    out = pathlib.Path(out).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="decl-index.") as d:
        src, part = pathlib.Path(d) / "DeclIndexRun.lean", out.with_name(out.name + f".{os.getpid()}.part")
        src.write_text(text)
        lake_build(top, modules)
        lib = pathlib.Path(d) / "lib"; link_build(top, lib, [m for m in modules if m != "Solidity"])
        env = dict(os.environ, DECLINDEX_OUT=str(part), LEAN_NUM_THREADS="1", DECLINDEX_LIB=str(lib))
        env.pop("DECLINDEX_LOCAL", None)
        r = subprocess.run(["lake", "env", "sh", "-c", 'LEAN_PATH="$DECLINDEX_LIB:$LEAN_PATH" exec lean --tstack=131072 "$1"',
                            "sh", str(src)], cwd=top, env=env, capture_output=True, text=True)
        if r.returncode or "decls=" not in r.stdout or not part.is_file():
            part.unlink(missing_ok=True)
            raise SetupError("DeclIndex failed (exit %d): %s" % (r.returncode, (r.stdout + r.stderr).strip()[-1500:]))
        os.replace(part, out)
    return r.stdout.strip().splitlines()[-1]


def load(path):
    rows = []
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip(): continue
            try: rows.append(json.loads(line))
            except ValueError as e: raise SetupError(f"{path}:{n}: not JSON: {e}")
    if not rows: raise SetupError(f"{path}: empty index")
    return rows


def countable(r):
    return r["kind"] == "theorem" and not r.get("aliasOf") and not r.get("deprecated") and not r.get("proj")


def key(r):
    """Statement key across runs: Expr.hash is 32-bit and collides on numerals, so the shape
    hash, constant count and literal-set hash join it."""
    return (r["typeHash"], r["shapeHash"], r["typeConsts"], r.get("litHash"))


# ---- Duplicates and ratchet -------------------------------------------------------------------

def duplicate_groups(rows):
    groups = defaultdict(list)
    for r in rows:
        if countable(r): groups[key(r)].append(r)
    return sorted((g for g in groups.values() if len(g) > 1), key=lambda g: (-len(g), g[0]["name"]))


def redundant(groups):
    return sum(len(g) - 1 for g in groups)


def show(groups, top):
    for g in groups[:top]:
        print(f"  {len(g)}x " + ", ".join(f"{r['name']} ({r['module']})" for r in g[:4]) + (" …" if len(g) > 4 else ""))


def read_baseline():
    try:
        b = json.loads(BASELINE.read_text())
        v = b["duplicate_theorems"]
        if not isinstance(v, int) or isinstance(v, bool) or v < 0: raise ValueError("not a count")
        return b
    except (OSError, ValueError, KeyError, TypeError) as e:
        raise SetupError(f"{BASELINE}: {e}")


def ratchet(index, update=False, top=8):
    groups = duplicate_groups(load(index)); n = redundant(groups)
    b = read_baseline(); limit = b["duplicate_theorems"]
    if update:
        if n < limit:
            b["duplicate_theorems"] = n
            BASELINE.write_text(json.dumps(b, indent=1) + "\n"); print(f"lowered duplicate_theorems: {limit} -> {n}")
        return 0
    if n <= limit:
        print(f"ok duplicate_theorems: {n} (baseline {limit})" +
              ("; lower it with `decl_index.py ratchet --update`" if n < limit else ""))
        return 0
    print(f"FAIL duplicate_theorems: {n}, over the baseline {limit}: reuse the existing theorem "
          f"(or state the new one as `theorem new := old`). Largest groups:")
    show(groups, top)
    return 1


# Keep in sync with the exclusions for Solidity.lean in register.sh. These modules
# belong to other libraries (or no library), so the Solidity build need not build them.
def indexed_module(path):
    if not path.startswith("Solidity/") or not path.endswith(".lean"):
        return None
    module = path[:-5].replace("/", ".")
    excluded = ("Solidity.Scratch", "Solidity.Corpus", "Solidity.TestSuite",
                "Solidity.Solkey.TestSuite", "Solidity.Examples")
    if any(module == prefix or module.startswith(prefix + ".") for prefix in excluded):
        return None
    return module


# ---- Base/head comparison ---------------------------------------------------------------------

def touched_modules(base, head="HEAD"):
    """Solidity.* modules of the .lean files added or modified in merge-base(base, head)..head."""
    merge = git("merge-base", base, head)
    out = git("diff", "--name-only", "--diff-filter=AMR", merge, head, "--")
    mods = []
    for p in out.splitlines():
        m = indexed_module(p)
        if m: mods.append(m)
    return merge, sorted(mods)


def waivers(merge, head="HEAD"):
    text = git("log", "--format=%(trailers:key=Review-Check,valueonly)", f"{merge}..{head}")
    return {line.split()[0] for line in text.splitlines() if len(line.split()) > 1}


def compare(base_rows, head_rows, touched, statement_preserving=False, waived=frozenset()):
    """(ok, report lines)."""
    touched = set(touched)
    base = {r["name"]: r for r in base_rows}
    head = {r["name"]: r for r in head_rows}
    by_hash = defaultdict(list)
    for r in base_rows:
        if countable(r): by_hash[key(r)].append(r["name"])
    gone = {n for n, r in base.items() if r["module"] in touched and n not in head}
    changed, dups, renames = [], [], []
    fresh = defaultdict(list)
    for r in head_rows:
        if r["module"] not in touched: continue
        old = base.get(r["name"])
        if old is not None:
            if key(old) != key(r): changed.append(r)
            continue
        if not countable(r): continue
        fresh[key(r)].append(r)
        same = by_hash.get(key(r), [])
        live = [n for n in same if n not in gone]
        if live: dups.append((r, live))
        elif same: renames.append((r, same))
    for g in fresh.values():
        if len(g) > 1:
            for r in g[1:]: dups.append((r, [g[0]["name"]]))
    rep, ok = [], True
    for r, olds in renames: rep.append(f"rename {olds[0]} -> {r['name']} ({r['module']})")
    for r in changed: rep.append(f"statement changed: {r['name']} ({r['module']})")
    for n in sorted(gone): rep.append(f"removed: {n} ({base[n]['module']})")
    if dups:
        waived_d = "duplicates" in waived
        ok = ok and waived_d
        rep.append(("waived (Review-Check: duplicates) " if waived_d else "FAIL ") +
                   f"{len(dups)} new theorem(s) restate an existing statement; reuse it or write `theorem new := old`:")
        rep += [f"  {r['name']} ({r['module']}) = {', '.join(olds[:3])}" for r, olds in dups]
    if statement_preserving and (changed or gone):
        waived_s = "statements" in waived
        ok = ok and waived_s
        rep.append(("waived (Review-Check: statements) " if waived_s else "FAIL ") +
                   f"statement-preserving change alters {len(changed)} and removes {len(gone)} statement(s)")
    rep.append(f"{'ok' if ok else 'FAIL'} decl-index: {len(touched)} touched module(s), {len(dups)} new duplicate(s), "
               f"{len(changed)} changed, {len(gone)} removed, {len(renames)} renamed")
    return ok, rep


# ---- Gate -------------------------------------------------------------------------------------

def cache_dir():
    d = os.environ.get("DECL_INDEX_CACHE")
    if not d:
        d = os.path.join(os.path.abspath(git("rev-parse", "--git-common-dir")), "decl-index")
    os.makedirs(d, exist_ok=True)
    return pathlib.Path(d)


def prune(d):
    files = sorted(d.glob("*.jsonl"), key=lambda p: p.stat().st_mtime, reverse=True)
    for p in files[KEEP:]: p.unlink(missing_ok=True)


def changed_modules(old, new):
    """(changed or added Solidity.* modules that exist at `new`, every touched module name), or
    None when a Lean input outside Solidity/ changed (toolchain, lakefile)."""
    out = git("diff", "--name-status", "--no-renames", old, new, "--")
    exist, all_ = set(), set()
    for line in out.splitlines():
        status, path = line.split("\t", 1)
        if path in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"): return None
        m = indexed_module(path)
        if m:
            all_.add(m)
            if status != "D": exist.add(m)
    return sorted(exist), all_


def index_commit(d, head):
    """The cached full index of `head`: incremental from the newest cached first-parent ancestor
    (re-indexing only changed modules; a statement only names constants, so other modules keep
    their rows), else a full run."""
    out = d / f"{head}.jsonl"
    if out.is_file(): return out
    for prev in git("rev-list", "--first-parent", "-n", str(INCREMENTAL_DEPTH), head).splitlines()[1:]:
        old = d / f"{prev}.jsonl"
        if not old.is_file(): continue
        diff = changed_modules(prev, head)
        if diff is None or len(diff[0]) > INCREMENTAL_MODULES: break
        exist, touched = diff
        rows = [r for r in load(old) if r["module"] not in touched]
        with tempfile.TemporaryDirectory(prefix="decl-index-inc.") as t:
            if exist:
                part = pathlib.Path(t) / "part.jsonl"
                print(dump(part, exist))
                rows += [r for r in load(part) if r["module"] in set(exist)]
            tmp = out.with_name(out.name + f".{os.getpid()}.part")
            tmp.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows))
            os.replace(tmp, out)
        print(f"incremental index from {prev[:12]}: {len(exist)} module(s) re-indexed")
        return out
    print(dump(out, ["Solidity"]))
    return out


def gate(mode):
    d = cache_dir(); head = git("rev-parse", "HEAD")
    if mode in ("checkpoint", "full"):
        out = index_commit(d, head)
        prune(d)
        return ratchet(out)
    merge, mods = touched_modules(os.environ.get("GATE_BASE") or "origin/master")
    existing = [m for m in mods if (root() / (m.replace(".", "/") + ".lean")).is_file()]
    if not existing:
        print("ok decl-index: no touched Solidity module"); return 0
    base_index = d / f"{merge}.jsonl"
    if not base_index.is_file():
        print(f"SKIP decl-index: no cached index for {merge[:12]} (a checkpoint gate on that commit writes it)")
        return 0
    with tempfile.TemporaryDirectory(prefix="decl-index-head.") as t:
        hp = pathlib.Path(t) / "head.jsonl"
        print(dump(hp, existing))
        ok, rep = compare(load(base_index), load(hp), existing,
                          os.environ.get("GATE_STATEMENT_PRESERVING") == "1", waivers(merge))
    print("\n".join(rep))
    return 0 if ok else 1


def main(argv):
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("dump"); s.add_argument("--out", default="decls.jsonl"); s.add_argument("modules", nargs="*")
    s = sub.add_parser("duplicates"); s.add_argument("index"); s.add_argument("--top", type=int, default=20)
    s = sub.add_parser("ratchet"); s.add_argument("index"); s.add_argument("--update", action="store_true")
    s = sub.add_parser("compare"); s.add_argument("--base-index", required=True); s.add_argument("--head-index", required=True)
    s.add_argument("--base", default="origin/master"); s.add_argument("--statement-preserving", action="store_true")
    s = sub.add_parser("gate"); s.add_argument("mode", choices=["touched", "checkpoint", "full"])
    a = p.parse_args(argv)
    try:
        if a.cmd == "dump":
            print(dump(a.out, a.modules or ["Solidity"])); return 0
        if a.cmd == "duplicates":
            g = duplicate_groups(load(a.index))
            print(f"{len(g)} groups, {redundant(g)} redundant theorems"); show(g, a.top); return 0
        if a.cmd == "ratchet":
            return ratchet(a.index, a.update)
        if a.cmd == "compare":
            merge, mods = touched_modules(a.base)
            ok, rep = compare(load(a.base_index), load(a.head_index), mods, a.statement_preserving, waivers(merge))
            print("\n".join(rep)); return 0 if ok else 1
        return gate(a.mode)
    except SetupError as e:
        print(f"decl-index: setup error: {e}", file=sys.stderr); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
