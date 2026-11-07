#!/usr/bin/env python3
"""fragments.py [--check | --resolve [--lane NAME] [--ours-lane NAME] | --force]

The shared bookkeeping files every lane appends to are generated from
per-lane fragments (`docs/parallelism.md`, "Shared registries"):

  combined file                   fragments
  docs/module-map.md              docs/module-map.d/*.md
  docs/module-map/<area>.md       docs/module-map/<area>.d/*.md
  docs/README.md                  docs/README.d/**/*.md
  TERRA-TODO.md                   TERRA-TODO.d/*.md
  scripts/g07-axiom-pins.json     scripts/g07-axiom-pins.d/<lean path>.json

A Markdown file is a marker line plus its fragments concatenated, ordered by
path component (bytewise: `00-base.md` first, lane names next, `~tail.md`
last; a subdirectory is a slot sorted by its name).  The pins inventory is the
union of its fragments, one per Lean file (the file's pins, its keys
`<file>.lean:<name>`), sorted and printed as `check-axiom-pins.mjs --write`
prints it; JSON has no comments, so it carries no marker.

  fragments.sh            rewrite every combined file that differs; refuse
                          (exit 1) when a combined file holds lines no
                          fragment here or at HEAD produced (a direct edit)
                          unless --force drops them
  fragments.sh --check    write nothing; exit 1 listing stale combined files
  fragments.sh --resolve  after a merge (MERGE_HEAD, or HEAD a merge commit):
                          move each side's direct edits of a combined file
                          into fragments (the side's lane name), regenerate
                          the combined files and the library roots, stage
                          them; exit 1 if other conflicts remain

Exit 0 = up to date (or rewritten / resolved), 1 = stale, refused or
conflicts left, 2 = invalid input or another error.
"""
import difflib, json, os, pathlib, re, subprocess, sys

FIXED = [("docs/module-map.md", "docs/module-map.d", "md"),
         ("docs/README.md", "docs/README.d", "md"),
         ("TERRA-TODO.md", "TERRA-TODO.d", "md"),
         ("scripts/g07-axiom-pins.json", "scripts/g07-axiom-pins.d", "json")]
AREAS = "docs/module-map"
ROOTS = ["Solidity.lean", "SolidityExamples.lean", "Bridge/SolidityBridge.lean"]
JS = r"""let s="";process.stdin.setEncoding("utf8");process.stdin.on("data",c=>s+=c).on("end",()=>{
const m=JSON.parse(s),o={};for(const [p,d] of Object.entries(m)){
o[p]=JSON.stringify(Object.fromEntries(Object.entries(d).sort(([a],[b])=>a.localeCompare(b))),null,1)+"\n";}
process.stdout.write(JSON.stringify(o));});"""


class Error(Exception): pass


def git(*a, check=True, inp=None):
    r = subprocess.run(["git", *a], capture_output=True, input=inp)
    if check and r.returncode: raise Error(f"git {' '.join(a)}: {r.stderr.decode()[-300:]}")
    return r.stdout


def marker(d):
    return f"<!-- Generated from {d}/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->\n"


def unmark(text, d):
    m = marker(d)
    return text[len(m):] if text.startswith(m) else text


def canon(dicts):
    """{path: dict} -> {path: canonical JSON text}, sorted as check-axiom-pins.mjs sorts."""
    if not dicts: return {}
    r = subprocess.run(["node", "-e", JS], input=json.dumps(dicts).encode(), capture_output=True)
    if r.returncode: raise Error("node: " + r.stderr.decode()[-300:])
    return json.loads(r.stdout)


class Tree:
    """The working tree (rev None) or a commit's tree."""
    def __init__(self, rev=None):
        self.rev = rev; self.cache = {}
        if rev is None:
            out = git("ls-files", "-co", "--exclude-standard", "-z").decode().split("\0")
            self.files = {f for f in out if f and os.path.isfile(f)}
        else:
            out = git("ls-tree", "-r", "-z", "--name-only", rev).decode().split("\0")
            self.files = {f for f in out if f}

    def has_dir(self, d): return any(f.startswith(d + "/") for f in self.files)

    def under(self, d): return [f for f in self.files if f.startswith(d + "/")]

    def read(self, p):
        if p not in self.files: return None
        if p not in self.cache:
            if self.rev is None: self.cache[p] = pathlib.Path(p).read_bytes().decode()
            else: self.prefetch([p])
        return self.cache[p]

    def prefetch(self, paths):
        if self.rev is None: return
        want = [p for p in paths if p in self.files and p not in self.cache]
        if not want: return
        out = git("cat-file", "--batch", inp="".join(f"{self.rev}:{p}\n" for p in want).encode())
        i = 0
        for p in want:
            nl = out.index(b"\n", i); size = int(out[i:nl].split()[2])
            self.cache[p] = out[nl + 1:nl + 1 + size].decode(); i = nl + 1 + size + 1


def specs(t):
    out = [(c, d, k) for c, d, k in FIXED if t.has_dir(d)]
    areas = sorted({f.split("/")[2] for f in t.files if f.startswith(AREAS + "/") and f.count("/") >= 3})
    out += [(f"{AREAS}/{a[:-2]}.md", f"{AREAS}/{a}", "md") for a in areas if a.endswith(".d")]
    return out


def ordered(t, d, kind, errors):
    ext = ".md" if kind == "md" else ".json"
    fs = t.under(d)
    for f in fs:
        if not f.endswith(ext): errors.append(f"{f}: not a {ext} fragment")
    return sorted((f for f in fs if f.endswith(ext)), key=lambda f: tuple(f[len(d) + 1:].split("/")))


def pins_file(key):
    i = key.find(".lean:")
    return key[:i] + ".lean" if i > 0 else None


def frag_of(d, key): return f"{d}/{pins_file(key)[:-len('.lean')]}.json"


def json_parts(t, d, errors):
    """{fragment path: dict} of a pins fragment directory."""
    fs = ordered(t, d, "json", errors); t.prefetch(fs); out = {}
    for f in fs:
        try: obj = json.loads(t.read(f))
        except ValueError as e: errors.append(f"{f}: {e}"); continue
        if not isinstance(obj, dict): errors.append(f"{f}: not an object"); continue
        for k, v in obj.items():
            if pins_file(k) is None or frag_of(d, k) != f: errors.append(f"{f}: key {k} belongs in {frag_of(d, k) if pins_file(k) else '?'}")
            if not (isinstance(v, list) and all(isinstance(x, str) for x in v)): errors.append(f"{f}: {k} is not a list of axiom names")
        out[f] = obj
    return out


def generate(t, c, d, kind, errors):
    if kind == "md":
        fs = ordered(t, d, "md", errors); t.prefetch(fs); parts = []
        for f in fs:
            s = t.read(f)
            if s and not s.endswith("\n"): errors.append(f"{f}: does not end with a newline")
            parts.append(s)
        return marker(d) + "".join(parts)
    merged = {}
    for obj in json_parts(t, d, errors).values(): merged.update(obj)
    return canon({"x": merged})["x"]


def lines(s): return s.splitlines(keepends=True)


def direct_md(cur, gen_now, gen_head):
    """Lines of cur that neither the current fragments nor HEAD's produce."""
    a, b = lines(gen_now), lines(cur); known = set(lines(gen_head))
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag in ("insert", "replace"): out += [l for l in b[j1:j2] if l.strip() and l not in known]
    return out


def direct_json(cur, gen_now, gen_head):
    return [k for k, v in cur.items() if gen_now.get(k) != v and gen_head.get(k) != v]


def write_mode(check, force):
    w = Tree(); errors = []; stale = 0; refused = 0
    head = Tree("HEAD") if git("rev-parse", "-q", "--verify", "HEAD", check=False) else None
    sp = specs(w)
    have = {c for c, _, _ in sp}
    for f in sorted(w.files):
        if f.startswith(AREAS + "/") and f.count("/") == 2 and f.endswith(".md") and f not in have:
            errors.append(f"{f}: an area file without fragments; move it to {f[:-3]}.d/<lane>.md")
    out = {}
    for c, d, kind in sp:
        want = generate(w, c, d, kind, errors); have_text = w.read(c)
        if have_text == want: continue
        stale = 1
        if check:
            if have_text is None: print(f"{c}: missing (fragments in {d}/)")
            else:
                diff = list(difflib.unified_diff(lines(have_text), lines(want), c, f"{c} (from {d}/)", n=0))
                print(f"{c}: differs from its fragments in {d}/ ({sum(1 for l in diff if l[:1] in '+-') - 2} lines)")
                for l in diff[2:14]: print("  " + l.rstrip("\n")[:160])
            continue
        if have_text is not None and not force and head is not None and head.has_dir(d):
            hgen = generate(head, c, d, kind, [])
            if kind == "md": extra = direct_md(unmark(have_text, d), unmark(want, d), unmark(hgen, d))
            else:
                try: extra = direct_json(json.loads(have_text), json.loads(want), json.loads(hgen))
                except ValueError: extra = ["(the file is not valid JSON)"]
            if extra:
                refused = 1
                print(f"{c}: {len(extra)} line(s) no fragment produces (a direct edit or a union merge); "
                      f"move them into a fragment under {d}/, run --resolve after a merge, or --force to drop them:")
                for l in extra[:10]: print("  " + l.rstrip("\n")[:160])
                continue
        out[c] = want
    if errors:
        for e in errors: print("fragments: " + e, file=sys.stderr)
        return 2
    for c, s in out.items(): pathlib.Path(c).parent.mkdir(parents=True, exist_ok=True); pathlib.Path(c).write_bytes(s.encode())
    if check and stale: print("fragments: stale combined files; run scripts/coord-tools/fragments.sh", file=sys.stderr)
    return 1 if (check and stale) or refused else 0


def lane_name(s, fallback):
    s = re.sub(r"[^a-z0-9-]+", "-", (s or "").lower()).strip("-")
    if not s: s = fallback
    return s if s[:1].isalpha() else "lane-" + s


def merge_label(text):
    m = re.match(r"Merge (?:branch |remote-tracking branch |commit |ref |tag )?'?([^'\s]+)'?", text or "")
    return m.group(1).rstrip("/").split("/")[-1] if m else None


def resolve(lane, ours_lane):
    gd = pathlib.Path(git("rev-parse", "--git-dir").decode().strip())
    if (gd / "MERGE_HEAD").exists():
        ours = git("rev-parse", "HEAD").decode().strip()
        mh = (gd / "MERGE_HEAD").read_text().split()
        if len(mh) != 1: raise Error("--resolve handles a two-parent merge, not an octopus merge")
        theirs = mh[0]
        msg = (gd / "MERGE_MSG").read_text() if (gd / "MERGE_MSG").exists() else ""
    else:
        ps = git("rev-list", "--parents", "-n1", "HEAD").decode().split()
        if len(ps) != 3:
            raise Error("--resolve needs a two-parent merge in progress or merge commit at HEAD; "
                        "after a rebase or fast-forward run fragments.sh and move refused lines into a fragment")
        ours, theirs = ps[1], ps[2]; msg = git("log", "-1", "--format=%s", "HEAD").decode()
    base = git("merge-base", ours, theirs, check=False).decode().split()
    if not base: raise Error("no merge base")
    lane = lane_name(lane or merge_label(msg), "lane-" + theirs[:8])
    branch = git("symbolic-ref", "-q", "--short", "HEAD", check=False).decode().strip()
    ours_lane = lane_name(ours_lane or branch.rstrip("/").split("/")[-1], "ours-" + ours[:8])
    unmerged = set(git("diff", "--name-only", "--diff-filter=U", "-z").decode().split("\0")) - {""}
    w = Tree(); sides = [(Tree(ours), ours_lane), (Tree(theirs), lane)]; tb = Tree(base[0])
    resolved, notes, left = set(), [], set()
    sp = specs(w); have = {c for c, _, _ in sp}
    # an area file a side created without fragments becomes that side's fragment
    for f in sorted(w.files | unmerged):
        if f.startswith(AREAS + "/") and f.count("/") == 2 and f.endswith(".md") and f not in have:
            if f in unmerged: notes.append(f"{f}: new area file conflicted; left"); continue
            owner = next((n for t, n in sides if f in t.files and f not in tb.files), lane)
            dst = f"{f[:-3]}.d/{owner}.md"; pathlib.Path(dst).parent.mkdir(parents=True, exist_ok=True)
            pathlib.Path(dst).write_bytes(pathlib.Path(f).read_bytes()); notes.append(f"{f}: moved into {dst}")
            sp.append((f, f[:-3] + ".d", "md")); w = Tree()
    for c, d, kind in sp:
        if any(u.startswith(d + "/") for u in unmerged):
            notes.append(f"{c}: a fragment under {d}/ is conflicted; left"); left.add(c); continue
        ok = True
        for t, name in sides:
            comb = t.read(c)
            if comb is None: continue
            own = t.has_dir(d)
            if own: gen = generate(t, c, d, kind, [])
            elif tb.has_dir(d): gen = generate(tb, c, d, kind, [])
            else: gen = tb.read(c) or ("{}\n" if kind == "json" else "")
            w = Tree()
            ok &= (apply_md if kind == "md" else apply_json)(w, c, d, unmark(gen, d), unmark(comb, d), name, notes, own)
        if not ok: left.add(c); continue
        errors = []; w = Tree(); text = generate(w, c, d, kind, errors)
        if errors: notes += errors; left.add(c); continue
        pathlib.Path(c).write_bytes(text.encode())
        git("add", "-A", "--", c, d); resolved.add(c)
    if any(r in unmerged for r in ROOTS) or os.path.isfile("scripts/coord-tools/register.sh"):
        r = subprocess.run(["bash", "scripts/coord-tools/register.sh"], capture_output=True, text=True)
        if r.returncode:
            notes.append("register.sh: " + (r.stdout + r.stderr)[-300:]); left |= {x for x in ROOTS if x in unmerged} or {"register.sh"}
        else:
            for x in ROOTS:
                if os.path.isfile(x): git("add", "--", x)
            resolved |= {x for x in ROOTS if x in unmerged}
    for n in notes: print("fragments: " + n)
    rest = sorted((unmerged - resolved) | left)
    for p in rest: print(f"fragments: still conflicted or not regenerated: {p}")
    print(f"fragments: resolved {len(resolved)} file(s) (lanes {ours_lane}, {lane}); {len(rest)} left")
    return 1 if rest else 0


def frag_lines(w, d):
    """[(path, lines)] of a Markdown fragment directory, in order."""
    return [(f, lines(w.read(f))) for f in ordered(w, d, "md", [])]


def apply_md(w, c, d, gen, comb, name, notes, own):
    """Move the lines `comb` adds to or drops from `gen` into the working fragments.

    For a side with its own fragments (`own`), its fragments are the truth: its combined
    file may be stale (not regenerated, or union-merged), so only lines no merged fragment
    has are adopted, and nothing is deleted.  For an old-style side every difference is a
    direct edit: a replaced block found once in one fragment is edited there in place,
    a deleted line found once is removed, and an inserted run goes to `<slot>/<lane>.md`.
    """
    a, b = lines(gen), lines(comb)
    frags = frag_lines(w, d); flat = [(f, i, l) for f, ls in frags for i, l in enumerate(ls)]
    present = {l for _, _, l in flat}
    dels, repl, adds = set(), {}, []
    def unique(l):
        hits = [(f, i) for f, i, x in flat if x == l]
        if len(hits) > 1: notes.append(f"{c}: {name} changed a line found {len(hits)} times; kept: {l.strip()[:80]}")
        return hits[0] if len(hits) == 1 else None
    def slot_of(i1):
        slot = d
        if i1 > 0:
            anchor = a[i1 - 1]; k = a[:i1 - 1].count(anchor)
            hits = [(f, i) for f, i, x in flat if x == anchor]
            if hits:
                f, i = hits[min(k, len(hits) - 1)]; slot = os.path.dirname(f)
                names = [g for g, _ in frags]; nxt = names.index(f) + 1
                if i == len(dict(frags)[f]) - 1 and nxt < len(names) and os.path.dirname(names[nxt]).startswith(slot + "/"):
                    slot = os.path.dirname(names[nxt])
        return slot
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == "equal": continue
        old, run = a[i1:i2], b[j1:j2]
        if own:
            run = [l for l in run if l.strip() and l not in present]
            if run: adds.append((f"{slot_of(i1)}/{name}.md", run))
            continue
        hits = [unique(l) if l.strip() else None for l in old]
        if tag == "replace" and all(h for h, l in zip(hits, old) if l.strip()) and any(hits):
            got = [h for h in hits if h]; f0 = got[0][0]; idx = [i for _, i in got]
            if all(f == f0 for f, _ in got) and idx == list(range(idx[0], idx[0] + len(idx))):
                # edit in place: the block of non-blank lines is contiguous in one fragment
                lo, hi = idx[0], idx[-1]; ls = dict(frags)[f0]
                k0 = next(k for k, l in enumerate(old) if l.strip()); k1 = max(k for k, l in enumerate(old) if l.strip())
                lo -= k0; hi += len(old) - 1 - k1
                if 0 <= lo and hi < len(ls) and ls[lo:hi + 1] == old:
                    repl[(f0, lo)] = (hi, run); dels |= {(f0, x) for x in range(lo, hi + 1)}; continue
        dels |= {h for h in hits if h}
        if tag in ("insert", "replace") and any(l.strip() for l in run):
            adds.append((f"{slot_of(i1)}/{name}.md", run))
    for f in sorted({f for f, _ in dels}):
        keep = []
        for i, l in enumerate(dict(frags)[f]):
            if (f, i) in repl: keep += repl[(f, i)][1]
            if (f, i) not in dels: keep.append(l)
        if keep: pathlib.Path(f).write_bytes("".join(keep).encode())
        else: os.remove(f)
        n = sum(1 for g, _ in dels if g == f); r = sum(1 for g, _ in repl if g == f)
        notes.append(f"{c}: {name}: " + (f"edited {r} block(s) in place in {f}" if r else f"removed {n} line(s) from {f}"))
    after = "".join(l for _, ls in frag_lines(Tree(), d) for l in ls) if dels and adds else "".join(l for _, _, l in flat)
    for f, run in adds:
        text = "".join(run)
        if not own and ("\n" + text) in ("\n" + after): continue  # the merged fragments already have this run
        p = pathlib.Path(f); old = p.read_bytes().decode() if p.is_file() else ""
        if old and not old.endswith("\n"): old += "\n"
        if not text.endswith("\n"): text += "\n"
        p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes((old + text).encode())
        notes.append(f"{c}: {name}: moved {len(run)} line(s) into {f}")
    return True


def apply_json(w, c, d, gen, comb, name, notes, own):
    try: a, b = json.loads(gen), json.loads(comb)
    except ValueError as e: notes.append(f"{c}: {name}'s file is not JSON ({e}); left"); return False
    errors = []; parts = json_parts(w, d, errors); cur = {}
    for obj in parts.values(): cur.update(obj)
    ok = True; changed = set()
    def put(k, v):
        f = frag_of(d, k); parts.setdefault(f, {})
        if v is None: parts[f].pop(k, None)
        else: parts[f][k] = v
        changed.add(f)
    for k, v in b.items():
        if a.get(k) == v or cur.get(k) == v: continue
        if own and (k in a or k in cur): continue  # its fragments are the truth; the combined file may be stale
        if k in cur and cur[k] != a.get(k): notes.append(f"{c}: {k} changed on both sides; left"); ok = False; continue
        put(k, v)
    for k in a:
        if not own and k not in b and k in cur:
            if cur[k] == a[k]: put(k, None)
            else: notes.append(f"{c}: {name} removed {k}, changed on the other side; left"); ok = False
    if not ok: return False
    texts = canon({f: parts[f] for f in changed if parts[f]})
    for f in changed:
        p = pathlib.Path(f)
        if parts[f]: p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(texts[f].encode())
        elif p.is_file(): p.unlink()
    if changed: notes.append(f"{c}: {name}: {len(changed)} pins fragment(s) updated")
    return True


def main(argv):
    opts = {"--lane": None, "--ours-lane": None}; flags = set(); i = 0
    while i < len(argv):
        x = argv[i]
        if x in opts:
            if i + 1 >= len(argv): raise Error(f"{x} needs a value")
            opts[x] = argv[i + 1]; i += 2; continue
        if x not in ("--check", "--resolve", "--force"): raise Error(f"unknown argument {x}")
        flags.add(x); i += 1
    if len(flags & {"--check", "--resolve"}) > 1: raise Error("--check and --resolve exclude each other")
    if "--resolve" in flags: return resolve(opts["--lane"], opts["--ours-lane"])
    if opts["--lane"] or opts["--ours-lane"]: raise Error("--lane needs --resolve")
    return write_mode("--check" in flags, "--force" in flags)


if __name__ == "__main__":
    try:
        os.chdir(git("rev-parse", "--show-toplevel").decode().strip())
        sys.exit(main(sys.argv[1:]))
    except Error as e:
        print("fragments: " + str(e), file=sys.stderr); sys.exit(2)
