#!/usr/bin/env python3
"""Print a compact starting context for a task, so an agent searches and reads less.

usage: context-pack.py [--goal NAME] [--names N1,N2] [--max-lines N] [SCOPE...]

SCOPE entries are files, directories or globs under the checkout. The pack lists the target
@[goal] declaration, where the names it mentions are defined and used, an outline of every
scope file (declarations with line numbers), the modules that import the scope, and recent
commits on it. Nothing is elaborated: it reads the source tree only.
"""
import argparse
import glob
import os
import re
import subprocess
import sys

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s(:{\[]+)")
NS = re.compile(r"^\s*namespace\s+(\S+)")
END = re.compile(r"^\s*end\s+(\S+)")
IDENT = re.compile(r"[A-Za-z_][\w'.]*[\w']")
SKIP = {"theorem", "lemma", "def", "goal", "Prop", "Type", "fun", "let", "have", "show", "then", "else",
        "with", "match", "by", "from", "forall", "exists", "true", "false", "True", "False", "Nat", "Int",
        "Bool", "List", "Option", "String", "some", "none", "and", "not", "Solidity", "Goals"}


def git_root():
    out = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True)
    return out.stdout.strip() or os.getcwd()


def lean_files(root):
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=root, capture_output=True, text=True)
    return [f for f in out.stdout.split() if not f.startswith(".lake/")]


def outline(root, path):
    """[(line, kind, full name)] with namespaces applied."""
    rows, ns = [], []
    try:
        lines = open(os.path.join(root, path), encoding="utf-8", errors="replace").read().split("\n")
    except OSError:
        return rows
    for i, line in enumerate(lines, 1):
        m = NS.match(line)
        if m:
            ns.append(m.group(1))
            continue
        m = END.match(line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(2)
            full = name if name.startswith("_root_.") else ".".join(ns + [name])
            rows.append((i, m.group(1), full.replace("_root_.", "")))
    return rows


def expand(root, scope):
    files = []
    for s in scope:
        p = os.path.join(root, s)
        if os.path.isdir(p):
            hits = glob.glob(os.path.join(p, "**", "*.lean"), recursive=True)
        else:
            hits = glob.glob(p, recursive=True)
        files += [os.path.relpath(h, root) for h in hits if h.endswith(".lean")]
    return sorted(set(files))


def module_of(path):
    """Bridge/ is its own Lake package root: Bridge/SolidityBridge/X.lean is module SolidityBridge.X."""
    if path.startswith("Bridge/"):
        path = path[len("Bridge/"):]
    return path[:-5].replace("/", ".")


def rg(root, args):
    out = subprocess.run(["rg", "--no-heading", "-n", *args], cwd=root, capture_output=True, text=True)
    return [line for line in out.stdout.split("\n") if line]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--goal", help="target @[goal] declaration (full or last component)")
    ap.add_argument("--names", default="", help="extra declaration names to locate, comma separated")
    ap.add_argument("--max-lines", type=int, default=400)
    ap.add_argument("scope", nargs="*")
    a = ap.parse_args()
    root = git_root()
    out = []
    names = [n for n in a.names.split(",") if n]

    files = lean_files(root)
    if a.goal:
        want = a.goal.split(".")
        found = False
        for f in (f for f in files if f.startswith("Solidity/Goals")):
            src = open(os.path.join(root, f), encoding="utf-8").read().split("\n")
            for ln, _, full in outline(root, f):
                parts = full.split(".")
                # a qualified request must match the declaration's full name as a suffix
                if parts[-len(want):] != want and not (len(want) == 1 and parts[-1] == want[0]):
                    continue
                i = ln - 1
                start = i
                while start > 0 and src[start - 1].strip().startswith(("@[", "/--", "--")):
                    start -= 1
                head = "\n".join(src[start:i + 1])
                if "@[goal" not in head:
                    continue
                end = i + 1
                while end < len(src) and src[end].strip() and not DECL.match(src[end]) and end - i < 40:
                    end += 1
                block = src[start:end]
                out += [f"## Goal `{full}` ({f}:{ln})", "```lean", *block, "```", ""]
                names += [t for t in IDENT.findall("\n".join(src[i:end]))
                          if t not in SKIP and t.split(".")[-1] != parts[-1] and len(t) > 3]
                found = True
                break
            if found:
                break
        if not found:
            out += [f"## Goal `{a.goal}`: no @[goal] declaration with that name in Solidity/Goals* (not stated yet)", ""]

    scope_files = expand(root, a.scope)
    seen, uniq = set(), []
    for n in names:
        if n not in seen:
            seen.add(n)
            uniq.append(n)
    uniq = uniq[:25]
    if uniq:
        out.append("## Names: definition, then up to 4 uses")
        pattern = "|".join(re.escape(n.split(".")[-1]) for n in uniq)
        defs = rg(root, ["-g", "*.lean", "-e",
                         rf"^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|partial)\s+)*"
                         rf"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+"
                         rf"(\S+\.)?({pattern})\b", "Solidity", "Bridge"])
        for n in uniq:
            last = n.split(".")[-1]
            d = [x for x in defs if re.search(rf"[\s.]{re.escape(last)}\b", x.split(":", 2)[2])]
            d = sorted(d, key=lambda x: not re.search(rf"\s{re.escape(last)}\b", x.split(":", 2)[2]))[:2]
            uses = rg(root, ["-g", "*.lean", "-w", "-m", "1", "--max-columns", "160", last, "Solidity"])
            uses = [u for u in uses if u not in d][:4]
            if not d and not uses:
                continue
            out.append(f"- `{n}`: " + ("; ".join(":".join(x.split(":", 2)[:2]) for x in d) or "no definition found"))
            out += [f"    {u[:180]}" for u in uses]
        out.append("")

    if scope_files:
        out.append("## Scope outline (line kind name)")
        for f in scope_files[:30]:
            rows = outline(root, f)
            imports = [x.split()[1] for x in open(os.path.join(root, f), encoding="utf-8", errors="replace")
                       if x.startswith("import ")]
            out.append(f"### {f} ({len(rows)} declarations; imports {', '.join(imports[:8])}"
                       f"{' …' if len(imports) > 8 else ''})")
            out += [f"  {ln} {k} {n}" for ln, k, n in rows[:60]]
            if len(rows) > 60:
                out.append(f"  … {len(rows) - 60} more")
        out.append("")
        mods = [module_of(f) for f in scope_files[:30]]
        importers = rg(root, ["-g", "*.lean", "-l", "-e",
                              r"^import (" + "|".join(re.escape(m) for m in mods) + r")\s*$", "Solidity", "Bridge"])
        importers = sorted(set(importers) - set(scope_files))
        if importers:
            out.append(f"## Imported by ({len(importers)})")
            out += [f"  {x}" for x in importers[:20]] + (["  …"] if len(importers) > 20 else [])
            out.append("")
        log = subprocess.run(["git", "log", "-6", "--format=%h %as %s", "--", *scope_files[:30]],
                             cwd=root, capture_output=True, text=True).stdout.strip()
        if log:
            out += ["## Recent commits on the scope", *[f"  {x}" for x in log.split("\n")], ""]

    if len(out) > a.max_lines:
        out = out[:a.max_lines] + [f"… cut at {a.max_lines} lines (--max-lines)"]
    print("\n".join(out) if out else "nothing to report: give --goal, --names or a scope")
    return 0


if __name__ == "__main__":
    sys.exit(main())
