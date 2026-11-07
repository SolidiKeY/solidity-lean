#!/usr/bin/env python3
"""Duplicate declaration statements across the package.

For every `theorem`/`lemma`/`def`/`abbrev` in Solidity/**.lean, take the text
from the name to the first top-level `:=` (or `where`/`|`), drop the name,
collapse whitespace, and hash it.  Groups of equal statements in different
files are printed (largest groups first), with a per-area summary.

Also: `private theorem/def X` whose bare name `X` is declared public elsewhere
with the same normalized statement ("private copies of public lemmas").

Usage (repo root): python3 -I docs/audits/architecture-tools/dup_decls.py [N]
"""
import os, re, sys, hashlib, collections

DECL = re.compile(
    r"^(?P<mods>(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)"
    r"(?P<kw>theorem|lemma|def|abbrev)\s+(?P<name>[^\s(:{\[]+)(?P<rest>.*?)(?=^\S)",
    re.M | re.S)


def statement(rest):
    # cut at the first := / where / | that is not inside brackets
    depth, i, s = 0, 0, rest
    while i < len(s):
        c = s[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0:
            if s.startswith(":=", i):
                return s[:i]
            if re.match(r"\swhere\b", s[i:i + 7]) or s.startswith("\n  |", i):
                return s[:i]
        i += 1
    return s


def norm(t):
    t = re.sub(r"--[^\n]*", "", t)
    t = re.sub(r"/-.*?-/", "", t, flags=re.S)
    return re.sub(r"\s+", " ", t).strip()


def scan():
    out = []
    for dp, _, fs in os.walk("Solidity"):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            t = open(p, encoding="utf-8", errors="replace").read()
            for m in DECL.finditer(t + "\nEND"):
                st = norm(statement(m.group("rest")))
                if len(st) < 40:  # too short to be meaningful (e.g. `: Nat`)
                    continue
                out.append((p, m.group("name"), "private" in m.group("mods"), m.group("kw"), st))
    return out


def main():
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    decls = scan()
    groups = collections.defaultdict(list)
    for d in decls:
        groups[hashlib.sha1(d[4].encode()).hexdigest()].append(d)
    multi = [g for g in groups.values() if len({x[0] for x in g}) > 1]
    print(f"declarations scanned: {len(decls)}; statement groups: {len(groups)}")
    print(f"groups repeated across >1 file: {len(multi)}; redundant copies: "
          f"{sum(len(g) - 1 for g in multi)}")
    thm = [g for g in multi if g[0][3] in ("theorem", "lemma")]
    print(f"  of which theorem groups: {len(thm)}, redundant theorem copies: {sum(len(g)-1 for g in thm)}")
    cross = collections.Counter()
    for g in multi:
        areas = sorted({x[0].split('/')[1] for x in g})
        if len(areas) > 1:
            cross[" + ".join(areas)] += 1
    print("cross-area groups by area set (top 15):")
    for k, n in cross.most_common(15):
        print(f"  {n}\t{k}")
    priv = [g for g in multi if any(x[2] for x in g) and any(not x[2] for x in g)]
    print(f"groups with a private copy of a public declaration: {len(priv)}; private copies: "
          f"{sum(sum(1 for x in g if x[2]) for g in priv)}")
    print(f"\nlargest theorem groups (top {top}):")
    for g in sorted(thm, key=lambda g: (-len(g), -len(g[0][4])))[:top]:
        print(f"[{len(g)}] {g[0][4][:150]}")
        for x in g[:4]:
            print(f"     {x[0]}  {x[1]}{' (private)' if x[2] else ''}")
    if "--priv" in sys.argv:
        for g in priv[:40]:
            print("PRIV", g[0][4][:120])
            for x in g:
                print("   ", x[0], x[1], "private" if x[2] else "public")


if __name__ == "__main__":
    main()
