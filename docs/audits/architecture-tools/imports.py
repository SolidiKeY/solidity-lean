#!/usr/bin/env python3
"""Import graph of the package, for docs/audits/architecture.md.

Usage: python3 -I docs/audits/architecture-tools/imports.py [areas|roots|orphans|edges|fanin]
Run from the repository root. Reads every .lean file under Solidity/, Bridge/ and
the top-level roots; prints the requested table.
"""
import os, re, sys, collections

ROOT = os.getcwd()
SRC_DIRS = ["Solidity", "Bridge"]
TOP = [f for f in os.listdir(ROOT) if f.endswith(".lean")]
IMPORT = re.compile(r"^\s*(?:public\s+|meta\s+)*import\s+(?:all\s+)?([\w.]+)", re.M)


def mod_of(path):
    rel = os.path.relpath(path, ROOT)[:-5]
    if rel.startswith("Bridge/"):
        rel = rel[len("Bridge/"):]
    return rel.replace("/", ".")


def files():
    out = [os.path.join(ROOT, f) for f in TOP]
    for d in SRC_DIRS:
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            out += [os.path.join(dp, f) for f in fs if f.endswith(".lean")]
    return out


def header(text):
    # imports sit before the first non-import, non-comment line
    m = re.search(r"^(?!\s*(import|public|meta|module|prelude|--|/-|$)).", text, re.M)
    return text[: m.start()] if m else text


def graph():
    g, size, path = {}, {}, {}
    for f in files():
        t = open(f, encoding="utf-8", errors="replace").read()
        m = mod_of(f)
        g[m] = [x for x in IMPORT.findall(header(t))]
        size[m] = t.count("\n")
        path[m] = os.path.relpath(f, ROOT)
    return g, size, path


AREAS = ["Syntax", "Semantics", "Calculus", "Typing", "Backend", "Yul", "Evm",
         "Lowering", "Frontend", "Tools", "Examples", "TestSuite", "Source",
         "Theory", "Storage", "Roadmap", "Corpus", "SolcValidation", "Language",
         "Optimizer", "Precompiles", "Hash", "SortCheck", "Counterexamples",
         "Solkey", "Stipend", "Automation"]


def area(m):
    p = m.split(".")
    if p[0] != "Solidity" or len(p) == 1:
        return "Bridge" if m in G and PATH[m].startswith("Bridge/") else "<root>:" + m
    if len(p) == 2:
        # Solidity.Syntax, Solidity.Semantics, Solidity.Yul file umbrellas
        return p[1] if p[1] in AREAS else "core-top"
    return p[1] if p[1] in AREAS else "core-top"


G, SIZE, PATH = graph()


def main(cmd):
    if cmd == "areas":
        dep = collections.Counter()
        for m, imps in G.items():
            for i in imps:
                if i in G:
                    a, b = area(m), area(i)
                    if a != b:
                        dep[(a, b)] += 1
        for (a, b), n in sorted(dep.items(), key=lambda x: (x[0][0], -x[1])):
            print(f"{a}\t->\t{b}\t{n}")
    elif cmd == "orphans":
        imported = {i for imps in G.values() for i in imps}
        for m in sorted(G):
            if m not in imported and not PATH[m].count("/") == 0:
                print(m, PATH[m], SIZE[m])
    elif cmd == "fanin":
        rev = collections.defaultdict(set)
        for m, imps in G.items():
            for i in imps:
                rev[i].add(m)
        for m in sorted(G, key=lambda m: -len(rev[m]))[:40]:
            print(len(rev[m]), m)
    elif cmd == "roots":
        # transitive closure from each top-level root
        for r in sorted(TOP):
            r = r[:-5]
            seen, st = set(), [r]
            while st:
                x = st.pop()
                if x in seen or x not in G:
                    continue
                seen.add(x)
                st += G[x]
            print(r, len(seen), sum(SIZE[x] for x in seen))
    elif cmd == "unreached":
        reach = set()
        roots = [r[:-5] for r in TOP] + ["SolidityBridge"]
        st = list(roots)
        while st:
            x = st.pop()
            if x in reach or x not in G:
                continue
            reach.add(x)
            st += G[x]
        for m in sorted(set(G) - reach):
            print(m, PATH[m], SIZE[m])
    elif cmd == "edges":
        for m, imps in sorted(G.items()):
            for i in imps:
                print(m, i)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "areas")
