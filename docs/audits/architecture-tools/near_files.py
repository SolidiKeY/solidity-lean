#!/usr/bin/env python3
"""Files that are copies of each other up to renamed identifiers.

Each Solidity/**.lean file (comments and the import header dropped) is
tokenized; every identifier is replaced by the order of its first occurrence
in the file (alpha-renaming to a canonical form), keywords and symbols kept.
Exact canonical matches are reported, then near matches by Jaccard similarity
of 10-token shingles (MinHash, 64 permutations, 16 bands of 4; candidate pairs
are verified exactly).  Only files of at least MIN tokens are compared.

Usage (repo root): python3 -I docs/audits/architecture-tools/near_files.py [threshold=0.8] [MIN=300]
"""
import os, re, sys, random, hashlib, collections

KW = set("""theorem lemma def abbrev structure inductive where with fun match by
at have show from let in if then else do return namespace section end open
variable instance class deriving private protected noncomputable import
simp rfl exact intro intros cases induction rw omega decide constructor
refine apply unfold change subst calc obtain rcases using only all_goals
Type Prop Nat Int Bool List Option True False and or not""".split())
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*|\d+|\S")


def canon(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    text = re.sub(r"^\s*import\s+\S+", " ", text, flags=re.M)
    ids, out = {}, []
    for t in TOK.findall(text):
        if t[0].isalpha() or t[0] == "_":
            if t in KW:
                out.append(t)
            else:
                out.append("v%d" % ids.setdefault(t, len(ids)))
        elif t.isdigit():
            out.append("N")
        else:
            out.append(t)
    return out


def shingles(toks, k=10):
    return {hash(" ".join(toks[i:i + k])) for i in range(max(1, len(toks) - k + 1))}


def main():
    thr = float(sys.argv[1]) if len(sys.argv) > 1 else 0.8
    mintok = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    files = []
    for dp, _, fs in os.walk("Solidity"):
        files += [os.path.join(dp, f) for f in fs if f.endswith(".lean")]
    data = {}
    exact = collections.defaultdict(list)
    for f in files:
        toks = canon(open(f, encoding="utf-8", errors="replace").read())
        if len(toks) < mintok:
            continue
        exact[hashlib.sha1(" ".join(toks).encode()).hexdigest()].append(f)
        data[f] = (len(toks), shingles(toks))
    eg = [g for g in exact.values() if len(g) > 1]
    print(f"files compared (>= {mintok} tokens): {len(data)}")
    print(f"exact alpha-renamed copies: {len(eg)} groups, {sum(len(g) for g in eg)} files")
    for g in sorted(eg, key=len, reverse=True)[:15]:
        print("  EXACT", len(g), " | ".join(sorted(g)[:4]))
    random.seed(1)
    P = (1 << 61) - 1
    perms = [(random.randrange(1, P), random.randrange(P)) for _ in range(64)]
    buckets = collections.defaultdict(list)
    for f, (_, sh) in data.items():
        sig = [min(((a * h + b) % P) for h in sh) for a, b in perms]
        for band in range(16):
            buckets[(band, tuple(sig[band * 4:band * 4 + 4]))].append(f)
    cand = set()
    for fs in buckets.values():
        if 1 < len(fs) < 200:
            for i in range(len(fs)):
                for j in range(i + 1, len(fs)):
                    cand.add(tuple(sorted((fs[i], fs[j]))))
    pairs = []
    for a, b in cand:
        sa, sb = data[a][1], data[b][1]
        j = len(sa & sb) / len(sa | sb)
        if j >= thr:
            pairs.append((j, a, b))
    pairs.sort(reverse=True)
    # cluster near-copies (union-find)
    par = {}

    def find(x):
        par.setdefault(x, x)
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for _, a, b in pairs:
        par[find(a)] = find(b)
    cl = collections.defaultdict(list)
    for x in list(par):
        cl[find(x)].append(x)
    cls = sorted(cl.values(), key=len, reverse=True)
    nfiles = sum(len(c) for c in cls)
    nlines = sum(sum(1 for _ in open(f)) for c in cls for f in c)
    print(f"near-copy pairs (Jaccard >= {thr}): {len(pairs)}; clusters: {len(cls)}; files in clusters: {nfiles}; their lines: {nlines}")
    bydir = collections.Counter(f.split("/")[1] for c in cls for f in c)
    print("  files in clusters by area:", dict(bydir.most_common()))
    for c in cls[:20]:
        print(f"  CLUSTER {len(c)}: " + " | ".join(sorted(c)[:3]))
    print("top pairs:")
    for j, a, b in pairs[:20]:
        print(f"  {j:.3f} {a} {b}")


if __name__ == "__main__":
    main()
