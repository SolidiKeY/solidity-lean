"""Tiny anti-unification compressor over Lean source.
Unit = indentation block (a line + deeper-indented lines). Tree = lines -> tokens.
Group units by shape, compute least general generalization (LGG) per group,
rank by MDL saving = (k-1)*const_tokens - k*holes."""
import re, sys, collections

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

main(sys.argv[2:])
