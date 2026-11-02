#!/usr/bin/env bash
set -euo pipefail
exec python3 - "$@" <<'PY'
import pathlib,re,sys

def imports(path):
    return [line.split()[1] for line in path.read_text().splitlines() if line.startswith("import ") and len(line.split())>1]
def main():
    args=sys.argv[1:]; check=bool(args and args[0]=="--check")
    if check: args=args[1:]
    if check and args: raise ValueError("--check takes no modules")
    root=pathlib.Path("."); graph={}
    for p in pathlib.Path("Solidity").rglob("*.lean"):
        if p.parts[:2]==("Solidity","Scratch"): continue
        graph[p.with_suffix("").as_posix().replace("/", ".")]=imports(p)
    roots=re.findall(r'^(?:name|root)\s*=\s*"([^"]+)"',pathlib.Path("lakefile.toml").read_text(),re.M)
    stack=[]
    for r in roots:
        p=pathlib.Path(r+".lean")
        if p.is_file(): stack.extend(imports(p))
    seen=set()
    while stack:
        m=stack.pop()
        if m in seen or m not in graph: continue
        seen.add(m); stack.extend(graph[m])
    orphans=sorted(set(graph)-seen)
    if check:
        for m in orphans: print(m)
        return 1 if orphans else 0
    for m in args:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+",m) or m not in graph: raise ValueError("unknown module: "+m)
    selected=sorted(set(args) if args else set(orphans)); p=pathlib.Path("Solidity.lean"); lines=p.read_text().split("\n")
    def lcp(a,b):
        n=0
        for x,y in zip(a.split("."),b.split(".")):
            if x!=y: break
            n+=1
        return n
    for m in selected:
        imps=[(i,l.split()[1]) for i,l in enumerate(lines) if l.startswith("import ")]
        if m in (x for _,x in imps): continue
        if not imps: raise ValueError("Solidity.lean has no imports")
        best=max(lcp(x,m) for _,x in imps)
        at=max(i for i,x in imps if lcp(x,m)==best) if best>1 else imps[-1][0]
        lines.insert(at+1,"import "+m)
    text="\n".join(lines)
    if text!=p.read_text(): p.write_text(text)
    return 0
try: sys.exit(main())
except Exception as e: print("register: "+str(e),file=sys.stderr); sys.exit(2)
PY
