#!/usr/bin/env python3
"""Deterministic source census; hashes freeze bytes, not elaborated interfaces."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT = Path(__file__).resolve().parents[4]
SCOPE = sorted((ROOT / "Solidity/Counterexamples").glob("*.lean"))
def sha(b): return hashlib.sha256(b).hexdigest()
def code_only(source):
    """Blank comments and string bodies, preserving character/line offsets."""
    out=list(source); i=0; depth=0; string=False
    while i<len(source):
        pair=source[i:i+2]
        if depth:
            if pair=="/-": depth+=1; out[i:i+2]="  "; i+=2; continue
            if pair=="-/": depth-=1; out[i:i+2]="  "; i+=2; continue
            if source[i]!="\n": out[i]=" "
        elif string:
            if source[i]=="\\" and i+1<len(source):
                out[i:i+2]="  "; i+=2; continue
            if source[i]=='"': string=False
            if source[i]!="\n": out[i]=" "
        elif pair=="/-": depth=1; out[i:i+2]="  "; i+=2; continue
        elif pair=="--":
            end=source.find("\n",i)
            if end<0: end=len(source)
            out[i:end]=" "*(end-i); i=end; continue
        elif source[i]=='"': string=True; out[i]=" "
        i+=1
    return "".join(out)
def inspect(root=ROOT):
    graph = {}
    def visit(module):
        if module in graph: return
        path = root / (module.replace(".", "/") + ".lean")
        if not path.exists():
            graph[module] = None
            return
        source = code_only(path.read_text())
        imports = re.findall(r"^import +([^\n]+)", source, re.M)
        graph[module] = [m for line in imports for m in line.split()]
        for dep in graph[module]: visit(dep)
    records = []
    for path in sorted((root / "Solidity/Counterexamples").glob("*.lean")):
        rel = path.relative_to(root).as_posix()
        raw = (root / rel).read_bytes()
        source = code_only(raw.decode())
        visit(rel[:-5].replace("/", "."))
        base = subprocess.check_output(["git", "show", f"{BASE}:{rel}"], cwd=ROOT)
        records.append({"path": rel, "sha256": sha(raw), "base_sha256": sha(base),
            "unchanged": raw == base,
            "declarations": [{"line": source[:m.start()].count("\n") + 1,
                "kind": m[1], "name": m[2] or None}
                for m in re.finditer(r"^(theorem|def|example)(?: +([^\s:]+))?", source, re.M)],
            "resource_options": re.findall(r"^set_option .*$", source, re.M),
            "trust_tokens": re.findall(r"\b(?:sorry|axiom|native_decide)\b", source)})
    return {"base": BASE, "files": records, "import_graph": dict(sorted(graph.items())),
        "external_dependencies": sorted(m for m, deps in graph.items()
            if deps is not None and not m.startswith("Solidity.Counterexamples.")),
        "boundary": "Byte equality freezes all statements, definitions, examples and proofs. Declaration inventory is a line-based census, not a Lean parser; hashes are not elaborated type hashes."}
if __name__ == "__main__":
    print(json.dumps(inspect(), indent=2, ensure_ascii=False))
