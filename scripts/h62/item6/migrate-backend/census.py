#!/usr/bin/env python3
"""Deterministic source census, not a Lean parser or semantic compatibility proof."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def mask(text):
    """Mask nested comments and strings, preserving positions and newlines."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            n = 2 if pair in ("/-", "-/") else 1
            if pair == "/-": depth += 1
            if pair == "-/": depth -= 1
        elif string:
            n = min(2, len(text)-i) if text[i] == chr(92) else 1
            if text[i] == '"': string = False
        elif pair == "/-":
            depth = 1
            n = 2
        elif pair == "--":
            end = text.find("\n", i)
            n = (len(text) if end == -1 else end)-i
        elif text[i] == '"':
            string = True
            n = 1
        else:
            i += 1
            continue
        for k in range(i, i+n):
            if out[k] != "\n": out[k] = " "
        i += n
    return "".join(out)

def imports(text):
    clean = mask(text)
    return [name for line in re.findall(r"(?m)^\s*(?:public\s+|meta\s+)?import\s+([^\n]+)", clean)
            for name in line.split()]

def is_toolchain_module(name):
    return name in ("Init", "Lean", "Std") or name.startswith(("Init.", "Lean.", "Std."))

def census(root):
    sources = {str(p.relative_to(root).with_suffix("")).replace("/", "."): p
               for p in sorted((root/"Solidity").rglob("*.lean"))}
    graph = {m: imports(p.read_text()) for m, p in sources.items()}
    assigned = sorted(m for m in graph if m.startswith("Solidity.Backend."))
    order, active, seen = [], set(), set()
    def visit(m):
        if m in seen: return
        if m in active: raise ValueError("import cycle: " + m)
        if m not in sources:
            if not is_toolchain_module(m):
                raise ValueError("unresolved non-toolchain import: " + m)
            return
        active.add(m)
        for dep in graph[m]: visit(dep)
        active.remove(m)
        seen.add(m)
        order.append(m)
    for m in assigned: visit(m)
    files = []
    for m in assigned:
        p = sources[m]
        raw = p.read_bytes()
        clean = mask(raw.decode())
        candidates = [{"kind": hit.group(1), "name": hit.group(2),
                       "line": clean.count("\n", 0, hit.start())+1}
                      for hit in re.finditer(r"\b(def|theorem|lemma|abbrev|inductive|structure|class|instance|axiom|opaque)\s+([^\s:({]+)", clean)]
        files.append({"module": m, "path": str(p.relative_to(root)),
                      "sha256": hashlib.sha256(raw).hexdigest(), "imports": graph[m],
                      "declaration_candidates": candidates,
                      "trust_tokens": {word: len(re.findall(r"\b"+word+r"\b", clean))
                                       for word in ("sorry", "axiom", "native_decide")}})
    return {"schema": 1, "base": BASE,
            "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
            "boundary": "Source hashes freeze every byte; declaration candidates are lexical, not elaborated API hashes.",
            "assigned_count": len(assigned), "closure_count": len(order),
            "files": files, "topological_closure": order,
            "cross_directory_edges": [{"importer": m, "dependency": dep}
                for m in assigned for dep in graph[m]
                if not dep.startswith("Solidity.Backend.")],
            "external_local_closure": sorted(set(order)-set(assigned))}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    import fcntl
    lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    lock = lockpath.open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    result = census(args.root.resolve())
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({k: result[k] for k in ("head", "assigned_count", "closure_count")}))
