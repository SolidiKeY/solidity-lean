#!/usr/bin/env python3
"""Deterministic source/import census. Lexical inventory is not elaborated API proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def mask(text):
    """Mask nested comments and strings, preserving newlines and offsets."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "; i += 1
                if i < len(text):
                    if text[i] != "\n": out[i] = " "
                    i += 1
            else:
                if text[i] == '"': string = False
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1: j = len(text)
            out[i:j] = " " * (j-i); i = j
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif text[i] == '"':
            out[i] = " "; string = True; i += 1
        else: i += 1
    return "".join(out)

def imports(text):
    return [m for line in mask(text).splitlines()
            if re.match(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+", line)
            for m in re.sub(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+", "", line).split()]

def sha(data): return hashlib.sha256(data).hexdigest()

def census(root, revision=BASE):
    def git(*args):
        return subprocess.check_output(["git", "-C", str(root), *args])
    paths = sorted(p for p in git("ls-tree", "-r", "--name-only", revision).decode().splitlines() if p.endswith(".lean"))
    blobs = {p: git("show", f"{revision}:{p}") for p in paths}
    modules = {p[:-5].replace("/", "."): p for p in paths}
    graph = {m: imports(blobs[p].decode()) for m, p in modules.items()}
    assigned = sorted(m for m,p in modules.items() if p.startswith("Solidity/Source/"))
    closure, order, visiting = set(), [], set()
    def visit(m):
        if m in visiting: raise ValueError("import cycle at " + m)
        if m in closure or m not in modules: return
        visiting.add(m)
        for dep in graph[m]: visit(dep)
        visiting.remove(m); closure.add(m); order.append(m)
    visit("Solidity.KeySort")
    for m in assigned: visit(m)
    entries = []
    declaration = re.compile(r"\b(theorem|lemma|def|abbrev|inductive|structure|class|instance|example|axiom|opaque)\b")
    for m in assigned:
        p = modules[m]; data = blobs[p]; text = data.decode(); clean = mask(text)
        candidates = [{"line": i, "kind": hit.group(1), "text": line.strip()}
                      for i,line in enumerate(clean.splitlines(), 1)
                      if (hit := declaration.search(line))]
        entries.append({"module": m, "path": p, "sha256": sha(data), "imports": graph[m],
                        "lexical_declaration_candidates": candidates,
                        "budget_options": [line.strip() for line in clean.splitlines() if re.search(r"set_option\s+(maxHeartbeats|maxRecDepth)",line)],
                        "sorry_tokens": len(re.findall(r"\bsorry\b", clean)),
                        "axiom_tokens": len(re.findall(r"\baxiom\b", clean)),
                        "native_decide_tokens": len(re.findall(r"\bnative_decide\b", clean))})
    direct = sorted({d for m in assigned for d in graph[m] if d not in assigned})
    reverse = sorted((m,d) for m in graph if m not in assigned for d in graph[m] if d in assigned)
    return {"schema": 1, "base": BASE, "revision": revision,
            "boundary": "Exact file hashes freeze all bytes, including statements and proof budgets. Lexical candidates are navigational, not elaborated declarations or API equivalence.",
            "assigned_count":len(assigned), "closure_count":len(closure), "files": entries,
            "external_direct_imports": direct, "nonlocal_imports": sorted({d for m in closure for d in graph[m] if d not in modules}), "external_transitive_local_modules":sorted(closure-set(assigned)),
            "external_consumers":reverse, "serial_build_order":order,
            "closure_file_hashes": {modules[m]:sha(blobs[modules[m]]) for m in sorted(closure)}}

if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--root", type=Path, default=Path.cwd()); ap.add_argument("--revision",default=BASE); ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args(); result=census(a.root,a.revision)
    a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("base","assigned_count","closure_count","external_direct_imports")}))
