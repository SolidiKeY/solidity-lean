#!/usr/bin/env python3
"""Deterministic source census; hashes are source identities, not elaborated types."""
import argparse, hashlib, json, pathlib, re, subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
NAMES = "CanonTest CleanTail CleanTailRun Constructibility Fits HeredRun Reachability Sorts Soundness Tight TypedRunInv Values".split()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def code(text):
    # Preserve offsets/newlines, discard nested comments and string contents.
    out = list(text); i = 0; depth = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2; continue
            if text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2; continue
            if text[i] != "\n": out[i] = " "
        elif string:
            if text[i] == "\\" and i+1 < len(text):
                out[i:i+2] = "  "; i += 2; continue
            if text[i] == '"': string = False
            if text[i] != "\n": out[i] = " "
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out[i:end] = " " * (end-i); i = end; continue
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2; continue
        elif text[i] == '"':
            out[i] = " "; string = True
        i += 1
    if depth or string: raise ValueError("unterminated comment/string")
    return "".join(out)

def imports(text):
    return [m for line in re.findall(r"^\s*(?:public\s+)?import[ \t]+([^\n]+)", code(text), re.M) for m in line.split()]

def census(root):
    assigned = ["Solidity.Typing."+n for n in NAMES]
    actual = sorted(p.stem for p in (root/"Solidity/Typing").glob("*.lean"))
    if actual != sorted(NAMES): raise ValueError("assigned Typing file census mismatch")
    graph = {}; external = set(); order = []; active = set()
    def visit(m):
        if m in active: raise ValueError("import cycle: "+m)
        if m in graph or m in external: return
        p = root/(m.replace(".","/")+".lean")
        if not p.exists():
            if not (m == "Init" or m == "Lean" or m == "Std" or m.startswith(("Init.", "Lean.", "Std."))):
                raise ValueError("missing local import: "+m)
            external.add(m); return
        active.add(m)
        deps = imports(p.read_text()); graph[m] = deps
        for d in deps: visit(d)
        active.remove(m); order.append(m)
    for m in assigned: visit(m)
    files = []
    for m in assigned:
        path = m.replace(".","/")+".lean"; raw = (root/path).read_bytes(); text = raw.decode(); clean = code(text)
        # Inventory syntax sites, including private/local declarations. This is
        # deliberately not advertised as a Lean environment/type export.
        declarations = []
        for match in re.finditer(r"^[ \t]*(?:@\[[^\]\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s(:{]+)", clean, re.M):
            declarations.append({"kind":match[1], "name":match[2], "line":clean.count("\n",0,match.start())+1})
        files.append({"module":m,"path":path,"sha256":digest(raw),"lines":text.count("\n"),"imports":graph[m],"declaration_sites":declarations,
          "branch_sites":[i for i,line in enumerate(clean.splitlines(),1) if re.match(r"\s*(?:\||case\s)",line)],
          "budget_sites":[{"line":i,"text":line.strip()} for i,line in enumerate(clean.splitlines(),1) if "maxHeartbeats" in line or "maxRecDepth" in line],
          "trust_sites":[{"line":i,"text":line.strip()} for i,line in enumerate(clean.splitlines(),1) if re.search(r"\b(sorry|axiom|native_decide)\b",line)]})
    edges = [{"from":m,"to":d} for m in sorted(graph) for d in graph[m] if m in assigned and d not in assigned]
    importers = []
    for p in sorted((root/"Solidity").rglob("*.lean")):
        m = str(p.relative_to(root).with_suffix("")).replace("/", ".")
        if m not in assigned:
            for d in imports(p.read_text()):
                if d in assigned: importers.append({"from":m,"to":d})
    return {"schema":1,"base":BASE,"files":files,"local_build_order":order,"external_imports":sorted(external),"local_import_graph":dict(sorted(graph.items())),"outbound_cross_directory":edges,"inbound_cross_directory":importers}

def verify(root, frozen):
    current = census(root)
    if current != frozen: raise ValueError("frozen census mismatch")
    return current

if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--root",type=pathlib.Path,default=pathlib.Path.cwd()); ap.add_argument("--verify",type=pathlib.Path)
    args=ap.parse_args()
    result=verify(args.root,json.loads(args.verify.read_text())) if args.verify else census(args.root)
    print(json.dumps(result,sort_keys=True,indent=2))
