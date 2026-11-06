#!/usr/bin/env python3
"""Deterministic source inventory; source hashes are NOT elaborated API hashes."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def code_only(text):
    """Blank nested comments and string contents, preserving line numbers."""
    out=list(text); depth=0; string=False; i=0
    while i<len(text):
        if depth:
            if text[i:i+2]=="/-": depth+=1; out[i:i+2]="  "; i+=2; continue
            if text[i:i+2]=="-/": depth-=1; out[i:i+2]="  "; i+=2; continue
            if text[i]!="\n": out[i]=" "
        elif string:
            if text[i]=="\\" and i+1<len(text):
                out[i]=" "; out[i+1]="\n" if text[i+1]=="\n" else " "; i+=2; continue
            if text[i]=='"': string=False
            out[i]="\n" if text[i]=="\n" else " "
        elif text[i:i+2]=="/-": depth=1; out[i:i+2]="  "; i+=2; continue
        elif text[i:i+2]=="--":
            end=text.find("\n",i)
            if end<0: end=len(text)
            out[i:end]=" "*(end-i); i=end; continue
        elif text[i]=='"': string=True; out[i]=" "
        i+=1
    if depth or string: raise ValueError("Unterminated comment/string")
    return "".join(out)

def imports(text):
    return re.findall(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", code_only(text), re.M)

def inventory(root):
    files = sorted(root.glob("Solidity/Syntax/**/*.lean"))
    modules = {str(p.relative_to(root))[:-5].replace("/", "."): p for p in root.glob("Solidity/**/*.lean")}
    order, seen, active, toolchain_imports = [], set(), set(), set()
    def visit(m):
        if m in active: raise ValueError("Import cycle: "+m)
        if m in seen: return
        if m not in modules:
            if m.startswith("Solidity."): raise ValueError("Missing local import: "+m)
            toolchain_imports.add(m); return
        active.add(m)
        for dep in imports(modules[m].read_text()): visit(dep)
        active.remove(m); seen.add(m); order.append(m)
    rows=[]
    for p in files:
        m=str(p.relative_to(root))[:-5].replace("/", ".")
        visit(m)
        text=p.read_text(); code=code_only(text)
        rows.append(dict(path=str(p.relative_to(root)), module=m,
            source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(), imports=imports(text),
            declaration_lines=[dict(line=i, text=s.strip()) for i,s in enumerate(code.splitlines(),1)
                if re.match(r"^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped) )*(?:def|theorem|lemma|inductive|structure|abbrev|class|instance|opaque)\b", s)],
            command_lines=[dict(line=i,text=s.strip()) for i,s in enumerate(code.splitlines(),1) if re.match(r"^\s*(?:scoped\s+|local\s+)?(?:syntax|macro|macro_rules|elab|elab_rules|declare_syntax_cat|deriving|attribute)\b",s)],
            case_lines=[i for i,s in enumerate(code.splitlines(),1) if s.lstrip().startswith("|")],
            budget_lines=[dict(line=i,text=s.strip()) for i,s in enumerate(text.splitlines(),1) if "maxHeartbeats" in s or "maxRecDepth" in s]))
    owned={r["module"] for r in rows}
    return dict(base=BASE, hash_kind="whole-source SHA256; lexical declaration inventory, not kernel API census",
        files=rows, build_order=order, toolchain_imports=sorted(toolchain_imports), external_dependencies=[m for m in order if m not in owned],
        direct_external_edges=[dict(importer=r["module"], dependency=d) for r in rows for d in r["imports"] if d not in owned])

if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--root", type=Path, default=Path.cwd()); ap.add_argument("--output", type=Path, required=True)
    a=ap.parse_args(); a.output.write_text(json.dumps(inventory(a.root), indent=2, sort_keys=True)+"\n")
