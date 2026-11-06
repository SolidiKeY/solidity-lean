#!/usr/bin/env python3
"""Deterministic source census; source hashes freeze all bytes, not inferred APIs."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def scan(root):
    files = subprocess.check_output(["git", "ls-files", "*.lean"], cwd=root, text=True).splitlines()
    modules = {p[:-5].replace("/", "."): p for p in files if not p.startswith(("Bridge/", "tests/", "vendor/"))}
    modules.update({p[len("vendor/LeanTeX/"):-5].replace("/", "."): p for p in files if p.startswith("vendor/LeanTeX/")})
    def clean(s):
        # Preserve newlines for line evidence. Nested block and line comments.
        out=[]; i=0; depth=0; string=False
        while i<len(s):
            if depth:
                if s.startswith("/-", i): depth+=1; out.extend("  "); i+=2
                elif s.startswith("-/", i): depth-=1; out.extend("  "); i+=2
                else: out.append("\n" if s[i]=="\n" else " "); i+=1
            elif string:
                if s[i]=="\\": out.extend("  "); i+=2
                elif s[i]=='"': string=False; out.append(" "); i+=1
                else: out.append("\n" if s[i]=="\n" else " "); i+=1
            elif s.startswith("/-",i): depth=1; out.extend("  "); i+=2
            elif s.startswith("--",i):
                j=s.find("\n",i); j=len(s) if j<0 else j; out.extend(" "*(j-i)); i=j
            elif s[i]=='"': string=True; out.append(" "); i+=1
            else: out.append(s[i]); i+=1
        return "".join(out)
    imports={}; owned={}
    for m,p in sorted(modules.items()):
        raw=(root/p).read_bytes(); s=clean(raw.decode())
        imports[m]=[v for x in re.findall(r"(?m)^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)",s) for v in x.split()]
        if p.startswith("Solidity/TestSuite/"):
            owned[m]={"path":p,"sha256":hashlib.sha256(raw).hexdigest(),"imports":imports[m],
                "declaration_lines":[{"line":n,"text":l.strip()} for n,l in enumerate(s.splitlines(),1) if re.match(r"\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:theorem|lemma|def|abbrev|opaque|axiom|instance|structure|inductive)\b",l)],
                "commands":[{"line":n,"text":l.strip()} for n,l in enumerate(s.splitlines(),1) if re.match(r"\s*(?:#|set_option|prepare_memory_replay|discover_memory_replay|assemble_memory_replay|resume_memory_replay|solc_scoped_problems|sol_auto_theorem)",l)]}
    order=[]; active=set(); visited=set()
    def visit(m):
        if m in active: raise ValueError("import cycle: "+m)
        if m in visited or m not in modules: return
        active.add(m)
        for dep in imports[m]: visit(dep)
        active.remove(m); visited.add(m); order.append(m)
    for m in sorted(owned): visit(m)
    return {"base":BASE,"kind":"source census; generated declarations require Lean validation","owned":owned,"build_order":order,"module_paths":{m:modules[m] for m in order},"external_edges":[{"from":m,"to":d} for m in sorted(owned) for d in imports[m] if d not in owned],"closure_modules":len(order),"closure_sha256":{modules[m]:hashlib.sha256((root/modules[m]).read_bytes()).hexdigest() for m in order},"source_matches_pinned_base":subprocess.run(["git","diff","--quiet",BASE,"--"]+[modules[m] for m in order],cwd=root).returncode==0}
if __name__=="__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--root",type=Path,default=Path.cwd()); a=ap.parse_args()
    print(json.dumps(scan(a.root),sort_keys=True,indent=2))
