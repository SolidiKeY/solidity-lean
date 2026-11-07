#!/usr/bin/env python3
"""Deterministic source/import census; source hashes are not elaborated type hashes."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path

def uncomment(s):
    # Nested Lean block comments and line comments; preserve newlines/strings.
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        pair=s[i:i+2]; c=s[i]
        if depth:
            if pair=="/-": depth+=1; i+=2; continue
            if pair=="-/": depth-=1; i+=2; continue
            out.append("\n" if c=="\n" else " "); i+=1; continue
        if not string and pair=="/-": out.append(" "); depth=1; i+=2; continue
        if not string and pair=="--":
            j=s.find("\n",i); i=len(s) if j<0 else j; continue
        out.append(c)
        if string and c=="\\" and i+1<len(s): out.append(s[i+1]); i+=2; continue
        if c=='"': string=not string
        i+=1
    if depth: raise ValueError("unterminated block comment")
    return "".join(out)

def census(root):
    paths=sorted(root.glob("Solidity/Lowering/**/*.lean")); rows=[]; graph={}
    for p in sorted(root.glob("Solidity/**/*.lean")):
        code=uncomment(p.read_text()); mod=".".join(p.relative_to(root).with_suffix("").parts)
        imports=[]
        for line in code.splitlines():
            m=re.match(r"^\s*(?:(?:public|private)\s+)?import\s+(.+)$",line)
            if m: imports.extend(m[1].split())
        graph[mod]=imports
        if p not in paths: continue
        decls=[{"line":i,"kind":m[1],"name":m[2]} for i,line in enumerate(code.splitlines(),1) if (m:=re.match(r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*(def|theorem|lemma|abbrev|inductive|structure|class|axiom|instance|example)\b\s*([^\s(:{]*)",line))]
        rows.append({"path":str(p.relative_to(root)),"module":mod,"sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"imports":imports,"declarations_lexical":decls,"api_directives":[{"line":i,"text":line.strip()} for i,line in enumerate(code.splitlines(),1) if re.match(r"^\s*(?:(?:local|scoped)\s+)?(?:deriving\s+instance|attribute)\b",line)],"budgets":[line.strip() for line in code.splitlines() if re.search(r"set_option\s+(maxHeartbeats|maxRecDepth)",line)]})
    scope={r["module"] for r in rows}; seen=set(); active=set(); order=[]
    def visit(m):
        if m in active: raise ValueError("import cycle at "+m)
        if m in seen: return
        active.add(m)
        seen.add(m)
        for dep in graph.get(m,[]): visit(dep)
        active.remove(m)
        if m in graph: order.append(m)
    for m in sorted(scope): visit(m)
    return {"base":subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip(),"note":"Lexical inventory: not an elaborated declaration/type/axiom audit. Whole-source hashes freeze all bytes.","modules":rows,"direct_external_edges":[{"from":r["module"],"to":d} for r in rows for d in r["imports"] if d not in scope],"closure_order":order,"external_project_closure":[m for m in order if m not in scope]}

if __name__=="__main__":
    a=argparse.ArgumentParser(); a.add_argument("--root",type=Path,default=Path.cwd()); a.add_argument("--output",type=Path,required=True); a.add_argument("--base"); args=a.parse_args()
    result=census(args.root.resolve())
    if args.base:
        base=subprocess.check_output(["git","rev-parse",args.base],cwd=args.root,text=True).strip()
        subprocess.run(["git","diff","--exit-code",base,"--","Solidity/Lowering"],cwd=args.root,check=True)
        paths=set(subprocess.check_output(["git","ls-tree","-r","--name-only",base,"Solidity/Lowering"],cwd=args.root,text=True).splitlines())
        assert {x for x in paths if x.endswith(".lean")}=={r["path"] for r in result["modules"]}, "pinned source path set mismatch"
        result["snapshot_head"]=result["base"]; result["base"]=base
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"modules":len(result["modules"]),"direct_external_edges":len(result["direct_external_edges"]),"closure_modules":len(result["closure_order"]),"output":str(args.output)}))
