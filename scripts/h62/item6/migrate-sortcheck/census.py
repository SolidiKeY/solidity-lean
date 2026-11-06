#!/usr/bin/env python3
"""Deterministic source census. Source hashes freeze whole files, not just signatures.
The declaration index is lexical/advisory; Lean acceptance is a separate gate.
"""
import hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
TARGETS = ["Solidity.SortCheck.Annotations", "Solidity.SortCheck.Faithfulness", "Solidity.SortCheck.Parser"]
def uncomment(s):
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        c=s[i]; pair=s[i:i+2]
        if depth:
            if pair=="/-": depth+=1; out.extend("  "); i+=2
            elif pair=="-/": depth-=1; out.extend("  "); i+=2
            else: out.append("\n" if c=="\n" else " "); i+=1
        elif string:
            out.append(c); i+=1
            if c=="\\" and i<len(s): out.append(s[i]); i+=1
            elif c=='"': string=False
        elif pair=="/-": depth=1; out.extend("  "); i+=2
        elif pair=="--":
            j=s.find("\n",i); j=len(s) if j<0 else j
            out.extend(" "*(j-i)); i=j
        else:
            out.append(c); i+=1
            if c=='"': string=True
    return "".join(out)
def path(m, source_root=ROOT): return source_root / (m.replace(".","/")+".lean")
def imports(m, source_root=ROOT):
    # Lean 4.35 header: optional module/prelude, then optional public/meta,
    # import, optional all, one module identifier. Reject unhandled valid
    # syntax rather than silently omitting overlay dependencies.
    out=[]
    for lineno,line in enumerate(uncomment(path(m,source_root).read_text()).splitlines(),1):
        line=line.strip()
        if not line or line in {"module","prelude"}: continue
        if re.fullmatch(r"(?:public|meta)(?:\s+(?:public|meta))*",line):
            raise ValueError(f"unsupported multiline import modifier: {path(m,source_root)}:{lineno}: {line}")
        if not re.match(r"(?:(?:public|meta)\s+)*import\b",line): break
        match=re.fullmatch(r"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\w+(?:\.\w+)*)",line)
        if not match or match[1]=="all":
            raise ValueError(f"unsupported import header: {path(m,source_root)}:{lineno}: {line}")
        out.append(match[1])
    return out
def closure(targets, source_root=ROOT):
    done=set(); active=set(); ordered=[]
    def visit(m):
        if m in done: return
        if not path(m, source_root).exists():
            if m in targets or m.startswith("Solidity."):
                raise ValueError("missing repository module: "+m)
            return
        if m in active: raise ValueError("import cycle: "+m)
        active.add(m)
        for x in imports(m, source_root): visit(x)
        active.remove(m); done.add(m); ordered.append(m)
    for m in targets: visit(m)
    return ordered

def census():
    files={}
    for m in TARGETS:
        p=path(m); raw=p.read_bytes(); s=uncomment(raw.decode())
        old=subprocess.check_output(["git","show",BASE+":"+str(p.relative_to(ROOT))],cwd=ROOT)
        files[m]={"path":str(p.relative_to(ROOT)),"sha256":hashlib.sha256(raw).hexdigest(),
          "base_sha256":hashlib.sha256(old).hexdigest(),"unchanged":raw==old,"imports":imports(m),
          "generated_theorems":[{"line":i,"constructor":parts[1],"domain":parts[2],"class":parts[3],
            "name":"Solidity.SortFaithfulness.faithful_"+parts[1]}
            for i,line in enumerate(s.splitlines(),1) if line.startswith("faithful_theorem ")
            for parts in [line.split()]],
          "pattern_clauses":[{"line":i,"text":line.strip()} for i,line in enumerate(s.splitlines(),1) if line.lstrip().startswith("|")],
          "where_declarations":[{"line":i,"text":line.strip()} for i,line in enumerate(s.splitlines(),1) if re.match(r"\s+dropBlock\s*:",line)],
          "commands":[{"line":i,"text":line.strip()} for i,line in enumerate(s.splitlines(),1)
            if re.match(r"\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|class|instance|example|macro|syntax|elab|#guard|#print|#check|set_option|namespace|end)\b",line)],
          "proof_budget_lines":[line.strip() for line in s.splitlines() if "maxHeartbeats" in line],
          "trust_tokens":{t:len(re.findall(r"\b"+t+r"\b",s)) for t in ["sorry","axiom","native_decide"]}}
    return {"base":BASE,"files":files,"closure_order":closure(TARGETS),
      "external_repository_dependencies":[m for m in closure(TARGETS) if m not in TARGETS],
      "note":"Lexical command index is not an elaborated interface or axiom audit; exact whole-file hashes are the source freeze."}
if __name__=="__main__": print(json.dumps(census(),indent=2,sort_keys=True))
