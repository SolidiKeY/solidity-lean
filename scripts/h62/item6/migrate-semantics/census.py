#!/usr/bin/env python3
"""Reproduce a source-level census; hashes freeze entire files, not elaborated APIs."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path

def strip_comments(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; out.extend('  '); i+=2
        elif depth and s[i:i+2]=='-/': depth-=1; out.extend('  '); i+=2
        elif depth: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i); j=len(s) if j<0 else j
            out.extend(' '*(j-i)); i=j
        elif s[i]=='"':
            out.append(' '); i+=1
            while i<len(s):
                ch=s[i]; out.append('\n' if ch=='\n' else ' '); i+=1
                if ch=='\\' and i<len(s): out.append('\n' if s[i]=='\n' else ' '); i+=1
                elif ch=='"': break
        else: out.append(s[i]); i+=1
    return ''.join(out)

def census(root):
    files=sorted(root.glob('Solidity/Semantics/**/*.lean'))
    graph={}; records=[]
    for name in subprocess.check_output(['git','ls-files','*.lean'],cwd=root,text=True).splitlines():
        p=root/name
        src=p.read_text(); clean=strip_comments(src)
        graph[str(p.relative_to(root))[:-5].replace('/','.')]=re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',clean,re.M)
    scope={str(p.relative_to(root))[:-5].replace('/','.') for p in files}
    for p in files:
        raw=p.read_bytes(); src=strip_comments(raw.decode()); mod=str(p.relative_to(root))[:-5].replace('/','.')
        records.append({'path':str(p.relative_to(root)), 'sha256':hashlib.sha256(raw).hexdigest(), 'imports':graph[mod], 'declarations_lexical':[{'line':src[:m.start()].count('\n')+1,'kind':m[1],'name':m[2]} for m in re.finditer(r'(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(def|theorem|lemma|inductive|structure|abbrev|class|instance|axiom|opaque)\s+([^\s(:{]+)',src)]})
    order=[]; visiting=set(); visited=set()
    def visit(m):
        if m in visited or m not in graph: return
        if m in visiting: raise ValueError('import cycle '+m)
        visiting.add(m)
        for dep in graph[m]: visit(dep)
        visiting.remove(m); visited.add(m); order.append(m)
    for m in sorted(scope): visit(m)
    return {'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(), 'closure_sha256':{m:hashlib.sha256((root/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in order}, 'boundary':'Lexical inventory and full source hashes; not elaborated interface equivalence or proof validation.', 'files':records,'build_order':order, 'external_direct_imports':sorted({d for m in scope for d in graph[m] if d not in scope}), 'external_transitive_modules':[m for m in order if m not in scope], 'outside_importers':{m:sorted(set(ds)&scope) for m,ds in graph.items() if m not in scope and set(ds)&scope}}

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--root',type=Path,default=Path.cwd()); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
    a.out.write_text(json.dumps(census(a.root),indent=2)+'\n')
