#!/usr/bin/env python3
"""Deterministic source census; source hashes freeze ALL statements and bodies.
Declaration lines are an audit index, not an elaborated Lean interface parser.
"""
import hashlib, json, pathlib, re, subprocess, sys
root = pathlib.Path(__file__).resolve().parents[4]
base = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
def sha(b): return hashlib.sha256(b).hexdigest()
def census():
    files = sorted(root.glob('Solidity/Language/**/*.lean'))
    base_files = subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--','Solidity/Language/'],cwd=root).decode().splitlines()
    base_files = sorted(p for p in base_files if p.endswith('.lean'))
    modules = {str(p.relative_to(root))[:-5].replace('/', '.') for p in files}
    rows = []
    for p in files:
        rel = str(p.relative_to(root)); data = p.read_bytes(); s = data.decode()
        old = subprocess.check_output(['git','show',base+':'+rel],cwd=root)
        rows.append(dict(path=rel,sha256=sha(data),base_sha256=sha(old),unchanged=data==old,
            imports=re.findall(r'^import\s+(\S+)',s,re.M),
            declarations=[dict(line=i,kind=m[1],name=m[2]) for i,l in enumerate(s.splitlines(),1)
                if (m:=re.match(r'^(?:private |protected |noncomputable |unsafe )*(def|abbrev|theorem|lemma|structure|inductive|class|instance|example)\s+([^\s:(]+)?',l))],
            commands=[dict(line=i,text=l) for i,l in enumerate(s.splitlines(),1) if l.startswith(('#','set_option'))]))
    consumers=[]
    for rel in subprocess.check_output(['git','ls-files','*.lean'],cwd=root).decode().splitlines():
        p = root / rel
        if not p.is_file(): continue
        if str(p.relative_to(root))[:-5].replace('/', '.') in modules: continue
        for imp in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):
            if imp in modules: consumers.append(dict(path=str(p.relative_to(root)),imports=imp))
    return dict(base=base,inventory_unchanged=base_files==sorted(r['path'] for r in rows),files=rows,external_imports=sorted({i for r in rows for i in r['imports'] if i not in modules}),consumers=consumers)
if __name__=='__main__':
    result=census()
    print(json.dumps(result,indent=2,sort_keys=True))
    if '--require-unchanged' in sys.argv and (not result['inventory_unchanged'] or not all(r['unchanged'] for r in result['files'])): sys.exit(1)

    if '--require-inventory' in sys.argv and not result['inventory_unchanged']: sys.exit(1)
