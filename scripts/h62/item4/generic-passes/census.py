#!/usr/bin/env python3
"""Deterministic lexical inventory. Hashes exact source, not elaborated types.
Comments/strings are blanked without changing offsets. Every family source is
retained, including non-Control negative/pin/fixture modules. No case selection.
"""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT = Path(__file__).resolve().parents[4]
FAMILY = "Solidity/Backend/Passes/"
DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(def|abbrev|opaque|theorem|lemma|example|instance|structure|inductive)\b(?:[ \t]+([^\s:({]+))?")
def sha(data): return hashlib.sha256(data).hexdigest()
def blank(source):
    out=list(source); i=0; depth=0; quoted=False
    while i<len(source):
        if depth:
            if source.startswith("/-",i):
                out[i:i+2]='  '; depth+=1; i+=2; continue
            if source.startswith("-/",i):
                out[i:i+2]='  '; depth-=1; i+=2; continue
            if source[i]!='\n': out[i]=' '
        elif quoted:
            if source[i]=='\\':
                out[i]=' '; i+=1
                if i<len(source): out[i]=' '
            elif source[i]=='"': out[i]=' '; quoted=False
            elif source[i]!='\n': out[i]=' '
        elif source.startswith("/-",i):
            out[i:i+2]='  '; depth=1; i+=2; continue
        elif source.startswith("--",i):
            end=source.find('\n',i)
            if end<0: end=len(source)
            out[i:end]=' '*(end-i); i=end; continue
        elif source[i]=='"': out[i]=' '; quoted=True
        i+=1
    if depth or quoted: raise ValueError('unterminated comment/string')
    return ''.join(out)
def signature_end(clean,start,end):
    depth=0
    for i in range(start,end):
        c=clean[i]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        if depth==0 and (clean.startswith(':=',i) or (clean.startswith('where',i) and (i==0 or not (clean[i-1].isalnum() or clean[i-1] in "_'")) and (i+5==len(clean) or not (clean[i+5].isalnum() or clean[i+5] in "_'"))) or (clean[i]=='|' and clean[clean.rfind('\n',0,i)+1:i].strip()=='')):
            return i
    return end

def inventory():
    paths=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,'--',FAMILY],cwd=ROOT,text=True).splitlines()
    files=[]
    for path in paths:
        if not path.endswith('.lean'): continue
        raw=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
        source=raw.decode(); clean=blank(source); matches=list(DECL.finditer(clean)); declarations=[]
        for index,m in enumerate(matches):
            end=matches[index+1].start() if index+1<len(matches) else len(source)
            finish=signature_end(clean,m.end(),end)
            declarations.append(dict(kind=m[1],name=m[2] if m[1]!='example' else None,
                line=source.count('\n',0,m.start())+1,
                statement_source_sha256=sha(source[m.start():finish].encode()),
                statement=source[m.start():finish].rstrip()))
        files.append(dict(path=path,sha256=sha(raw),control=path.endswith('Controls.lean'),
            imports=re.findall(r'(?m)^import\s+(\S+)',clean),
            axiom_guards=len(re.findall(r'(?m)^#print axioms ',clean)),
            declarations=declarations))
    return dict(schema=1,base=BASE,boundary='lexical source inventory; no elaborated type equivalence claim',
        files=files,totals=dict(files=len(files),controls=sum(f['control'] for f in files),
            declarations=sum(len(f['declarations']) for f in files),
            control_declarations=sum(len(f['declarations']) for f in files if f['control'])))
def main():
    p=argparse.ArgumentParser(); p.add_argument('--output',type=Path); p.add_argument('--check',type=Path); a=p.parse_args()
    result=inventory(); encoded=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
    if a.check:
        if a.check.read_bytes()!=encoded: raise SystemExit('FAIL: census differs from pinned original')
        for f in result['files']:
            if sha((ROOT/f['path']).read_bytes())!=f['sha256']: raise SystemExit('FAIL: original changed: '+f['path'])
        print('PASS: exact pinned census and every original source unchanged')
    if a.output: a.output.write_bytes(encoded)
    print(json.dumps(result['totals'],sort_keys=True))
if __name__=='__main__': main()
