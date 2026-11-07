#!/usr/bin/env python3
"""Inventory imports and byte-frozen Automation sources at an explicit Git revision."""
import argparse, hashlib, json, re, subprocess

def uncomment(source):
    out=[]; i=0; depth=0; string=False
    while i<len(source):
        pair=source[i:i+2]; c=source[i]
        if depth:
            if pair=='/-': depth+=1; i+=2
            elif pair=='-/': depth-=1; i+=2
            else:
                out.append('\n' if c=='\n' else ' '); i+=1
        elif string:
            out.append('\n' if c=='\n' else ' '); i+=1
            if c=='\\' and i<len(source): out.append(' '); i+=1
            elif c=='"': string=False
        elif pair=='/-': depth=1; out.append(' '); i+=2
        elif pair=='--':
            end=source.find('\n',i); i=len(source) if end<0 else end
        else:
            out.append(c); i+=1
            if c=='"': string=True; out[-1]=' '
    if depth: raise ValueError('unterminated block comment')
    return ''.join(out)

def imports(source):
    return [m for line in uncomment(source).splitlines()
            if re.match(r'^\s*(?:public\s+|meta\s+)?import\s+',line)
            for m in re.sub(r'^\s*(?:public\s+|meta\s+)?import\s+','',line).split()]

def census(repo,revision):
    def git(*args): return subprocess.check_output(['git','-C',repo,*args])
    revision=git('rev-parse',revision+'^{commit}').decode().strip()
    paths=git('ls-tree','-r','--name-only',revision).decode().splitlines()
    modules={p[:-5].replace('/','.'):p for p in paths if p.endswith('.lean')}
    roots=sorted(m for m,p in modules.items() if p.startswith('Solidity/Automation/'))
    sources={}; edges={}; seen=set()
    def visit(m):
        if m in seen:return
        seen.add(m)
        if m not in modules:return
        b=git('show',revision+':'+modules[m]); sources[m]=b
        edges[m]=imports(b.decode())
        for dep in edges[m]: visit(dep)
    for root in roots:visit(root)
    files=[{'path':p,'sha256':hashlib.sha256(git('show',revision+':'+p)).hexdigest()}
           for p in paths if p.startswith('Solidity/Automation/')]
    return {'revision':revision,'roots':roots,'files':files,'imports':dict(sorted(edges.items())),
        'local_closure':sorted(edges),'external_imports':sorted(seen-set(edges)),
        'cross_directory_direct':[{'module':m,'dependency':d,'owner':'migrate-calculus / live Calculus producer'}
            for m in roots for d in edges[m] if d in modules and d not in roots],
        'elaborators':{m:[{'line':i+1,'kind':'elab_rules','source_sha256':hashlib.sha256(sources[m]).hexdigest()} for i,line in enumerate(uncomment(sources[m].decode()).splitlines()) if re.match(r'^elab_rules\s*:',line)] for m in roots},
        'declarations':{m:[{'kind':x[0],'name':x[1] or x[2]} for x in re.findall(
            r'\b(def|theorem|syntax)\s+(?:\(name\s*:=\s*([^\s)]+)\)|([^\s(:]+))',uncomment(sources[m].decode()))]
            for m in roots}}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--revision',required=True)
    a=p.parse_args(); print(json.dumps(census(a.repo,a.revision),indent=2,sort_keys=True))
