#!/usr/bin/env python3
"""Conservative source census; never treats extracted signatures as kernel evidence.
Every syntactic theorem is retained, including no-premise and private helpers.
Exact signatures plus surrounding variable commands are frozen by SHA256.
Elaborated binder classification and simultaneous witnesses remain separate gates.
"""
import argparse, hashlib, json, pathlib, re, subprocess

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

def mask(s):
    """Blank nested Lean comments and strings, preserving offsets/newlines."""
    out=list(s); i=0; depth=0; quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): out[i:i+2]='  '; depth+=1; i+=2
            elif s.startswith('-/',i): out[i:i+2]='  '; depth-=1; i+=2
            else:
                if s[i]!='\n': out[i]=' '
                i+=1
        elif quoted:
            if s[i]=='\\':
                out[i]=' '; i+=1
                if i<len(s): out[i]=' '; i+=1
            else:
                if s[i]=='"': quoted=False
                if s[i]!='\n': out[i]=' '
                i+=1
        elif s.startswith('/-',i): out[i:i+2]='  '; depth=1; i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i); j=len(s) if j<0 else j; out[i:j]=' '*(j-i); i=j
        elif s[i]=='"': out[i]=' '; quoted=True; i+=1
        else: i+=1
    if depth or quoted: raise ValueError('unterminated comment/string')
    return ''.join(out)

def signature_end(m,start):
    nesting=[]; i=start; root_match=False; pending_lets=0
    opening='({[⟨⦃'; closing=')} ]⟩⦄'.replace(' ','')
    def keyword(word,at):
        previous=m[at-1] if at else ' '
        after=m[at+len(word)] if at+len(word)<len(m) else ' '
        identifier=lambda c:c.isalnum() or c in "_'.«»"
        return m.startswith(word,at) and not identifier(previous) and not identifier(after)
    while i<len(m):
        c=m[i]
        if c in opening: nesting.append(c)
        elif c in closing:
            if not nesting or opening.index(nesting[-1])!=closing.index(c):
                raise ValueError('unbalanced signature')
            nesting.pop()
        if not nesting:
            if keyword('match',i):root_match=True
            if keyword('let',i):pending_lets+=1
            if m.startswith(':=',i):
                if pending_lets:pending_lets-=1
                else:return i
            if c=='|' and not root_match and not m[m.rfind('\n',0,i)+1:i].strip():return i
            if keyword('where',i):return i
        i+=1
    raise ValueError('missing theorem body')

def scan(path):
    source=path.read_text(); m=mask(source); records=[]; stack=[]; variables=[]
    command=re.compile(r'(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(namespace|section|mutual|end|variable|include|omit|theorem)\b[ \t]*([^\n]*)')
    consumed=0
    for c in command.finditer(m):
        if c.start()<consumed: continue
        kind,tail=c.group(1),c.group(2).strip()
        if kind in ('namespace','section','mutual'): stack.append((kind,tail,len(variables)))
        elif kind=='end':
            if stack:
                _,_,n=stack.pop(); variables=variables[:n]
        elif kind in ('variable','include','omit'):
            start=c.start(); end=c.end(); balance=sum(m[start:end].count(x)-m[start:end].count(y) for x,y in [('(',')'),('{','}'),('[',']')])
            while balance>0:
                nxt=m.find('\n',end+1); nxt=len(m) if nxt<0 else nxt
                balance+=sum(m[end:nxt].count(x)-m[end:nxt].count(y) for x,y in [('(',')'),('{','}'),('[',']')]); end=nxt
            variables.append(source[start:end].strip()); consumed=end
        elif kind=='theorem':
            name=re.match(r'[^\s({\[:]+',tail)
            if not name: raise ValueError(f'unrecognized theorem at {path}:{c.start()}')
            name=name.group(); end=signature_end(m,c.start()); consumed=end
            ns='.'.join(n for k,n,_ in stack if k=='namespace'); fq=(ns+'.'+name).removeprefix('_root_.') if ns else name
            if name.startswith('_root_.'): fq=name.removeprefix('_root_.')
            signature=source[c.start():end].strip()
            records.append(dict(candidate_name=fq,qualified_name_is_source_candidate=True,line=source.count('\n',0,c.start())+1,visibility='private' if re.search(r'\bprivate\b',m[c.start():c.start(1)]) else 'public-source',source_signature=signature,source_signature_sha256=sha(signature),preceding_context_command_history=list(variables),status='pending-elaboration-and-simultaneous-witness'))
    return records

def main():
    p=argparse.ArgumentParser(); p.add_argument('--output',required=True); a=p.parse_args()
    root=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip()); map_path=root/'docs/module-map/evm-compiler.md'
    base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
    subprocess.run(['git','merge-base','--is-ancestor',base,'HEAD'],check=True,cwd=root)
    def frozen(relative):
        expected=subprocess.check_output(['git','show',base+':'+relative],cwd=root)
        actual=(root/relative).read_bytes()
        if actual!=expected: raise ValueError('frozen blob mismatch: '+relative)
    frozen('docs/module-map/evm-compiler.md')
    modules=re.findall(r'^\| `([^`]+\.lean)`',map_path.read_text(),re.M)
    if len(set(modules))!=len(modules): raise ValueError('duplicate module-map path')
    result=[]
    for module in modules:
        relative=module if module.startswith('Bridge/') else 'Solidity/'+module; frozen(relative); path=root/relative
        for r in scan(path):
            r.update(file=relative,module_map_area='evm-compiler',source_file_sha256=sha(path.read_text()),owner_status='pending-producer-reconciliation')
            result.append(r)
    # Independent masked-token count fails closed on any silently missed declaration.
    token_count=sum(len(re.findall(r'\btheorem\s',mask((root/(m if m.startswith('Bridge/') else 'Solidity/'+m)).read_text()))) for m in modules)
    if token_count!=len(result): raise ValueError(f'masked tokens {token_count} != records {len(result)}')
    keys=[(r['file'],r['line']) for r in result]
    if len(set(keys))!=len(keys): raise ValueError('duplicate declaration position')
    output=dict(schema=2,signature_parser="balanced-root-let-match-aware",base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4',module_map_sha256=sha(map_path.read_text()),modules=modules,module_count=len(modules),candidate_count=len(result),kernel_verified=False,statements=result)
    pathlib.Path(a.output).write_text(json.dumps(output,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:output[k] for k in ('module_count','candidate_count','kernel_verified')}))
if __name__=='__main__': main()
