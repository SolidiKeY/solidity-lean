"""Read Lean header imports, ignoring nested block and line comments."""
import re

def header_imports(text):
    clean=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':
            clean.append(' ');depth+=1;i+=2;continue
        if depth and text[i:i+2]=='-/':depth-=1;i+=2;continue
        if depth:
            if text[i]=='\n':clean.append('\n')
            i+=1;continue
        if text[i:i+2]=='--':
            end=text.find('\n',i);i=len(text) if end<0 else end;continue
        clean.append(text[i]);i+=1
    source=''.join(clean);pos=0;out=[]
    prelude=re.match(r'\s*prelude\b',source)
    if prelude:pos=prelude.end()
    while True:
        m=re.match(r'\s*(?:public\s+)?import[ \t]+([A-Za-z0-9_.]+(?:[ \t]+[A-Za-z0-9_.]+)*)',source[pos:])
        if not m:break
        out.extend(m.group(1).split());pos+=m.end()
    return out
