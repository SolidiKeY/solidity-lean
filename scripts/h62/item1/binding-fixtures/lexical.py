"""Mask Lean comments and string literals while preserving offsets and newlines.
This is a lexical filter, not a Lean parser or declaration-boundary oracle.
"""
import re
from functools import lru_cache
RAW = re.compile(r'r(#{0,})"')
CHAR = re.compile(r"'(?:\\.|[^\\'\r\n])'")


@lru_cache(maxsize=512)
def scan_source(source):
    result=list(source)
    unknown=[]
    def blank(start,end):
        for pos in range(start,end):
            if source[pos] not in '\r\n':result[pos]=' '
    i=0
    while i<len(source):
        start=i
        if source.startswith('--',i):
            end=source.find('\n',i)
            i=len(source) if end<0 else end
        elif source.startswith('/-',i):
            depth=1;i+=2
            while i<len(source) and depth:
                if source.startswith('/-',i):depth+=1;i+=2
                elif source.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            if depth:raise ValueError('unterminated block comment')
        else:
            raw=RAW.match(source,i) if source[i]=='r' and (i==0 or not (source[i-1].isalnum() or source[i-1]=='_')) else None
            if raw:
                close='"'+raw.group(1);end=source.find(close,raw.end())
                if end<0:raise ValueError('unterminated raw string')
                i=end+len(close)
            elif source[i]=="'" and (i==0 or not (source[i-1].isalnum() or source[i-1] in "_'")) and (char:=CHAR.match(source,i)):
                i=char.end()
            elif source[i]=='«':
                end=source.find('»',i+1)
                if end<0:raise ValueError('unterminated quoted identifier')
                unknown.append((source.count('\n',0,i)+1,source[i:end+1]))
                i=end+1
            elif source[i]=='"':
                i+=1
                while i<len(source):
                    if source[i]=='\\':
                        if i+1>=len(source):raise ValueError('unterminated string escape')
                        i+=2
                    elif source[i]=='"':i+=1;break
                    else:i+=1
                else:raise ValueError('unterminated string')
            else:i+=1;continue
        blank(start,i)
    return ''.join(result), tuple(unknown)


def code_only(source):
    return scan_source(source)[0]


def unknown_identifiers(source):
    return [{"line":line,"text":text,"status":"unknown quoted identifier"} for line,text in scan_source(source)[1]]
